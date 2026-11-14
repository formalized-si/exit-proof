#!/usr/bin/env python3
"""selftest.py <traces.jsonl or trace.json> ...: shows that each monitor of monitor.py can fire.

Takes traces on which the monitors report nothing, doctors one fact at a time (a balance in a
recorded state, the outcome of a receipt, a measured move) and checks that the expected monitor
reports it. This tests the monitors, not the contract. Exit status 0 iff every mutation that could
be applied was caught, and every kind was applied at least once.
"""
import collections, copy, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import monitor  # noqa: E402


def cov():
    return monitor.new_cov()


def kinds(t):
    return {v["kind"] for v in monitor.check_trace(t, cov())}


def bump(d, key, by):
    d[key] = str(int(d.get(key, "0")) + by)


def m_ledger_only(t):
    """one account's ledger balance grows in a recorded step state, the supply does not"""
    for s in t["steps"]:
        for tid, m in s["state"]["ledger"].items():
            a = next(iter(m))
            bump(m, a, 5)
            return "supply_mismatch"


def m_ledger_and_supply(t):
    """ledger balance and supply of a backed asset grow by more than the contract holds, in one step state"""
    backed = [a["ledger"] for a in t["world"]["assets"]]
    for s in t["steps"]:
        for tid in backed:
            if tid in s["state"]["ledger"]:
                held = int(s["state"]["held"].get(tid, "0"))
                a = next(iter(s["state"]["ledger"][tid]))
                bump(s["state"]["ledger"][tid], a, held + 1)
                bump(s["state"]["supply"], tid, held + 1)
                return "overcredit"


def m_private_ok(t):
    """a private callback called by a stranger is recorded as successful"""
    C = t["world"]["contract"]
    for s in t["steps"]:
        if s["recv"] == C and s["method"] in t["world"]["private"] and s["pred"] != C:
            s["ok"] = True
            return "private_ran"


def m_failed_moves(t):
    """a failed receipt is recorded with a balance change"""
    C = t["world"]["contract"]
    for s in t["steps"]:
        if not s["ok"] and s["recv"] == C:
            s["moves"] = [[C, t["world"]["ids"][0], "alice.near", "7"]]
            return "failed_changed"


def m_paused_ok(t):
    """a call of a paused entry point is recorded as successful"""
    C = t["world"]["contract"]
    prev = t["init"]["state"]
    for s in t["steps"]:
        k = monitor.PAUSE_KEY.get(s["method"])
        if s["recv"] == C and k and (k in prev["paused"] or "ALL" in prev["paused"]) and not s["ok"]:
            s["ok"] = True
            return "ran_while_paused"
        prev = s["state"]


def m_locked_ok(t):
    """a locked account's own withdrawal or transfer is recorded as successful"""
    C = t["world"]["contract"]
    prev = t["init"]["state"]
    for s in t["steps"]:
        if s["recv"] == C and s["method"] in monitor.OWNER_SPENDS and s["pred"] in prev["locked"] and not s["ok"]:
            s["ok"] = True
            return "locked_spent"
        prev = s["state"]


def m_refund_too_big(t):
    """the refund a withdrawal callback credits is recorded larger than what came back"""
    C = t["world"]["contract"]
    backed = [a["ledger"] for a in t["world"]["assets"]]
    for s in t["steps"]:
        if s["recv"] == C and s["method"] in ("ft_resolve_withdraw", "mt_resolve_withdraw") and s["ok"]:
            for mv in s["moves"]:
                if mv[0] == C and mv[2] is not None and mv[1] in backed and int(mv[3]) > 0:
                    mv[3] = str(int(mv[3]) + 3)
                    return "tx_overcredit"


def m_refund_missing(t):
    """the refund of a failed plain transfer is dropped from the record"""
    C = t["world"]["contract"]
    backed = [a["ledger"] for a in t["world"]["assets"]]
    for s in t["steps"]:
        if s["recv"] == C and s["method"] in ("ft_resolve_withdraw", "mt_resolve_withdraw") and s["ok"] \
                and not s["args"].get("is_call") and any(mv[1] in backed and int(mv[3]) > 0 for mv in s["moves"]):
            s["moves"] = []
            return "tx_stranded"


def m_idle_gap(t):
    """in a block with nothing pending the views show a smaller ledger and supply than before"""
    backed = [a["ledger"] for a in t["world"]["assets"]]
    for ob in t["obs"]:
        if ob["pending_ops"]:
            continue
        for tid in backed:
            m = ob["state"]["ledger"].get(tid)
            if m:
                a = next(iter(m))
                if int(m[a]) > 1:
                    bump(m, a, -1)
                    bump(ob["state"]["supply"], tid, -1)
                    return "quiescent_gap"


def m_taken(t):
    """a token receipt that is no settlement and not the contract's call lowers the contract's balance"""
    C = t["world"]["contract"]
    for s in t["steps"]:
        if s["recv"] == "token.near" and s["method"] == "ft_transfer" and s["pred"] != C and s["ok"]:
            s["moves"].append(["token.near", None, C, "-9"])
            return "holdings_taken"


def m_unknown_token(t):
    """the contract enumerates a ledger token id the trace does not track"""
    t["obs"][len(t["obs"]) // 2]["tokens"].append("nep141:unknown.near")
    return "unknown_ledger_token"


def m_own_callback(t):
    """a callback the contract scheduled for itself is recorded as failed"""
    C = t["world"]["contract"]
    for s in t["steps"]:
        if s["recv"] == C and s["pred"] == C and s["callback"] and s["ok"] and not s["moves"]:
            s["ok"] = False
            s["status"] = "Panic(\"doctored\")"
            return "own_callback_failed"


def m_unauthorized_ok(t):
    """a role-guarded method called by an account without a required role is recorded as successful"""
    C = t["world"]["contract"]
    prev = t["init"]["state"]
    for s in t["steps"]:
        need = monitor.ROLES.get(s["method"])
        if s["recv"] == C and need and not s["ok"]:
            held = {r for r, l in prev["acl"]["grantees"].items() if s["pred"] in l}
            if not held & set(need):
                s["ok"] = True
                return "unauthorized_ran"
        prev = s["state"]


def m_unauthorized_switch(t):
    """a failed pause or lock by an account without the role is recorded with the switch changed"""
    C = t["world"]["contract"]
    prev = t["init"]["state"]
    for s in t["steps"]:
        if s["recv"] == C and s["method"] in ("pa_pause_feature", "force_lock_account") and not s["ok"]:
            held = {r for r, l in prev["acl"]["grantees"].items() if s["pred"] in l}
            if not held & set(monitor.ROLES[s["method"]]):
                key = "paused" if s["method"] == "pa_pause_feature" else "locked"
                s["state"][key] = sorted(set(s["state"][key]) | {"doctored.near"})
                return "unauthorized_ran"
        prev = s["state"]


def m_unauthorized_grant(t):
    """a role grant by an account that is no admin is recorded as answered with true"""
    C = t["world"]["contract"]
    prev = t["init"]["state"]
    for s in t["steps"]:
        if s["recv"] == C and s["method"] in monitor.ACL_ADMIN and s["ok"] and isinstance(s["args"], dict):
            acl = prev["acl"]
            if s["pred"] not in acl["super_admins"] and s["pred"] not in acl["admins"].get(s["args"].get("role"), []):
                s["ret"] = {"kind": "value", "json": True}
                return "unauthorized_ran"
        prev = s["state"]


def m_auth_off_ok(t):
    """a call by an account whose auth-by-predecessor flag is off is recorded as successful"""
    C = t["world"]["contract"]
    prev = t["init"]["state"]
    for s in t["steps"]:
        if s["recv"] == C and s["method"] in monitor.AUTH_PRED and s["pred"] in prev["auth_off"] and not s["ok"]:
            s["ok"] = True
            return "auth_off_ran"
        prev = s["state"]


MUTATIONS = [m_unauthorized_ok, m_unauthorized_switch, m_unauthorized_grant, m_auth_off_ok, m_ledger_only, m_ledger_and_supply, m_private_ok, m_failed_moves, m_paused_ok, m_locked_ok, m_refund_too_big,
             m_refund_missing, m_idle_gap, m_taken, m_unknown_token, m_own_callback]


def main():
    traces = [json.loads(line) for p in sys.argv[1:] for line in open(p) if line.strip()]
    traces = [t for t in traces if "sim_panic" not in t]
    clean = [t for t in traces if not kinds(t)]
    print(f"{len(clean)} of {len(traces)} traces are clean before doctoring")
    ok = True
    for m in MUTATIONS:
        applied = caught = 0
        want = None
        for t in clean:
            d = copy.deepcopy(t)
            want_here = m(d)
            if want_here is None:
                continue
            want = want_here
            applied += 1
            caught += want in kinds(d)
        verdict = "caught" if applied and caught == applied else ("NOT APPLICABLE to these traces" if not applied else "MISSED")
        ok &= bool(applied) and caught == applied
        print(f"{verdict:8} {caught}/{applied}  {want or '?':22} {m.__doc__}")
    for k in ("unauthorized_ran", "auth_off_ran"):
        n = sum(1 for t in traces for v in monitor.check_trace(t, cov()) if v["kind"] == k)
        print(f"{k} on the undoctored traces: {n}")
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
