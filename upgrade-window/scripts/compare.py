#!/usr/bin/env python3
"""Diffs near-contract-sim traces of the example vault against the Lean model's replay.

usage: compare.py SIM.jsonl MODEL.jsonl [--json OUT]

Per receipt on the vault: success/failure, the panic text, the return value, the receipts it
created (the deploy batch: actions, methods, arguments, gas, deposit; the withdrawal transfer).
Per block: the plugin's five storage slots, the staged code, the same through the plugin's views,
the account's code hash and `version()`, the role grants, the vault balances.

Model-free monitors, computed from the wasm's own data only:
  safe_until    safeUntil (README, W3), computed from the storage slots after every block, never
                decreases; no up_deploy_code call succeeds before the largest value seen so far
  deploy_origin a successful up_deploy_code runs at or after the staging timestamp read before it,
                with the hash argument the view up_staged_code_hash returned before it; if its
                batch succeeds, the account's code hash becomes that hash

Exit status 0 iff there is no divergence and no monitor violation.
"""
import json
import sys

U64_MAX = 2**64 - 1
VERSION = {"v1": 1, "v2": 2, "v3": 3}
STATUS_FIELDS = ("staging_duration", "staging_timestamp", "new_staging_duration", "new_staging_duration_timestamp")


def sat(a, b):
    return min(a + b, U64_MAX)


# --unchecked: the wasm was built without overflow checks; the monitors then use `safeUntilU`
# (Unchecked.lean) with B = 2^63: a duration above B counts as 0.
UNCHECKED = False
B = 2**63


def eff(d):
    return 0 if (UNCHECKED and d > B) else d


def safe_until(status, now):
    """Model.lean `safeUntil` (Unchecked.lean `safeUntilU` with --unchecked), from the four
    delay-status fields (decimal strings or None)."""
    g = lambda k: None if status.get(k) is None else int(status[k])
    a = sat(now, eff(g("staging_duration") or 0))
    b = a if g("staging_timestamp") is None else min(a, g("staging_timestamp"))
    nd, ndt = g("new_staging_duration"), g("new_staging_duration_timestamp")
    if nd is not None and ndt is not None:
        return min(b, sat(max(now, ndt), eff(nd)))
    return b


def attribute(kind, method, field, sim_status, model_err):
    """Which statement the diverging behaviour belongs to."""
    text = f"{sim_status or ''} {model_err or ''}"
    if kind == "obs":
        if field in ("staging_timestamp",):
            return "W1"
        if field in ("staged", "staged_hash", "code", "code_hash", "version"):
            return "W2"
        if field in ("staging_duration", "new_staging_duration", "new_staging_duration_timestamp"):
            return "W3"
        if field in ("roles", "super_admins"):
            return "ACL"
        return "vault"
    if method == "up_deploy_code":
        if "wrong hash" in text or "No staged code" in text:
            return "W2"
        if "permissions" in text:
            return "ACL"
        return "W1"
    if method == "up_stage_code":
        return "ACL" if "permissions" in text else "W1"
    if method in ("up_init_staging_duration", "up_stage_update_staging_duration", "up_apply_update_staging_duration"):
        return "ACL" if "permissions" in text else "W3"
    if method and method.startswith("acl_"):
        return "ACL"
    if kind == "batch":
        return "W2"
    return "vault"


def compare_step(s, m):
    """Returns (kind, detail) for the first difference in one receipt, or None."""
    if s["k"] == "batch":
        if m.get("unexpected_batch"):
            return ("batch", "a deploy batch ran that no modelled up_deploy_code created")
        return None
    if m.get("ok") != s["ok"]:
        return ("outcome", f"wasm {'ok' if s['ok'] else s['status']} / model {'ok' if m.get('ok') else m.get('err')}")
    if not s["ok"]:
        if m.get("err") and m["err"] not in s["status"]:
            return ("error text", f"wasm {s['status']} / model {m['err']}")
        return None
    mr = m.get("ret") or {}
    if mr.get("kind") != "any" and mr != s["ret"]:
        return ("return value", f"wasm {json.dumps(s['ret'])} / model {json.dumps(mr)}")
    eff, me = s["eff"], m.get("eff")
    if me is None:
        if eff:
            return ("receipts", f"wasm created {json.dumps(eff)} / model none")
        return None
    if len(eff) != 1:
        return ("receipts", f"wasm created {len(eff)} receipts / model {json.dumps(me)}")
    c = eff[0]
    if "transfer" in me:
        want = {"receiver": me["transfer"][0], "actions": ["Transfer"], "deposit": me["transfer"][1]}
        got = {k: c[k] for k in want}
    else:
        n = len(me["methods"])
        args = ([me["fc_args"]] if n == 2 else []) + [""]
        want = {"receiver": s["self_id"], "actions": ["DeployContract"] + ["FunctionCall"] * n, "methods": me["methods"],
                "args": args, "deposit": me["fc_amount"], "gas": me["gas"]}
        got = {k: c[k] for k in want}
    if got != want:
        return ("receipts", f"wasm {json.dumps(got)} / model {json.dumps(want)}")
    return None


def compare_obs(o, m, self_id):
    """Returns (field, detail) for the first difference in one observation, or None."""
    st = o["storage"]
    for f in STATUS_FIELDS:
        if st["status"][f] != m["status"][f]:
            return (f, f"storage {st['status'][f]} / model {m['status'][f]}")
    if st["staged"] != m["staged"]:
        return ("staged", f"storage {st['staged']} / model {m['staged']}")
    if o["code"] != m["code"] or o["code_hash"] != m["code_hash"]:
        return ("code", f"account {o['code']} {o['code_hash']} / model {m['code']} {m['code_hash']}")
    v = o["views"]
    if m["code"] == "stub":
        if v["status"] is not None or v["staged_hash"]["ok"] or v["roles"] is not None:
            return ("version", "views answer although the model says the code is the stub")
        return None
    if v["status"] != m["status"]:
        return ("staging_timestamp" if (v["status"] or {}).get("staging_timestamp") != m["status"]["staging_timestamp"]
                else "staging_duration", f"view {json.dumps(v['status'])} / model {json.dumps(m['status'])}")
    if v["staged_hash"] != {"ok": True, "hash": m["staged_hash"]}:
        return ("staged_hash", f"view {json.dumps(v['staged_hash'])} / model {m['staged_hash']}")
    if v["version"] != VERSION.get(m["code"]):
        return ("version", f"view {v['version']} / model code {m['code']}")
    if v["roles"] != m["roles"]:
        return ("roles", f"view {v['roles']} / model {m['roles']}")
    if v["super_admins"] != [self_id]:
        return ("super_admins", f"view {v['super_admins']}")
    if v["bal"] != m["bal"]:
        return ("bal", f"view {json.dumps(v['bal'])} / model {json.dumps(m['bal'])}")
    return None


def monitors(t, cov, viol):
    """Model-free checks on one trace; counts coverage."""
    obs = t["obs"]
    by_h = {}
    for o in obs:
        by_h[o["h"]] = o
    hs = sorted(by_h)
    # safeUntil after every block, and its running maximum
    run_max, prev = {}, None
    cur = 0
    for h in hs:
        o = by_h[h]
        su = safe_until(o["storage"]["status"], int(o["t"]))
        if prev is not None and su < prev:
            viol["safe_until_decreased"] += 1
            viol.setdefault("examples", []).append({"trace": t["id"], "h": h, "from": prev, "to": su})
        prev = su
        cur = max(cur, su)
        run_max[h] = cur

    def before(h):
        """Last observation strictly before block h."""
        c = [x for x in hs if x < h]
        return by_h[c[-1]] if c else None

    staged_in_block = set()
    batch_result = {s["rid"]: s for s in t["steps"] if s["k"] == "batch"}
    batches_in_block = Counter()
    for s in t["steps"]:
        if s["k"] == "batch":
            batches_in_block[s["h"]] += 1
    for i, s in enumerate(t["steps"]):
        if s["k"] == "batch":
            cov["batches"] += 1
            cov["batch_ok" if s["ok"] else "batch_rolled_back"] += 1
            continue
        meth, ok, status, now = s["method"], s["ok"], s["status"], int(s["t"])
        ob = before(s["h"])
        if meth == "up_stage_code" and ok:
            staged_in_block.add(s["h"])
            cov["stage_ok"] += 1
            if not s.get("code"):
                cov["stage_removed"] += 1
        if meth == "up_deploy_code":
            ts = ob and ob["storage"]["status"]["staging_timestamp"]
            clean = s["h"] not in staged_in_block
            if ok:
                cov["deploy_ok"] += 1
                c = [x for x in hs if x < s["h"]]
                if c and run_max[c[-1]] > now:
                    viol["deploy_before_safe_until"] += 1
                    viol.setdefault("examples", []).append({"trace": t["id"], "h": s["h"], "now": now, "safe_until": run_max[c[-1]]})
                if clean and ob:
                    if ts is None or int(ts) > now:
                        viol["deploy_before_staging_timestamp"] += 1
                        viol.setdefault("examples", []).append({"trace": t["id"], "h": s["h"], "now": now, "staging_timestamp": ts})
                    elif int(ts) == now:
                        cov["deploy_ok_exactly_at_staging_timestamp"] += 1
                    want = (ob["views"]["staged_hash"] or {}).get("hash")
                    try:
                        arg = json.loads(s["args"]).get("hash")
                    except Exception:
                        arg = None
                    if want is not None and arg != want:
                        viol["deploy_with_other_hash"] += 1
                        viol.setdefault("examples", []).append({"trace": t["id"], "h": s["h"], "arg": arg, "view": want})
                    b = batch_result.get(s.get("deploy_rid"))
                    if b and b["ok"] and want is not None and batches_in_block[b["h"]] == 1:
                        after = by_h.get(b["h"])
                        if after and after["code_hash"] != want:
                            viol["deployed_code_is_not_staged_code"] += 1
                            viol.setdefault("examples", []).append({"trace": t["id"], "h": b["h"], "account": after["code_hash"], "staged": want})
                        elif after:
                            cov["code_replaced"] += 1
                            if after["code"] == "stub":
                                cov["code_replaced_by_stub"] += 1
            elif "too early" in status:
                cov["deploy_too_early"] += 1
                if clean and ts is not None and int(ts) == now + 1:
                    cov["deploy_rejected_1ns_before_staging_timestamp"] += 1
            elif "wrong hash" in status:
                cov["deploy_wrong_hash"] += 1
            elif "timestamp isn't set" in status:
                cov["deploy_nothing_staged"] += 1
        if meth == "up_apply_update_staging_duration":
            ndt = ob and ob["storage"]["status"]["new_staging_duration_timestamp"]
            if ok:
                cov["apply_ok"] += 1
                if ndt is not None and int(ndt) == now:
                    cov["apply_ok_exactly_at_timestamp"] += 1
            elif "too early" in status:
                cov["apply_too_early"] += 1
                if ndt is not None and int(ndt) == now + 1:
                    cov["apply_rejected_1ns_before_timestamp"] += 1
            elif "No staged update" in status:
                cov["apply_nothing_staged"] += 1
        if meth == "up_stage_update_staging_duration":
            if ok:
                cov["stage_duration_ok"] += 1
            elif "overflow" in status:
                cov["stage_duration_overflow_panic"] += 1
            if ok and ob:
                d0 = ob["storage"]["status"]["staging_duration"]
                if d0 is not None and now + int(d0) > U64_MAX:
                    cov["stage_duration_wrapped"] += 1
            elif "isn't initialized" in status:
                cov["stage_duration_not_initialized"] += 1
        if meth == "up_init_staging_duration":
            if ok:
                cov["init_duration_ok"] += 1
            elif "already initialized" in status:
                cov["init_duration_already_set"] += 1
        if meth and meth.startswith("up_") and "Insufficient permissions" in status:
            cov["refused_by_access_control"] += 1
        if ok and meth in ("up_stage_code", "up_deploy_code", "up_init_staging_duration",
                           "up_stage_update_staging_duration", "up_apply_update_staging_duration"):
            cov["protected_calls_ok"] += 1
            if s.get("logs"):
                cov["protected_calls_ok_that_logged_something"] += 1
        if "Failed to deserialize" in status:
            cov["bad_arguments"] += 1
        if "doesn't accept deposit" in status:
            cov["deposit_on_non_payable"] += 1
        if meth == "withdraw" and ok:
            cov["withdraw_ok"] += 1
        if meth == "deposit" and ok:
            cov["deposit_ok"] += 1
        if meth in ("acl_grant_role", "acl_revoke_role", "acl_renounce_role") and ok:
            cov["role_calls_ok"] += 1
    for o in obs:
        if o["storage"]["status"]["staging_timestamp"] == str(U64_MAX):
            cov["staging_timestamp_saturated_blocks"] += 1
            break
    if t["init_dur"] is None:
        cov["traces_without_initial_duration"] += 1
    cov["protected_calls_ok_that_logged_something"] += 0


class Counter(dict):
    def __missing__(self, k):
        return 0


def main():
    global UNCHECKED
    UNCHECKED = "--unchecked" in sys.argv
    sim_path, model_path = sys.argv[1], sys.argv[2]
    out = sys.argv[sys.argv.index("--json") + 1] if "--json" in sys.argv else None
    models = {}
    for line in open(model_path):
        if line.strip():
            m = json.loads(line)
            models[m.get("id")] = m
    tot = Counter()
    cov, viol = Counter(), Counter()
    divs, by_prop = [], Counter()
    for line in open(sim_path):
        if not line.strip():
            continue
        t = json.loads(line)
        m = models.get(t["id"])
        tot["traces"] += 1
        if not t["settled"]:
            tot["unsettled_traces"] += 1
        if m is None or "error" in m:
            divs.append({"trace": t["id"], "kind": "model", "detail": "no model output", "property": "-"})
            continue
        first = None
        if len(m["steps"]) != len(t["steps"]) or len(m["obs"]) != len(t["obs"]):
            first = {"trace": t["id"], "kind": "model", "detail": "step/observation count differs", "property": "-"}
        # walk receipts and observations in block order: the first difference in time wins
        events = [(s["h"], 0, i) for i, s in enumerate(t["steps"])] + [(o["h"], 1, i) for i, o in enumerate(t["obs"])]
        events.sort()
        for h, kind, i in events:
            if first:
                break
            if kind == 0:
                s = dict(t["steps"][i], self_id=t["self"])
                tot["receipts"] += 1
                tot["calls" if s["k"] == "call" else "deploy_batches"] += 1
                d = compare_step(s, m["steps"][i])
                if d:
                    meth = s.get("method")
                    first = {"trace": t["id"], "h": h, "kind": "batch" if s["k"] == "batch" else d[0], "method": meth,
                             "pred": s.get("pred"), "args": (s.get("args") or s.get("code") or "")[:200], "detail": d[1][:600],
                             "property": attribute("batch" if s["k"] == "batch" else "step", meth, None, s.get("status"), m["steps"][i].get("err"))}
            else:
                tot["blocks"] += 1
                tot["state_comparisons"] += 1
                d = compare_obs(t["obs"][i], m["obs"][i], t["self"])
                if d:
                    first = {"trace": t["id"], "h": h, "kind": "state", "field": d[0], "detail": d[1][:600],
                             "property": attribute("obs", None, d[0], None, None)}
        if first:
            divs.append(first)
            by_prop[first["property"]] += 1
        monitors(t, cov, viol)
    examples = viol.pop("examples", [])
    n_viol = sum(viol.values())
    res = {
        "ok": not divs and n_viol == 0,
        "model": "unchecked build (Up.callU), monitors with safeUntilU, B = 2^63" if UNCHECKED else "checked build (Up.call)",
        "traces": tot["traces"], "unsettled_traces": tot["unsettled_traces"],
        "receipts": tot["receipts"], "calls": tot["calls"], "deploy_batches": tot["deploy_batches"],
        "blocks": tot["blocks"],
        "diverging_traces": len(divs),
        "diverging_traces_by_first_property": dict(by_prop),
        "first_divergence": divs[0] if divs else None,
        "more_divergences": divs[1:6],
        "monitor_violations": dict(viol), "monitor_violation_examples": examples[:5],
        "coverage": dict(sorted(cov.items())),
    }
    text = json.dumps(res, indent=1)
    if out:
        open(out, "w").write(text + "\n")
    print(text)
    sys.exit(0 if res["ok"] else 1)


if __name__ == "__main__":
    main()
