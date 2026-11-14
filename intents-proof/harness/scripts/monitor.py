#!/usr/bin/env python3
"""Model-free monitors over the traces of intents-gen (see FORMAT.md).

  monitor.py [--out summary.json] [--violations v.jsonl] [--sample-dir DIR --sample N]
             [--keep-violating N] traces.jsonl ... (or stdin)

The monitors use only what the trace records: the receipts, the balance changes the simulator
measured with views around every receipt, and the views after every block. They contain no model
of the contract. Notation, per backed asset `a` (a ledger token id whose tokens another contract
holds for the contract):

  L(a)  sum over all accounts of the ledger balance (mt_balance_of)
  S(a)  mt_supply
  H(a)  what the token contract says the contract holds (ft_balance_of / mt_balance_of of it)
  U(a)  tokens that reached the contract with no deposit notification: every change of H made by
        a token receipt that is neither an `*_transfer_call` naming the contract as receiver, nor
        the token's own `*_resolve_transfer`, nor a call made by the contract itself
  G(a)  what completed transactions left in the contract without a ledger owner (each one is
        itself reported, kind tx_stranded)

Checks:
  overcredit           after every receipt:  L(a) <= H(a) - U(a)
  supply_mismatch      after every receipt and in every block's views:  L(t) == S(t), all ledger ids
  tx_overcredit /      for every finished transaction:  dL(a) == dH(a) - dU(a)  (its own receipts'
  tx_stranded          measured changes); ">" is tx_overcredit, "<" is tx_stranded
  withdraw_inexact     for a finished withdrawal with no nested calls: the owner's ledger balance
                       fell by exactly what left the contract's holdings
  quiescent_gap        in every block's views with no receipt pending:  L(a) == H(a) - U(a) - G(a)
  own_callback_failed  a callback the contract scheduled for itself must not fail
  private_ran          a private callback called by another account must fail
  failed_changed       a failed receipt must change no watched balance
  ran_while_paused     a paused entry point must fail
  locked_spent         a locked account's own withdrawal or transfer must fail
  unauthorized_ran     a role-guarded method called by an account that holds none of the required
                       roles must fail and change nothing; a near-plugins `acl_*` method called by
                       an account that is neither a super-admin nor (where that suffices) an admin
                       of the role must return null, emit no event and leave the role table as it
                       was. Roles are read from the role table before the receipt (`state.acl`),
                       the required roles from ROLES below.
  auth_off_ran         a method that authenticates its predecessor must fail for an account whose
                       auth-by-predecessor flag is off
  holdings_taken       U never decreases (tokens leave the contract only by its own calls or a
                       token's settlement)
  unknown_ledger_token the contract enumerates no ledger token id the trace does not track
Harness integrity (not properties of the contract): derive_mismatch, view_errors, derive_errors,
unsettled, sim_panic.
"""
import argparse, collections, json, os, sys

PAUSE_KEY = {
    "ft_on_transfer": "ft_on_transfer", "ft_withdraw": "ft_withdraw", "mt_on_transfer": "mt_on_transfer",
    "mt_withdraw": "mt_withdraw", "mt_transfer": "mt_transfer", "mt_batch_transfer": "mt_transfer",
    "mt_transfer_call": "mt_transfer", "mt_batch_transfer_call": "mt_transfer", "execute_intents": "intents",
}
# The role table of the contract: method -> the roles one of which the predecessor must hold. From the source
# at commit 16d04f6ec4401263f8914638710260da50bb46b0 (contracts/defuse/src/contract/...): every
# `#[access_control_any(roles(...))]`, and `#[pausable(pause_roles(...), unpause_roles(...))]` of the contract struct.
# All of these methods are exported by the deployed wasm; `force_add_public_keys` / `force_remove_public_keys`
# (feature `far`) are not, and are left out.
_W = ["DAO", "UnrestrictedWithdrawer"]
_LOCK = ["DAO", "UnrestrictedAccountLocker", "UnrestrictedAccountManager"]
_UNLOCK = ["DAO", "UnrestrictedAccountUnlocker", "UnrestrictedAccountManager"]
ROLES = {
    "ft_force_withdraw": _W,                                            # tokens/nep141/withdraw.rs:199
    "nft_force_withdraw": _W,                                           # tokens/nep171/withdraw.rs:199
    "mt_force_withdraw": _W,                                            # tokens/nep245/withdraw.rs:267
    "mt_force_transfer": _W, "mt_force_batch_transfer": _W,             # tokens/nep245/force.rs:16, 37
    "mt_force_transfer_call": _W, "mt_force_batch_transfer_call": _W,   # tokens/nep245/force.rs:62, 85
    "force_lock_account": _LOCK,                                        # accounts/force.rs:16
    "force_unlock_account": _UNLOCK,                                    # accounts/force.rs:35
    "force_disable_auth_by_predecessor_ids": _LOCK,                     # accounts/force.rs:54
    "force_enable_auth_by_predecessor_ids": _UNLOCK,                    # accounts/force.rs:69
    "pa_pause_feature": ["DAO", "PauseManager"],                        # mod.rs:75-78 (pause_roles)
    "pa_unpause_feature": ["DAO", "UnpauseManager"],                    # mod.rs:75-78 (unpause_roles)
    "upgrade": ["DAO", "Upgrader"],                                     # upgrade.rs:11
    "admin_call": ["DAO"],                                              # admin_call.rs:10
    "add_full_access_key": ["DAO"], "delete_key": ["DAO"],              # admin.rs:9, 16
    "set_fee": ["DAO", "FeesManager"],                                  # fees.rs:18
    "set_fee_collector": ["DAO", "FeesManager"],                        # fees.rs:36
    "add_relayer_key": ["DAO", "RelayerKeysManager"],                   # intents/relayer.rs:16
    "delete_relayer_key": ["DAO", "RelayerKeysManager"],                # intents/relayer.rs:35
    "cleanup_nonces": ["DAO", "GarbageCollector"],                      # garbage_collector.rs:11
    "update_current_salt": ["DAO", "SaltManager"],                      # salts.rs:13
    "invalidate_salts": ["DAO", "SaltManager"],                         # salts.rs:30
}
ALL_ROLES = ["DAO", "FeesManager", "RelayerKeysManager", "UnrestrictedWithdrawer", "PauseManager", "Upgrader", "UnpauseManager",
             "UnrestrictedAccountLocker", "UnrestrictedAccountUnlocker", "SaltManager", "GarbageCollector",
             "UnrestrictedAccountManager"]                                  # contract/mod.rs:51-71
# near-plugins 0.5.3 `AccessControllable`: the methods that change the role table. A caller without the permission
# gets `null`; the receipt itself succeeds.
ACL_SUPER = {"acl_add_super_admin", "acl_revoke_super_admin", "acl_transfer_super_admin"}   # a super-admin
ACL_ADMIN = {"acl_add_admin", "acl_revoke_admin", "acl_grant_role", "acl_revoke_role"}      # or an admin of `role`
# Methods that take the predecessor as the acting account (`ensure_auth_predecessor_id`).
AUTH_PRED = {"ft_withdraw", "nft_withdraw", "mt_withdraw", "mt_transfer", "mt_batch_transfer", "mt_transfer_call",
             "mt_batch_transfer_call", "add_public_key", "remove_public_key", "disable_auth_by_predecessor_id"}
OWNER_SPENDS = {"ft_withdraw", "mt_withdraw", "mt_transfer", "mt_batch_transfer", "mt_transfer_call", "mt_batch_transfer_call"}
WITHDRAW_ENTRY = {"ft_withdraw", "ft_force_withdraw", "mt_withdraw", "mt_force_withdraw"}
ANNOUNCE = {"ft_transfer_call", "mt_transfer_call", "mt_batch_transfer_call"}
SETTLE = {"ft_resolve_transfer", "mt_resolve_transfer"}


def sums(state, tid):
    led = state["ledger"].get(tid, {})
    return sum(int(v) for v in led.values()), int(state["supply"].get(tid, "0")), int(state["held"].get(tid, "0"))


def check_trace(t, cov):
    """Returns the list of violations of one trace; updates the coverage counters."""
    out = []
    tid_ = t["id"]

    def bad(kind, **kw):
        out.append({"trace": tid_, "kind": kind, **kw})

    if "sim_panic" in t:
        bad("sim_panic", detail=t["sim_panic"][:400])
        return out
    w = t["world"]
    C = w["contract"]
    assets = {(a["contract"], a["inner"]): a["ledger"] for a in w["assets"]}
    backed = [a["ledger"] for a in w["assets"]]
    ids = w["ids"]
    private = set(w["private"])
    ops = t["ops"]
    forced_op = {o["i"]: bool(o["faults"]) for o in ops}
    if not t["settled"]:
        bad("unsettled")
    for e in t["derive_errors"]:
        bad("derive_errors", detail=e)

    U = collections.Counter()
    U_at = {}                       # block height -> copy of U after the block's last receipt
    txL = collections.defaultdict(collections.Counter)      # tx -> ledger id -> sum of ledger changes
    txH = collections.defaultdict(collections.Counter)
    txU = collections.defaultdict(collections.Counter)
    txLo = collections.defaultdict(collections.Counter)     # tx -> (ledger id, account) -> change
    tx_steps = collections.defaultdict(list)
    prev = t["init"]["state"]
    seen_over = set()
    for s in t["steps"]:
        tx = s["tx"]
        tx_steps[tx].append(s)
        cov["calls"][f'{s["recv"]}::{s["method"]}' if s["method"] else f'{s["recv"]}::<{"+".join(s["actions"])}>'][0 if s["ok"] else 1] += 1
        for token, token_id, holder, delta in s["moves"]:
            d = int(delta)
            if token == C and holder is not None:
                txL[tx][token_id] += d
                txLo[tx][(token_id, holder)] += d
            elif holder == C and (token, token_id) in assets:
                a = assets[(token, token_id)]
                txH[tx][a] += d
                m = s["method"]
                if m in ANNOUNCE and isinstance(s["args"], dict) and s["args"].get("receiver_id") == C:
                    pass
                elif m in SETTLE and s["pred"] == s["recv"]:
                    pass
                elif s["pred"] == C:
                    pass
                else:
                    U[a] += d
                    txU[tx][a] += d
                    cov["unnotified_inflows"] += 1
                    if d < 0:
                        bad("holdings_taken", asset=a, step=s["i"], h=s["h"], delta=str(d), by=f'{s["pred"]} -> {s["recv"]}::{s["method"]}')
        if not s["ok"] and s["moves"]:
            bad("failed_changed", step=s["i"], h=s["h"], call=f'{s["recv"]}::{s["method"]}', moves=s["moves"])
        if s["recv"] == C and s["method"]:
            m = s["method"]
            if m in private and s["pred"] != C:
                cov["private_attempts"]["direct" if not s["callback"] else "as_callback"] += 1
                if s["ok"] or s["moves"] or s["events"]:
                    bad("private_ran", step=s["i"], h=s["h"], method=m, pred=s["pred"], ok=s["ok"])
            if s["pred"] == C and s["callback"] and not s["ok"]:
                bad("own_callback_failed", step=s["i"], h=s["h"], method=m, status=s["status"][:160], op=s["op"],
                    forced=forced_op.get(s["op"], False), probe=ops[s["op"]].get("probe") if s["op"] is not None else None,
                    result_it_read=["failed" if not r.get("ok") else "ok" for r in s["results"]])
            key = PAUSE_KEY.get(m)
            if key and (key in prev["paused"] or "ALL" in prev["paused"]):
                cov["calls_while_paused"] += 1
                if s["ok"]:
                    bad("ran_while_paused", step=s["i"], h=s["h"], method=m, paused=prev["paused"])
            if m in OWNER_SPENDS and s["pred"] in prev["locked"]:
                cov["spends_by_locked"] += 1
                if s["ok"]:
                    bad("locked_spent", step=s["i"], h=s["h"], method=m, account=s["pred"])
            if m in AUTH_PRED and s["pred"] in prev.get("auth_off", ()):
                cov["calls_with_auth_off"] += 1
                if s["ok"] or s["moves"]:
                    bad("auth_off_ran", step=s["i"], h=s["h"], method=m, account=s["pred"])
            acl = prev.get("acl")
            if acl is not None and (m in ROLES or m in ACL_SUPER or m in ACL_ADMIN):
                who = s["pred"]
                held = {r for r, l in acl["grantees"].items() if who in l}
                admin_of = {r for r, l in acl["admins"].items() if who in l}
                switches = lambda st: (st["paused"], st["locked"], st.get("auth_off"), st.get("acl"))
                if m in ROLES:
                    need = set(ROLES[m])
                    cls = ("holds a required role" if held & need else "holds other roles only" if held
                           else "admin of a required role, holds none" if admin_of & need
                           else "super-admin, holds no role" if who in acl["super_admins"] else "holds no role")
                    cov["guarded"][m][cls][0 if s["ok"] else 1] += 1
                    for role in (held or {"no role"}):
                        cov["guarded_by_role"][m][role][0 if s["ok"] else 1] += 1
                    if not held & need:
                        cov["unauthorized_attempts"] += 1
                        cov["unauthorized_rejected_by_the_role_check"] += "Insufficient permissions" in s["status"]
                        if s["ok"] or s["moves"] or switches(s["state"]) != switches(prev):
                            bad("unauthorized_ran", step=s["i"], h=s["h"], method=m, pred=who, required=sorted(need),
                                held=sorted(held), ok=s["ok"])
                else:
                    role = s["args"].get("role") if isinstance(s["args"], dict) else None
                    may = who in acl["super_admins"] or (m in ACL_ADMIN and role in admin_of)
                    cls = "may change the role table" if may else "may not"
                    cov["guarded"][m][cls][0 if s["ok"] else 1] += 1
                    if not may:
                        cov["unauthorized_attempts"] += 1
                        answered = s["ok"] and s["ret"] != {"kind": "value", "json": None}
                        emitted = s["ok"] and any(e.get("standard") == "AccessControllable" for e in s["events"])
                        if answered or emitted or s["moves"] or switches(s["state"]) != switches(prev):
                            bad("unauthorized_ran", step=s["i"], h=s["h"], method=m, pred=who, role=role,
                                held=sorted(held), admin_of=sorted(admin_of), ok=s["ok"], ret=s["ret"])
            if m == "ft_resolve_withdraw" and s["pred"] == C and s["results"] and isinstance(s["args"], dict):
                r0 = s["results"][0]
                n = len(r0.get("hex", "")) // 2
                if s["args"].get("is_call"):
                    k = ("failed" if not r0.get("ok") else "up to 42 bytes" if n <= 42 else f"{n} bytes" if n <= 46
                         else "47 bytes or more")
                    cov["token_replies"]["ft_transfer_call: " + k] += 1
                    v = r0.get("json")
                    if r0.get("ok") and n <= 44 and isinstance(v, str) and v.lstrip("+").isdigit() \
                            and int(v) > int(s["args"].get("amount", "0")):
                        cov["token_replies"]["ft_transfer_call: reports more than the amount"] += 1
                else:
                    cov["token_replies"]["ft_transfer: " + ("failed" if not r0.get("ok") else "succeeded with no value" if n == 0
                                                             else "succeeded with a value")] += 1
        st = s["state"]
        if s["recv"] == C and any(abs(int(mv[3])) >= 2 ** 127 for mv in s["moves"] if mv[0] == C):
            cov["receipts_moving_2^127_or_more"] += 1
        for tid in ids:
            L, S, H = sums(st, tid)
            if S == 2 ** 128 - 1 and int(prev["supply"].get(tid, "0")) != S:
                cov["times_a_supply_reached_u128_max"] += 1
            if L != S:
                bad("supply_mismatch", where="step", step=s["i"], h=s["h"], token=tid, ledger_sum=str(L), supply=str(S))
            cov["backing_checks"] += tid in backed
            if tid in backed and L > H - U[tid] and tid not in seen_over:
                seen_over.add(tid)
                bad("overcredit", asset=tid, step=s["i"], h=s["h"], ledger_sum=str(L), held=str(H), unnotified=str(U[tid]),
                    excess=str(L - (H - U[tid])), after=f'{s["pred"]} -> {s["recv"]}::{s["method"]}', op=s["op"])
        U_at[s["h"]] = dict(U)
        prev = st

    # finished transactions
    last_pending = set(t["obs"][-1]["pending_ops"]) if t["obs"] else set()
    G_tx = []                        # (last block, asset, stranded amount)
    for tx, steps in tx_steps.items():
        op = steps[0]["op"]
        if op in last_pending:
            continue
        o = ops[op] if op is not None else None
        forced = bool(o and o["faults"])
        for a in backed:
            dL, dH, dU = txL[tx][a], txH[tx][a], txU[tx][a]
            if dL == dH - dU:
                continue
            gap = (dH - dU) - dL
            failed_calls = [f'{x["recv"]}::{m}' for x in steps if x["pred"] == C and x["recv"] != C and not x["ok"]
                            for m in (x.get("methods") or [x["method"]])]
            cause = "other"
            if any(c.endswith("_call") for c in failed_calls):
                cause = "the contract's *_transfer_call to the token failed; the debit was kept"
            elif any(c.endswith("::near_withdraw") for c in failed_calls):
                cause = "the contract's near_withdraw on wNEAR failed; the wNEAR debit was kept"
            elif any(x["recv"] != C and x["method"] in SETTLE and not x["ok"] for x in steps):
                cause = "the token's own *_resolve_transfer failed"
            bad("tx_stranded" if gap > 0 else "tx_overcredit", asset=a, op=op, h=steps[-1]["h"], ledger_change=str(dL),
                holdings_change=str(dH), unnotified=str(dU), gap=str(gap), forced=forced, cause=cause,
                kind_of_op=o["kind"] if o else None)
            G_tx.append((steps[-1]["h"], a, gap))
        # withdrawals with no nested calls
        root = next((x for x in steps if x["recv"] == C and x["method"] in WITHDRAW_ENTRY), None)
        if root is None or not root["ok"]:
            continue
        own = [x for x in steps if x["recv"] == C]
        nested = [x for x in own if x["method"] not in WITHDRAW_ENTRY and x["method"] not in ("ft_resolve_withdraw", "mt_resolve_withdraw", "do_ft_withdraw", "do_mt_withdraw")]
        a_ = root["args"]
        owner = a_.get("owner_id", root["pred"]) if "force" in root["method"] else root["pred"]
        if root["method"].startswith("ft_"):
            wanted = {"nep141:" + a_["token"]: int(a_["amount"])}
        else:
            wanted = collections.Counter()
            for i_, x in zip(a_["token_ids"], a_["amounts"]):
                wanted[f'nep245:{a_["token"]}:{i_}'] += int(x)
        is_call = a_.get("msg") is not None
        tok = [x for x in steps if x["pred"] == C and x["recv"] != C and x["method"]]
        tok_ok = all(x["ok"] for x in tok) and bool(tok)
        res = next((x for x in steps if x["recv"] == C and x["method"] in ("ft_resolve_withdraw", "mt_resolve_withdraw")), None)
        for a, amount in wanted.items():
            if a not in backed:
                cov["withdrawals"]["of an id no contract backs"] += 1
                continue
            delivered = -(txH[tx][a] - txU[tx][a])
            debit = -txLo[tx][(a, owner)]
            if not is_call:
                cls = "ft/mt transfer delivered" if tok_ok else "transfer failed, refunded"
            elif not tok_ok:
                cls = "transfer_call failed"
            elif delivered == amount:
                cls = "transfer_call accepted in full"
            elif delivered == 0:
                cls = "transfer_call returned everything"
            else:
                cls = "transfer_call accepted in part"
            if nested or len(own) > 3:
                cls += " (nested calls)"
            cov["withdrawals"][cls] += 1
            if res is not None and any(x["recv"] == C and x["moves"] and x["tx"] != tx and root["h"] < x["h"] < res["h"] for x in t["steps"]):
                cov["withdrawals_overlapped"] += 1
            if not nested and len(own) <= 3 and debit != delivered:
                bad("withdraw_inexact", asset=a, op=op, h=steps[-1]["h"], amount=str(amount), owner=owner, debit=str(debit),
                    delivered=str(delivered), is_call=is_call, token_call_ok=tok_ok, forced=forced,
                    kind_of_op=o["kind"] if o else None)

    # the views after every block
    u_now = {}
    by_h = sorted(U_at)
    for ob in t["obs"]:
        h = ob["h"]
        while by_h and by_h[0] <= h:
            u_now = U_at[by_h.pop(0)]
        st = ob["state"]
        if "derive_mismatch" in ob:
            bad("derive_mismatch", h=h, detail=json.dumps(ob["derive_mismatch"])[:600])
        if "view_errors" in ob:
            bad("view_errors", h=h, detail=ob["view_errors"][:3])
        for tk in ob["tokens"]:
            if tk not in ids:
                bad("unknown_ledger_token", h=h, token=tk)
        idle = not ob["pending_ops"]
        cov["blocks"] += 1
        cov["idle_blocks"] += idle
        for tid in ids:
            L, S, H = sums(st, tid)
            if L != S:
                bad("supply_mismatch", where="views", h=h, token=tid, ledger_sum=str(L), supply=str(S))
            if tid not in backed:
                continue
            u = u_now.get(tid, 0)
            if L > H - u and ("v", tid) not in seen_over:
                seen_over.add(("v", tid))
                bad("overcredit", where="views", asset=tid, h=h, ledger_sum=str(L), held=str(H), unnotified=str(u), excess=str(L - (H - u)))
            if idle:
                g = sum(x for (hh, a, x) in G_tx if a == tid and hh <= h)
                cov["idle_checks"] += 1
                if L != H - u - g:
                    bad("quiescent_gap", asset=tid, h=h, ledger_sum=str(L), held=str(H), unnotified=str(u), stranded=str(g),
                        gap=str(H - u - g - L))

    # coverage of deposits and of signed intents
    for s in t["steps"]:
        if s["recv"] == C and s["method"] == "execute_intents" and isinstance(s["args"], dict):
            for p in s["args"].get("signed", []):
                try:
                    for it in json.loads(p["payload"]).get("intents", []):
                        cov["intents"][f'{it.get("intent")}: {"executed" if s["ok"] else "call failed"}'] += 1
                except (ValueError, KeyError, TypeError, AttributeError):
                    pass
        if s["recv"] == C and s["method"] in ("ft_on_transfer", "mt_on_transfer"):
            real = (s["pred"], None) in assets or any(c == s["pred"] for (c, _i) in assets)
            cov["deposits"][("token" if real else "caller that is no token") + (": credited" if s["ok"] else ": rejected")] += 1
    for o in ops:
        if o.get("probe"):
            cov["probe_ops"][o["probe"]] += 1
        cov["ops"][o["kind"]] += 1
        cov["ops_with_faults"] += bool(o["faults"])
        cov["ops_with_gas_limit"] += o["gas_tgas"] is not None
    cov["receipts"] += len(t["steps"])
    cov["refund_receipts"] += t["refund_receipts"]
    cov["max_pending"] = max(cov["max_pending"], max((len(o["pending_ops"]) for o in t["obs"]), default=0))
    return out


def new_cov():
    return {
        "calls": collections.defaultdict(lambda: [0, 0]), "ops": collections.Counter(), "deposits": collections.Counter(),
        "intents": collections.Counter(),
        "withdrawals": collections.Counter(), "private_attempts": collections.Counter(), "receipts": 0, "refund_receipts": 0,
        "unnotified_inflows": 0, "calls_while_paused": 0, "spends_by_locked": 0, "withdrawals_overlapped": 0, "blocks": 0,
        "idle_blocks": 0, "idle_checks": 0, "ops_with_faults": 0, "ops_with_gas_limit": 0, "max_pending": 0, "backing_checks": 0,
        "guarded": collections.defaultdict(lambda: collections.defaultdict(lambda: [0, 0])), "unauthorized_attempts": 0,
        "guarded_by_role": collections.defaultdict(lambda: collections.defaultdict(lambda: [0, 0])),
        "unauthorized_rejected_by_the_role_check": 0, "calls_with_auth_off": 0, "token_replies": collections.Counter(),
        "probe_ops": collections.Counter(), "receipts_moving_2^127_or_more": 0, "times_a_supply_reached_u128_max": 0,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*")
    ap.add_argument("--out")
    ap.add_argument("--violations")
    ap.add_argument("--sample-dir")
    ap.add_argument("--sample", type=int, default=0)
    ap.add_argument("--keep-violating", type=int, default=0)
    a = ap.parse_args()
    cov = new_cov()
    kinds = collections.Counter()
    detail = collections.Counter()
    traces = mock = 0
    seeds = set()
    with_viol = 0
    vf = open(a.violations, "w") if a.violations else None
    if a.sample_dir:
        os.makedirs(a.sample_dir, exist_ok=True)
    kept_v = kept_s = 0
    streams = [open(f) for f in a.files] if a.files else [sys.stdin]
    for f in streams:
        for line in f:
            if not line.strip():
                continue
            t = json.loads(line)
            traces += 1
            mock += bool(t.get("mock"))
            seeds.add(t.get("seed"))
            v = check_trace(t, cov)
            real = [x for x in v]
            for x in real:
                kinds[x["kind"]] += 1
                if x["kind"] == "own_callback_failed":
                    detail[f'own_callback_failed | {"fault injected" if x.get("forced") else "no fault injected"} | {x["method"]}: {x["status"][:70]}'
                           + (f' | in the probe {x["probe"]}' if x.get("probe") else "")] += 1
                if x["kind"] in ("tx_stranded", "tx_overcredit", "withdraw_inexact"):
                    detail[f'{x["kind"]} | {"fault injected" if x.get("forced") else "no fault injected"} | {x.get("cause") or ("is_call=%s token_call_ok=%s" % (x.get("is_call"), x.get("token_call_ok")))}'] += 1
                if vf:
                    vf.write(json.dumps(x) + "\n")
            with_viol += bool(real)
            if a.sample_dir:
                if real and kept_v < a.keep_violating:
                    kept_v += 1
                    open(os.path.join(a.sample_dir, f'violating-{t["id"]}.json'), "w").write(line)
                elif not real and kept_s < a.sample:
                    kept_s += 1
                    open(os.path.join(a.sample_dir, f'trace-{t["id"]}.json'), "w").write(line)
    harness = {k: kinds.get(k, 0) for k in ("sim_panic", "unsettled", "derive_mismatch", "view_errors", "derive_errors")}
    prop = {k: n for k, n in sorted(kinds.items()) if k not in harness}
    summary = {
        "traces": traces, "mock_traces": mock, "seeds": sorted(s for s in seeds if s is not None),
        "receipts": cov["receipts"], "gas_and_deposit_refund_receipts_not_listed": cov["refund_receipts"],
        "blocks_observed": cov["blocks"], "blocks_with_nothing_pending": cov["idle_blocks"],
        "backing_inequalities_checked_after_receipts": cov["backing_checks"],
        "quiescent_equalities_checked": cov["idle_checks"],
        "operations": dict(sorted(cov["ops"].items())), "operations_with_injected_faults": cov["ops_with_faults"],
        "operations_with_gas_limit": cov["ops_with_gas_limit"], "max_operations_pending_at_once": cov["max_pending"],
        "calls": {k: {"ok": v[0], "failed": v[1]} for k, v in sorted(cov["calls"].items())},
        "deposits": dict(sorted(cov["deposits"].items())), "withdrawals": dict(sorted(cov["withdrawals"].items())),
        "withdrawals_with_other_ledger_changes_before_their_callback": cov["withdrawals_overlapped"],
        "signed_intents": dict(sorted(cov["intents"].items())),
        "private_callback_attempts": dict(cov["private_attempts"]),
        "calls_to_paused_entry_points": cov["calls_while_paused"], "spends_by_locked_accounts": cov["spends_by_locked"],
        "calls_by_accounts_with_auth_by_predecessor_off": cov["calls_with_auth_off"],
        "guarded_calls_by_accounts_without_the_permission": cov["unauthorized_attempts"],
        "of_them_rejected_with_insufficient_permissions": cov["unauthorized_rejected_by_the_role_check"],
        "guarded_calls": {m: {c: {"ok": v[0], "failed": v[1]} for c, v in sorted(by.items())}
                          for m, by in sorted(cov["guarded"].items())},
        "guarded_calls_by_role_of_the_caller": {m: {c: {"ok": v[0], "failed": v[1]} for c, v in sorted(by.items())}
                                                for m, by in sorted(cov["guarded_by_role"].items())},
        "guarded_method_and_role_pairs_never_tried": sorted(
            f"{m} by {r}" for m in ROLES for r in ALL_ROLES + ["no role"] if r not in cov["guarded_by_role"].get(m, {})),
        "token_replies_read_by_ft_resolve_withdraw": dict(sorted(cov["token_replies"].items())),
        "probe_operations": dict(sorted(cov["probe_ops"].items())),
        "receipts_moving_2^127_or_more": cov["receipts_moving_2^127_or_more"],
        "times_a_supply_reached_u128_max": cov["times_a_supply_reached_u128_max"],
        "unnotified_inflows": cov["unnotified_inflows"],
        "traces_with_violations": with_viol, "violations": prop, "violation_detail": dict(sorted(detail.items())),
        "simulator_and_harness_failures": harness,
    }
    js = json.dumps(summary, indent=1)
    if a.out:
        open(a.out, "w").write(js + "\n")
    print(js)


if __name__ == "__main__":
    main()
