#!/usr/bin/env python3
"""Model-free property monitors for NEP-141 tokens, over the traces written by `ftmon run`.

usage: monitors.py TRACES.jsonl [TRACES.jsonl ...] --json OUT [--examples N]

The monitors read only what an outside observer sees: the views ft_total_supply / ft_balance_of
of every watched account after every block, and the receipts the token executed (who called what,
success or failure, the return value). No model of the token, no storage layout, no error texts,
no log format.

A trace is a list of rounds. A round of one operation ("single") gets every monitor. A round of
several interleaved operations ("batch") and the two funding rounds get the aggregate monitors
only: P1.supply_eq_sum, P2.refund_le_amount (reported side), P3.foreign_resolve_fails and
P4.lowered_only_by_holder. The checks of a settlement after the receiver made its own calls to
the token assume those calls moved exactly what they said.

The output says, per monitor, how many checks it made and how many of them were violations, and
lists under "inconclusive" every monitor that made no check and every kind of step the checks
depend on that never happened. A monitor with zero checks is not a pass.
"""
import hashlib
import json
import re
import sys
from collections import Counter

MONITORS = [
    ("P1.supply_eq_sum", "P1",
     "after every block ft_total_supply equals the sum of ft_balance_of over the watched accounts"),
    ("P1.exact_transfer", "P1",
     "a successful ft_transfer of an amount lowers the sender by exactly that amount, raises the receiver by "
     "exactly that amount and changes nobody else and not the supply; a failed one changes nothing"),
    ("P2.settlement_completed", "P2",
     "an accepted ft_transfer_call is settled: the token's own settlement callback runs, succeeds and returns "
     "the used amount"),
    ("P2.refund_le_amount", "P2",
     "the used amount the token reports and the tokens that move back to the sender do not exceed the "
     "transferred amount"),
    ("P2.reported_refund_eq_returned", "P2",
     "the refund the token reports (the amount minus the used amount its settlement returns) equals the "
     "tokens that actually moved back to the sender"),
    ("P2.receiver_keeps_used", "P2",
     "the receiver ends with exactly the amount minus the reported refund (minus what it paid out itself)"),
    ("P2.pair_conserved", "P2",
     "a settled ft_transfer_call changes only the sender and the receiver (and the accounts the receiver paid "
     "itself); the changes sum to zero and the supply does not change"),
    ("P2.refund_follows_reply", "P2",
     "the refund is what the receiver's reply asks for: min(unused, amount) when it returns a number, the "
     "whole amount when it fails"),
    ("P2.rejected_call_no_effect", "P2",
     "a rejected ft_transfer_call changes no balance and not the supply"),
    ("P3.foreign_resolve_fails", "P3",
     "the settlement callback run by anyone but the token's own pending transfer (a user, a contract, another "
     "contract's callback, a transaction signed with the token's key) fails"),
    ("P3.foreign_resolve_no_effect", "P3",
     "an attempt of a stranger to run the settlement callback changes no balance and not the supply"),
    ("P4.lowered_only_by_holder", "P4",
     "a balance falls in a round only if its holder made a successful call to the token in that round"),
    ("P4.non_transfer_op_changes_others", "P4",
     "storage_deposit, storage_withdraw, a view sent as a transaction, a repeated init and NEAR sent to the "
     "token change no balance; storage_unregister changes none but the caller's"),
    ("P5.unregister_refused", "P5",
     "storage_unregister without force=true by an account with a positive balance changes no balance and not "
     "the supply"),
]
NAMES = [m[0] for m in MONITORS]

# Why a monitor can have made no check at all.
NO_CHECKS = {
    "P1.supply_eq_sum": "no block was observed",
    "P1.exact_transfer": "no ft_transfer was sent in a round of its own",
    "P2.settlement_completed": "no ft_transfer_call was accepted in any trace",
    "P2.refund_le_amount": "no accepted ft_transfer_call was settled in any trace",
    "P2.reported_refund_eq_returned": "no accepted ft_transfer_call was settled in any trace",
    "P2.receiver_keeps_used": "no accepted ft_transfer_call was settled in any trace",
    "P2.pair_conserved": "no accepted ft_transfer_call was settled in any trace",
    "P2.refund_follows_reply": "no settlement followed a plain reply of the receiver (a number or a failure) in any trace",
    "P2.rejected_call_no_effect": "no ft_transfer_call was rejected in any trace",
    "P3.foreign_resolve_fails": "no call of the settlement callback by a stranger reached the token in any trace",
    "P3.foreign_resolve_no_effect": "no stranger tried the settlement callback in a round of its own",
    "P4.lowered_only_by_holder": "no watched account held a positive balance at the start of any round",
    "P4.non_transfer_op_changes_others": "no storage call, view, repeated init or NEAR transfer was sent in a round of its own",
    "P5.unregister_refused": "no account with a positive balance called storage_unregister without force in any trace",
}
# Kinds of steps the checks depend on: (coverage counter, monitors that need it, what it means when it is zero).
REQUIRED = [
    ("blocks_with_positive_supply", ["P1.supply_eq_sum"], "ft_total_supply was never positive"),
    ("transfers_ok_positive_amount", ["P1.exact_transfer"],
     "no ft_transfer of a positive amount succeeded in a round of its own"),
    ("transfers_failed", ["P1.exact_transfer"], "no ft_transfer failed in a round of its own"),
    ("settlements_with_refund",
     ["P2.refund_le_amount", "P2.reported_refund_eq_returned", "P2.receiver_keeps_used", "P2.pair_conserved"],
     "no settlement refunded a positive amount in any trace"),
    ("settlements_without_refund",
     ["P2.refund_le_amount", "P2.reported_refund_eq_returned", "P2.receiver_keeps_used", "P2.pair_conserved"],
     "no settlement left the whole amount with the receiver in any trace"),
    ("foreign_resolve_positive_amount", ["P3.foreign_resolve_no_effect"],
     "no stranger tried the settlement callback for a positive amount"),
    ("balance_falls_after_own_call", ["P4.lowered_only_by_holder"], "no balance fell in any trace"),
]
PURE = ("num", "panic", "bytes", "limit", "json_number", "no_stub")
ACCOUNT_RE = re.compile(r"^(([a-z\d]+[-_])*[a-z\d]+\.)*([a-z\d]+[-_])*[a-z\d]+$")


def num(x):
    return int(x) if isinstance(x, str) and x.isdigit() else None


def main():
    argv = sys.argv[1:]
    paths, out_path, n_ex = [], None, 3
    i = 0
    while i < len(argv):
        if argv[i] == "--json":
            out_path = argv[i + 1]; i += 2
        elif argv[i] == "--examples":
            n_ex = int(argv[i + 1]); i += 2
        else:
            paths.append(argv[i]); i += 1
    if not paths:
        print(__doc__); return 2
    checked = Counter(); fired = Counter(); examples = {n: [] for n in NAMES}
    st = Counter(); ops = Counter(); cov = Counter(); kinds_fired = {n: Counter() for n in NAMES}
    methods = {}
    digests = {}
    first = {}

    def fire(name, tid, ri, kind, detail, op=None):
        fired[name] += 1
        kinds_fired[name][kind] += 1
        if len(examples[name]) < n_ex:
            examples[name].append({"trace": tid, "round": ri, "step": kind, "detail": detail, "op": op})

    def balances(o):
        b = o.get("_b")
        if b is None:
            b = {}
            for a, v in o["bal"].items():
                n = num(v)
                if n is None:
                    # the watched names include two deliberately invalid account ids; a view of them may fail
                    valid = 2 <= len(a) <= 64 and ACCOUNT_RE.match(a) is not None
                    st["balance_views_without_a_number" if valid else "balance_views_of_invalid_ids_without_a_number"] += 1
                    n = 0
                b[a] = n
            o["_b"] = b
        return b

    def judge(t):
        tid = t["id"]; token = t["token"]; st["traces"] += 1
        RES = t.get("resolve_method", "ft_resolve_transfer")  # the token's settlement callback
        if not t.get("settled", True):
            st["unsettled_traces"] += 1

        def p1(o, ri, kind):
            checked["P1.supply_eq_sum"] += 1
            s = num(o["supply"])
            tot = sum(balances(o).values())
            if s is not None and s > 0:
                cov["blocks_with_positive_supply"] += 1
            if s is None or s != tot:
                fire("P1.supply_eq_sum", tid, ri, kind, f"h{o['h']}: ft_total_supply {o['supply']} != sum of balances {tot}")

        prev = t["init"]
        p1(prev, -1, "initial state")
        if not first:
            first["initial_supply"] = prev["supply"]
        for ri, r in enumerate(t["rounds"]):
            kind = r["kind"]; st[f"rounds_{kind}"] += 1
            blocks = r["blocks"]; st["blocks"] += len(blocks)
            opnames = "+".join(sorted({o["op"] for o in r["ops"]})) or "none"
            label = opnames if kind == "single" else f"{kind} round ({opnames})"
            for b in blocks:
                p1(b, ri, label)
            post = blocks[-1] if blocks else prev
            pb, qb = balances(prev), balances(post)
            accts = list(qb)
            delta = {a: qb[a] - pb.get(a, 0) for a in accts}
            ds = (num(post["supply"]) or 0) - (num(prev["supply"]) or 0)
            recs = r["receipts"]
            tok = [x for x in recs if x["recv"] == token]
            st["token_receipts"] += len(tok); st["token_receipts_ok"] += sum(1 for x in tok if x["ok"])
            st["out_of_gas_receipts"] += sum(1 for x in tok if x.get("oog"))
            for x in tok:
                m = methods.setdefault(x["method"], [0, 0])
                m[0] += 1; m[1] += 1 if x["ok"] else 0
            # --- aggregate monitors, every round ---
            own_ok = {x["pred"] for x in tok if x["ok"]}
            checked["P4.lowered_only_by_holder"] += sum(1 for a in accts if pb.get(a, 0) > 0)
            for a, d in delta.items():
                if d < 0 and a not in own_ok:
                    fire("P4.lowered_only_by_holder", tid, ri, label,
                         f"{a} lost {-d} in a round where it made no successful call to the token",
                         r["ops"] if kind == "single" else None)
                elif d < 0:
                    cov["balance_falls_after_own_call"] += 1
            accepted_tx = {x["tx"] for x in tok if x["method"] == "ft_transfer_call" and x["ok"]}
            asked = {o["tx"]: int(o["amount"]) for o in r["ops"] if o["op"] == "ft_transfer_call"}
            for x in tok:
                if x["method"] != RES:
                    continue
                own = x["pred"] == token and x["callback"] and x["tx"] in accepted_tx
                if not own:
                    checked["P3.foreign_resolve_fails"] += 1
                    if x["ok"]:
                        fire("P3.foreign_resolve_fails", tid, ri, label,
                             f"{RES} run by {x['pred']} (as a callback: {x['callback']}) succeeded")
                elif x["ok"] and kind != "single":
                    try:
                        a = asked[x["tx"]] if x["tx"] in asked else int(json.loads(x["args"])["amount"])
                        used = int(x["ret"]["json"])
                    except (ValueError, KeyError, TypeError):
                        continue
                    checked["P2.refund_le_amount"] += 1
                    if used > a:
                        fire("P2.refund_le_amount", tid, ri, label, f"the settlement reported used {used} > amount {a}")
            for o in r["ops"]:
                main_r = next((x for x in tok if x["tx"] == o["tx"] and x["pred"] == o.get("caller")), None)
                ops[(o["op"], "ok" if (main_r and main_r["ok"]) else "fail")] += 1
            if kind != "single":
                prev = post
                continue
            # --- exact monitors, rounds of one operation ---
            o = r["ops"][0]; who = o.get("caller"); tx = o["tx"]
            mine = [x for x in tok if x["tx"] == tx]
            changed = {a: d for a, d in delta.items() if d != 0}
            if o["op"] == "ft_transfer":
                rc = next((x for x in mine if x["method"] == "ft_transfer" and x["pred"] == who), None)
                amt = int(o["amount"]); exp = Counter()
                if rc and rc["ok"]:
                    exp[who] -= amt; exp[o["to"]] += amt
                    if amt > 0:
                        cov["transfers_ok_positive_amount"] += 1
                else:
                    cov["transfers_failed"] += 1
                checked["P1.exact_transfer"] += 1
                bad = {a: (delta.get(a, 0), exp.get(a, 0)) for a in set(accts) | set(exp) if delta.get(a, 0) != exp.get(a, 0)}
                if bad or ds != 0:
                    fire("P1.exact_transfer", tid, ri, "ft_transfer (%s)" % ("successful" if rc and rc["ok"] else "failed"),
                         f"amount {amt}; (observed, expected) changes that differ: {bad}; supply change {ds}", o)
            elif o["op"] == "ft_transfer_call":
                rc = next((x for x in mine if x["method"] == "ft_transfer_call" and x["pred"] == who), None)
                amt = int(o["amount"]); rcv = o["to"]; reply = o.get("reply") or {}; fault = o.get("fault")
                if not (rc and rc["ok"]):
                    checked["P2.rejected_call_no_effect"] += 1
                    if changed or ds != 0:
                        fire("P2.rejected_call_no_effect", tid, ri, "ft_transfer_call (rejected)",
                             f"changes {changed}, supply change {ds}", o)
                    prev = post
                    continue
                res = next((x for x in mine if x["method"] == RES and x["pred"] == token and x["callback"]), None)
                on = next((x for x in recs if x["tx"] == tx and x["method"] == "ft_on_transfer"), None)
                checked["P2.settlement_completed"] += 1
                used = None
                if res is not None and res["ok"]:
                    try:
                        used = int(res["ret"]["json"])
                    except (ValueError, KeyError, TypeError):
                        used = None
                if used is None:
                    fire("P2.settlement_completed", tid, ri, "ft_transfer_call settlement",
                         "the token's %s callback %s (receiver reply: %s, fault: %s)" % (
                             RES, "did not run" if res is None else ("failed: " + res["status"][:120] if not res["ok"] else "returned no amount"),
                             reply.get("kind"), fault), o)
                    prev = post
                    continue
                if who == rcv:
                    st["self_transfer_call_accepted"] += 1
                    prev = post
                    continue
                rep_refund = amt - used
                by_rcv = [x for x in mine if x["pred"] == rcv and x["ok"] and x is not res]
                nested = []
                for x in by_rcv:
                    if x["method"] == "ft_transfer":
                        try:
                            a = json.loads(x["args"]); nested.append((a["receiver_id"], int(a["amount"])))
                        except (ValueError, KeyError, TypeError):
                            pass
                unreg = any(x["method"] == "storage_unregister" for x in by_rcv)
                other_nested = any(x["method"] not in ("ft_transfer", "storage_unregister") for x in by_rcv)
                to_sender = sum(a for (to, a) in nested if to == who)
                out_of_rcv = sum(a for (to, a) in nested if to != rcv)
                step = "ft_transfer_call settlement (receiver reply: %s%s)" % (reply.get("kind"), ", " + json.dumps(fault) if fault else "")
                checked["P2.refund_le_amount"] += 1
                moved_back = delta.get(who, 0) + amt - to_sender
                if used > amt or (to_sender == 0 and not (0 <= moved_back <= amt)):
                    fire("P2.refund_le_amount", tid, ri, step,
                         f"amount {amt}, reported used {used}, moved back to the sender {moved_back}", o)
                checked["P2.reported_refund_eq_returned"] += 1
                exp_s = -amt + rep_refund + to_sender
                exp_r = amt - rep_refund - out_of_rcv
                if delta.get(who, 0) != exp_s:
                    fire("P2.reported_refund_eq_returned", tid, ri, step,
                         f"amount {amt}, reported used {used}: reported refund {rep_refund}, moved back to the sender {moved_back}", o)
                if not unreg and not other_nested:
                    checked["P2.receiver_keeps_used"] += 1
                    if delta.get(rcv, 0) != exp_r:
                        fire("P2.receiver_keeps_used", tid, ri, step,
                             f"amount {amt}, reported used {used}: the receiver changed by {delta.get(rcv, 0)}, amount - reported refund - own payments = {exp_r}", o)
                cov["settlements_with_refund" if rep_refund > 0 else "settlements_without_refund"] += 1
                if not unreg and not other_nested:
                    checked["P2.pair_conserved"] += 1
                    allowed = {who, rcv} | {to for (to, _) in nested}
                    outside = {a: d for a, d in changed.items() if a not in allowed}
                    if outside or ds != 0 or sum(delta.values()) != 0:
                        fire("P2.pair_conserved", tid, ri, step,
                             f"amount {amt}; changes outside sender/receiver {outside}; sum of all changes {sum(delta.values())}; supply change {ds}", o)
                if reply.get("kind") in PURE and not by_rcv and on is not None:
                    expd = None
                    if (not on["ok"]) or fault == "promise_failed":
                        expd = amt
                    elif reply.get("kind") == "num":
                        expd = min(int(reply["u"]), amt)
                    if expd is not None:
                        checked["P2.refund_follows_reply"] += 1
                        if rep_refund != expd:
                            fire("P2.refund_follows_reply", tid, ri, step,
                                 f"amount {amt}, the receiver's side asks for a refund of {expd}, the token reports {rep_refund}", o)
            elif o["op"] == "foreign_resolve":
                rr = [x for x in mine if x["method"] == RES]
                cov["foreign_resolve_reached_token"] += len(rr)
                cov["foreign_resolve_" + o["way"]] += 1
                try:
                    if int(o["args"]["amount"]) > 0:
                        cov["foreign_resolve_positive_amount"] += 1
                except (ValueError, KeyError, TypeError):
                    pass
                checked["P3.foreign_resolve_no_effect"] += 1
                if changed or ds != 0:
                    fire("P3.foreign_resolve_no_effect", tid, ri, "%s by a stranger (%s)" % (RES, o["way"]),
                         f"changes {changed}, supply change {ds}", o)
            elif o["op"] in ("storage_deposit", "storage_withdraw", "other", "reinit", "near_transfer", "storage_unregister"):
                checked["P4.non_transfer_op_changes_others"] += 1
                ch = {a: d for a, d in changed.items() if not (o["op"] == "storage_unregister" and a == who)}
                if ch:
                    fire("P4.non_transfer_op_changes_others", tid, ri, o["op"], f"changes {ch}", o)
                if o["op"] == "storage_unregister" and (o.get("args") or {}).get("force") is not True and pb.get(who, 0) > 0:
                    checked["P5.unregister_refused"] += 1
                    if changed or ds != 0:
                        fire("P5.unregister_refused", tid, ri, "storage_unregister without force",
                             f"the caller held {pb.get(who, 0)}; changes {changed}, supply change {ds}", o)
            prev = post

    for path in paths:
        with open(path, "rb") as f:
            for raw in f:
                raw = raw.rstrip(b"\n")
                if not raw:
                    continue
                t = json.loads(raw)
                if t["id"] in digests:
                    print(f"trace {t['id']} occurs twice", file=sys.stderr); return 2
                digests[t["id"]] = hashlib.sha256(raw).hexdigest()
                judge(t)

    h = hashlib.sha256()
    for tid in sorted(digests):
        h.update(f"{tid}:{digests[tid]}\n".encode())
    inconclusive = []
    for n in NAMES:
        if checked[n] == 0:
            inconclusive.append({"monitor": n, "reason": NO_CHECKS[n]})
    for key, mons, why in REQUIRED:
        if cov[key] == 0 and not any(x["reason"] == why for x in inconclusive):
            inconclusive.append({"monitors": mons, "coverage": key, "reason": why})
    if st["unsettled_traces"]:
        inconclusive.append({"reason": "%d trace(s) still had receipts pending after 200 blocks" % st["unsettled_traces"]})
    res = {
        "traces": st["traces"],
        "trace_digest": h.hexdigest(),
        "initial_supply": first.get("initial_supply"),
        "counts": {k: st[k] for k in sorted(st)},
        "operations": {f"{k[0]} {k[1]}": v for k, v in sorted(ops.items())},
        "methods": {m: {"receipts": v[0], "successful": v[1]} for m, v in sorted(methods.items())},
        "coverage": {k: cov[k] for k in sorted(set(cov) | {r[0] for r in REQUIRED})},
        "monitors": {n: {"property": p, "statement": s, "checks": checked[n], "violations": fired[n],
                         "violations_by_step": dict(kinds_fired[n]), "examples": examples[n]} for n, p, s in MONITORS},
        "fired": [n for n in NAMES if fired[n]],
        "inconclusive": inconclusive,
    }
    if out_path:
        with open(out_path, "w") as f:
            json.dump(res, f, indent=1)
    brief = {k: res[k] for k in ("traces", "fired", "inconclusive")}
    brief["monitors"] = {n: [checked[n], fired[n]] for n in NAMES}
    print(json.dumps(brief, indent=1))
    return 1 if res["fired"] else (2 if inconclusive else 0)


if __name__ == "__main__":
    sys.exit(main())
