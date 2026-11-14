#!/usr/bin/env python3
"""Checks, on harness traces of the deployed wasm, the facts about NEAR's promise plumbing that
the two-contract world with wNEAR takes as hypotheses (NOTES.md, section 10). A test on
recorded receipts, not a proof.

usage: wnear_glue.py < traces.jsonl      (format: ../FORMAT.md)
Prints one JSON object with the counts; exit status 1 if any check failed.
"""
import collections
import json
import sys

WNEAR = "wrap.near"
CALLBACKS = ("do_native_withdraw", "do_storage_deposit", "do_ft_withdraw", "do_mt_withdraw")


def main():
    c = collections.Counter()
    bad = []

    def check(name, cond, where):
        c[name] += 1
        if not cond:
            c[name + ":FAILED"] += 1
            if len(bad) < 20:
                bad.append([name, where])

    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        t = json.loads(line)
        if "steps" not in t:
            continue
        me = t["world"]["contract"]
        steps = t["steps"]
        byrid = {s["rid"]: s for s in steps}
        got = 0       # NEAR wNEAR sent to the contract in its near_withdraw receipts
        fwd = 0       # NEAR the do_* callbacks sent on
        burned = 0    # wNEAR burned by the contract's near_withdraw receipts
        for s in steps:
            where = [t["id"], s["i"]]
            m = s.get("method")
            # H-a: near_withdraw sent by the contract
            if s["recv"] == WNEAR and s["pred"] == me and m == "near_withdraw":
                x = int(s["args"]["amount"])
                check("near_withdraw.deposit_is_1_yocto", s["deposit"] == "1", where)
                if s["ok"]:
                    c["near_withdraw.ok"] += 1
                    mv = sorted(((a[0], a[1], a[2], int(a[3])) for a in s["moves"]
                                 if a[0] == WNEAR), key=str)
                    want = sorted([(WNEAR, None, me, -x), (WNEAR, None, None, -x)], key=str)
                    check("near_withdraw.burns_exactly_amount", mv == want, where)
                    tr = [k for k in s["calls"] if k["actions"] == ["Transfer"]]
                    check("near_withdraw.one_transfer_of_amount_plus_1",
                          len(tr) == 1 and tr[0]["recv"] == me and int(tr[0]["deposit"]) == x + 1
                          and len(s["calls"]) == 1, where)
                    got += x + 1
                    burned += x
                else:
                    c["near_withdraw.failed:" + ("forced" if s["fault"] else s["status"][:30])] += 1
                    check("near_withdraw.failed_moves_nothing", s["moves"] == [], where)
            # H-b: the callbacks chained to near_withdraw
            if s["recv"] == me and s["pred"] == me and m in CALLBACKS:
                wd = s["args"].get("withdraw") or {}
                unwraps = m in ("do_native_withdraw", "do_storage_deposit") or \
                    wd.get("storage_deposit") is not None
                if not unwraps:
                    continue
                c["callback"] += 1
                r = s["results"][0] if s["results"] else None
                src = byrid.get(r["from"]) if r and r.get("from") else None
                if r and r["ok"]:
                    check("callback.ok_result_is_empty", r.get("hex") == "", where)
                    check("callback.ok_result_comes_from_the_transfer_to_the_contract",
                          src is not None and src["recv"] == me and src["actions"] == ["Transfer"]
                          and src["ok"], where)
                else:
                    c["callback.reads_failure"] += 1
                    check("callback.failure_comes_from_near_withdraw",
                          src is not None and src["recv"] == WNEAR
                          and src.get("method") == "near_withdraw" and not src["ok"], where)
                    check("callback.on_failure_fails_and_sends_nothing",
                          (not s["ok"]) and s["calls"] == [], where)
                    check("callback.on_failure_ledger_untouched", s["moves"] == [], where)
                if s["ok"]:
                    c["callback.ran"] += 1
                    if m == "do_native_withdraw":
                        amt = int(s["args"]["withdraw"]["amount"])
                    elif m == "do_storage_deposit":
                        amt = int(s["args"]["storage_deposit"]["amount"])
                    else:
                        amt = int(wd["storage_deposit"])
                    k = s["calls"]
                    check("callback.sends_exactly_the_amount",
                          len(k) == 1 and int(k[0]["deposit"]) in (amt, amt + 1), where)
                    check("callback.ledger_untouched", s["moves"] == [], where)
                    fwd += amt
            # H-c: wNEAR's settlement of a transfer to the contract reads the contract's answer
            if s["recv"] == WNEAR and m == "ft_resolve_transfer" and \
                    s["args"].get("receiver_id") == me and s["pred"] == WNEAR:
                r = s["results"][0] if s["results"] else None
                src = byrid.get(r["from"]) if r and r.get("from") else None
                c["settle_deposit"] += 1
                if r and r["ok"]:
                    check("settle_deposit.reads_the_bytes_of_0", r.get("hex") == "223022", where)
                    if s["ok"]:
                        check("settle_deposit.credited_then_no_refund",
                              [a for a in s["moves"] if a[0] == WNEAR] == [], where)
                    check("settle_deposit.source_is_ft_on_transfer",
                          src is not None and src["recv"] == me
                          and src.get("method") == "ft_on_transfer" and src["ok"], where)
                else:
                    c["settle_deposit.reads_failure"] += 1
                    check("settle_deposit.failure_source_is_ft_on_transfer",
                          src is not None and src["recv"] == me
                          and src.get("method") == "ft_on_transfer" and not src["ok"], where)
            # H-d: what ft_resolve_withdraw reads for a withdrawal of wNEAR
            if s["recv"] == me and s["pred"] == me and m == "ft_resolve_withdraw" and \
                    s["args"].get("token") == WNEAR:
                r = s["results"][0] if s["results"] else None
                src = byrid.get(r["from"]) if r and r.get("from") else None
                c["resolve_withdraw"] += 1
                if r and r["ok"]:
                    if s["args"]["is_call"]:
                        ret = (src or {}).get("ret") or {}
                        check("resolve_withdraw.call_reads_the_u128_wnear_returned",
                              src is not None and src["recv"] == WNEAR
                              and src.get("method") == "ft_resolve_transfer"
                              and isinstance(r.get("json"), str) and r["json"].isdigit()
                              and ret.get("json") == r["json"], where)
                    else:
                        check("resolve_withdraw.plain_reads_empty",
                              r.get("hex") == "" and src is not None and src["recv"] == WNEAR,
                              where)
                else:
                    c["resolve_withdraw.reads_failure"] += 1
        check("trace.near_sent_on_le_wnear_burned_le_near_received",
              fwd <= burned <= got, [t["id"], None])
        c["sum.near_received"] += got
        c["sum.near_sent_on"] += fwd
        c["sum.wnear_burned"] += burned
        c["traces"] += 1

    failed = sum(v for k, v in c.items() if k.endswith(":FAILED"))
    print(json.dumps({"counts": dict(sorted(c.items())), "failed": failed, "first_failures": bad},
                     indent=1))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
