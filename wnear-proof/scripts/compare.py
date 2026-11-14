#!/usr/bin/env python3
"""Compare near-contract-sim traces (wnear-gen) with the Lean model's replay (wnearmodel).

usage: compare.py SIM.jsonl MODEL.jsonl [--json OUT]
Per receipt: success/failure, the resolve callback's return value, the NEAR transfers sent.
Per block: total_supply, the contract's NEAR balance, storage_usage, the whole accounts map.
"""
import json, sys
from collections import Counter

def main():
    sim_path, model_path = sys.argv[1], sys.argv[2]
    out_path = sys.argv[sys.argv.index("--json") + 1] if "--json" in sys.argv else None
    st = Counter(); methods = Counter(); rcases = Counter(); replies = Counter()
    mism = []; inter = Counter(); max_burnt = 0; wacts = Counter()
    with open(sim_path) as fs, open(model_path) as fm:
        for ls, lm in zip(fs, fm):
            t = json.loads(ls); m = json.loads(lm)
            tid = t["id"]; st["traces"] += 1
            if not t.get("settled", False): st["unsettled_traces"] += 1
            if t["obs"][0]["map"]: mism.append((tid, "init", "nonempty initial map"))
            for op in t["ops"]:
                if "ft_transfer_call" in op and "receiver:" in op:
                    lab = op.split("receiver: ")[1]
                    replies[lab.split(" ")[0].rstrip(",;")] += 1
                    if "held" in lab: replies["(resolve held)"] += 1
                    if "forced to fail" in lab: replies["(forced fail)"] += 1
            for a, n in t.get("wrap_actions", {}).items(): wacts[a] += n
            for g in t.get("resolve_gas", []):
                max_burnt = max(max_burnt, g[1])
            ss, ms = t["steps"], m["steps"]
            if len(ss) != len(ms):
                mism.append((tid, "steps", f"len {len(ss)} vs {len(ms)}")); continue
            # interleaving: other txs' wrap.near receipts between a transfer_call and its resolve
            pos = {}
            for i, s in enumerate(ss):
                if s["k"] != "call": continue
                if s["method"] == "ft_transfer_call" and s["ok"]: pos[s["tx"]] = i
                if s["method"] == "ft_resolve_transfer" and s["pred"] == t["self"] and s["tx"] in pos:
                    between = [x for x in ss[pos[s["tx"]] + 1:i] if x.get("tx") != s["tx"]]
                    inter["resolves"] += 1
                    if between: inter["with_foreign_receipts_between"] += 1
                    inter["foreign_receipts_between_total"] += len(between)
            for i, (s, md) in enumerate(zip(ss, ms)):
                st["receipts"] += 1
                key = s["k"] if s["k"] == "in" else s["method"] + ("" if s["pred"] != t["self"] else "@self")
                methods[(key, "ok" if s["ok"] else "fail")] += 1
                if s.get("oog"): st["out_of_gas_receipts"] += 1
                if md.get("rcase"): rcases[md["rcase"]] += 1
                if s["ok"] != md["ok"]:
                    mism.append((tid, f"step {i}", f"{key}: sim ok={s['ok']} ({s.get('status')}) model ok={md['ok']} args={s.get('args')} dep={s.get('deposit')} res={s.get('res')}"))
                    continue
                if s["k"] == "call" and s["ok"]:
                    if s["method"] == "ft_resolve_transfer":
                        sret = json.loads(s["ret"]) if s["ret"] else None
                        if sret != md.get("ret"):
                            mism.append((tid, f"step {i}", f"resolve ret sim={sret} model={md.get('ret')}"))
                    if [list(x) for x in s["transfers"]] != [list(x) for x in md.get("transfers", [])]:
                        mism.append((tid, f"step {i}", f"{key} transfers sim={s['transfers']} model={md.get('transfers')}"))
                    st["transfers_compared"] += len(s["transfers"])
            if len(t["obs"]) != len(m["obs"]):
                mism.append((tid, "obs", "length")); continue
            for so, mo in zip(t["obs"], m["obs"]):
                st["blocks"] += 1
                for f in ("supply", "near", "storage"):
                    if str(so[f]) != str(mo[f]):
                        mism.append((tid, f"h{so['h']}", f"{f} sim={so[f]} model={mo[f]}"))
                if so["map"] != mo["map"]:
                    mism.append((tid, f"h{so['h']}", f"map sim={so['map']} model={mo['map']}"))
                st["accounts_compared"] += len(so["map"])
    res = {
        "verdict": "EXACT" if not mism else "MISMATCH",
        "counts": dict(st), "mismatches": len(mism), "first_mismatches": mism[:40],
        "receipts_by_method": {f"{k[0]} {k[1]}": v for k, v in sorted(methods.items())},
        "resolve_branches": dict(rcases), "receiver_behaviours": dict(replies),
        "interleaving": dict(inter), "resolve_max_gas_burnt": max_burnt,
        "actions_sent_by_wrap_near": dict(wacts),
    }
    print(json.dumps(res, indent=1))
    if out_path:
        with open(out_path, "w") as f: json.dump(res, f, indent=1)
    return 0 if not mism else 1

if __name__ == "__main__":
    sys.exit(main())
