#!/usr/bin/env python3
"""Compare near-contract-sim traces (ftcert-gen) with the Lean model's replay (ftmodel).

usage: compare.py SIM.jsonl MODEL.jsonl [--json OUT]

Per receipt on the token: success/failure, return value, NEAR transfers sent, function calls
sent (ft_on_transfer arguments, settlement callback arguments and its exact gas), NEP-141
events logged. Per block: total_supply, the token's NEAR balance, storage_usage, the whole
accounts map. Independently of the model, monitors check P1/P2/P3/P4 on the sim alone.
Every divergence is attributed to the property whose proof covers that behaviour.
"""
import json
import sys
from collections import Counter

PROPS = ["P1", "P2", "P3", "P4", "P5"]


def prop_of(step, self_id):
    """The property whose proof covers what this receipt does."""
    if step.get("k") != "call":
        return "P5"  # NEAR arriving: storage accounting
    m = step["method"]
    if m == "ft_resolve_transfer":
        return "P2" if (step["pred"] == self_id and step.get("callback")) else "P3"
    if m in ("ft_transfer", "ft_transfer_call"):
        return "P4"
    if m in ("ft_total_supply", "ft_balance_of"):
        return "P1"
    return "P5"  # storage_* methods, storage views, re-init, unknown methods


def norm_ret(r):
    if r is None:
        return None
    if r.get("kind") == "value":
        return ("value", json.dumps(r.get("json"), sort_keys=True))
    return (r.get("kind"), r.get("hex"))


def expected_calls(self_id, model_calls):
    out = []
    for c in model_calls:
        out.append(("ft_on_transfer", c["receiver"], json.dumps(c["on_args"], sort_keys=True), "0", None))
        out.append(("ft_resolve_transfer", c["resolve_receiver"], json.dumps(c["resolve_args"], sort_keys=True),
                    "0", int(c["resolve_gas"])))
    return sorted(out, key=str)


def sim_calls(step):
    out = []
    for c in step.get("calls", []):
        try:
            args = json.dumps(json.loads(c.get("args") or "null"), sort_keys=True)
        except ValueError:
            args = c.get("args")
        gas = int(c["gas"]) if c.get("method") == "ft_resolve_transfer" else None
        out.append((c.get("method"), c["receiver"], args, c.get("deposit"), gas))
    return sorted(out, key=str)


def sim_events(step):
    evs = []
    for l in step.get("logs", []):
        if l.startswith("EVENT_JSON:"):
            try:
                evs.append(json.loads(l[len("EVENT_JSON:"):]))
            except ValueError:
                evs.append({"unparsable": l})
    return evs


def main():
    sim_path, model_path = sys.argv[1], sys.argv[2]
    out_path = sys.argv[sys.argv.index("--json") + 1] if "--json" in sys.argv else None
    st = Counter(); methods = Counter(); rcases = Counter(); replies = Counter(); inter = Counter()
    on_status = Counter(); props_hit = Counter()
    first = None; mism_total = 0; mism_by_prop = Counter(); first_by_prop = Counter(); examples = []
    monitors = {p: [] for p in PROPS}
    init_bad = []
    with open(sim_path) as fs, open(model_path) as fm:
        for ls, lm in zip(fs, fm):
            t = json.loads(ls); m = json.loads(lm)
            tid = t["id"]; self_id = t["self"]; st["traces"] += 1
            if not t.get("settled", False):
                st["unsettled_traces"] += 1
            if not m.get("init_ok", {}).get("all", False):
                init_bad.append((tid, m.get("init_ok")))
            for op in t["ops"]:
                if "ft_transfer_call" in op and "receiver:" in op:
                    lab = op.split("receiver: ")[1]
                    replies[lab.split(" ")[0].rstrip(",;")] += 1
                    if "held" in lab:
                        replies["(settlement held)"] += 1
                    if "forced to fail" in lab:
                        replies["(forced fail)"] += 1
            for x in t.get("on_transfer", []):
                on_status["ok" if x["ok"] else "failed"] += 1
            ss, ms = t["steps"], m.get("steps", [])
            found = []  # (h, order, idx, record)

            def add(h, order, idx, kind, prop, detail, step=None):
                rec = {"trace": tid, "h": h, "kind": kind, "property": prop, "detail": detail}
                if step is not None:
                    rec.update({"step": idx, "method": step.get("method"), "pred": step.get("pred"),
                                "args": step.get("args"), "deposit": step.get("deposit"),
                                "sim_status": step.get("status")})
                found.append((h, order, idx, rec))

            if len(ss) != len(ms):
                add(0, 0, 0, "steps", "P1", f"receipt count {len(ss)} vs {len(ms)}")
            # interleaving: other transactions' token receipts between a transfer_call and its settlement
            pos = {}
            children_of_tc = set()
            for i, s in enumerate(ss):
                if s["k"] != "call":
                    continue
                if s["method"] == "ft_transfer_call" and s["ok"]:
                    pos[s["tx"]] = i
                    children_of_tc.update(s.get("children", []))
                if s["method"] == "ft_resolve_transfer" and s["pred"] == self_id and s["tx"] in pos:
                    between = [x for x in ss[pos[s["tx"]] + 1:i] if x.get("tx") != s["tx"]]
                    inter["settlements"] += 1
                    if between:
                        inter["with_foreign_receipts_between"] += 1
                    inter["foreign_receipts_between_total"] += len(between)
            # receipt-level comparison
            for i, (s, md) in enumerate(zip(ss, ms)):
                st["receipts"] += 1
                key = s["k"] if s["k"] == "in" else s["method"] + ("@self" if s["pred"] == self_id else "")
                methods[(key, "ok" if s["ok"] else "fail")] += 1
                if s.get("oog"):
                    st["out_of_gas_receipts"] += 1
                if md.get("rcase"):
                    rcases[md["rcase"]] += 1
                p = prop_of(s, self_id)
                if s["ok"] != md["ok"]:
                    add(s["h"], 0, i, "success", p, f"sim ok={s['ok']} model ok={md['ok']} res={s.get('res')}", s)
                    continue
                if s["k"] != "call" or not s["ok"]:
                    continue
                st["returns_compared"] += 1
                if norm_ret(s.get("ret")) != norm_ret(md.get("ret")):
                    add(s["h"], 0, i, "return", p, f"sim={s.get('ret')} model={md.get('ret')}", s)
                if [list(x) for x in s["transfers"]] != [list(x) for x in md.get("transfers", [])]:
                    add(s["h"], 0, i, "near-transfers", "P5" if p != "P2" else p,
                        f"sim={s['transfers']} model={md.get('transfers')}", s)
                st["transfers_compared"] += len(s["transfers"])
                ec = expected_calls(self_id, md.get("calls", []))
                sc = sim_calls(s)
                if ec != sc:
                    gas_only = [x[:4] for x in ec] == [x[:4] for x in sc]
                    add(s["h"], 0, i, "calls-gas" if gas_only else "calls", "P2" if gas_only else p,
                        f"sim={sc} model={ec}", s)
                st["calls_compared"] += len(sc)
                if s.get("other_actions"):
                    add(s["h"], 0, i, "other-actions", p, f"token sent {s['other_actions']}", s)
                se, me = sim_events(s), md.get("events", [])
                if se != me:
                    add(s["h"], 0, i, "events", p, f"sim={se} model={me}", s)
                st["events_compared"] += len(se)
            # block-level comparison
            mo_list = m.get("obs", [])
            if len(t["obs"]) != len(mo_list):
                add(0, 1, 0, "obs", "P1", "block count differs")
            for so, mo in zip(t["obs"], mo_list):
                st["blocks"] += 1
                for f, prop in (("supply", "P1"), ("near", "P5"), ("storage", "P5")):
                    if str(so[f]) != str(mo[f]):
                        add(so["h"], 1, 0, f"block-{f}", prop, f"h{so['h']} {f} sim={so[f]} model={mo[f]}")
                if so["map"] != mo["map"]:
                    diff = {k: (so["map"].get(k), mo["map"].get(k)) for k in set(so["map"]) | set(mo["map"])
                            if so["map"].get(k) != mo["map"].get(k)}
                    # the map changes only through receipts in this block: blame the first of them
                    blk = [x for x in ss if x.get("h") == so["h"] and x.get("k") == "call" and x.get("ok")]
                    prop = prop_of(blk[0], self_id) if blk else "P1"
                    add(so["h"], 1, 0, "block-map", prop, f"h{so['h']} accounts sim/model: {diff}")
                st["accounts_compared"] += len(so["map"])
            # --- monitors on the sim alone (no model) ---
            obs = t["obs"]
            for so in obs:  # P1: supply = sum of balances after every block
                try:
                    if int(so["supply"]) != sum(int(v) for v in so["map"].values()):
                        monitors["P1"].append({"trace": tid, "h": so["h"],
                                               "detail": f"supply {so['supply']} != sum {sum(int(v) for v in so['map'].values())}"})
                except ValueError:
                    monitors["P1"].append({"trace": tid, "h": so["h"], "detail": f"supply view: {so['supply']}"})
            for i, s in enumerate(ss):
                if s["k"] != "call" or s["method"] != "ft_resolve_transfer" or not s["ok"]:
                    continue
                own = s["pred"] == self_id and s.get("callback") and s["rid"] in children_of_tc
                if not own:  # P3: only the token's own settlement callback may succeed
                    monitors["P3"].append({"trace": tid, "h": s["h"], "step": i,
                                           "detail": f"ft_resolve_transfer by {s['pred']} (callback={s.get('callback')}) succeeded, args {s['args']}"})
                try:  # P2: the used amount never exceeds the transferred amount
                    a = int(json.loads(s["args"])["amount"])
                    used = int(s["ret"]["json"])
                    if used > a:
                        monitors["P2"].append({"trace": tid, "h": s["h"], "step": i,
                                               "detail": f"settlement returned used={used} > amount={a}"})
                except (ValueError, KeyError, TypeError):
                    pass
            for prev, cur in zip(obs, obs[1:]):  # P4: who lowered a balance in this block
                blk = [x for x in ss if x.get("h") == cur["h"] and x.get("k") == "call" and x.get("ok")]
                for u, pv in prev["map"].items():
                    dec = int(pv) - int(cur["map"].get(u, "0"))
                    if dec <= 0:
                        continue
                    if any(x["pred"] == u for x in blk):
                        continue
                    back = 0
                    for x in blk:
                        if x["method"] == "ft_resolve_transfer" and x["pred"] == self_id and x.get("callback"):
                            try:
                                a = json.loads(x["args"])
                                if a.get("receiver_id") == u:
                                    back += int(a["amount"])
                            except (ValueError, KeyError):
                                pass
                    if dec > back:
                        monitors["P4"].append({"trace": tid, "h": cur["h"],
                                               "detail": f"{u} lost {dec} with no own call and settlements to it of {back}"})
            if found:
                found.sort(key=lambda x: (x[0], x[1], x[2]))
                mism_total += len(found)
                # after the first divergence the two states differ and later mismatches are
                # consequences: attribute each diverging trace to its first divergence only
                first_by_prop[found[0][3]["property"]] += 1
                for f in found:
                    mism_by_prop[f[3]["property"]] += 1
                if first is None:
                    first = found[0][3]
                    first["trace_ops"] = t["ops"]
                if len(examples) < 20:
                    examples.extend(f[3] for f in found[:2])
    mon_counts = {p: len(v) for p, v in monitors.items()}
    failed = sorted(set(first_by_prop) | {p for p, v in monitors.items() if v} | ({"P1", "P5"} if init_bad else set()))
    res = {
        "verdict": "EXACT" if mism_total == 0 and not any(mon_counts.values()) and not init_bad else "MISMATCH",
        "counts": dict(st),
        "mismatches": mism_total,
        "mismatches_by_property": dict(mism_by_prop),
        "diverging_traces": sum(first_by_prop.values()),
        "diverging_traces_by_first_property": dict(first_by_prop),
        "monitor_violations": mon_counts,
        "monitor_examples": {p: v[:3] for p, v in monitors.items() if v},
        "init_ok_failures": init_bad[:5],
        "failed_properties": failed,
        "first_divergence": first,
        "examples": examples[:20],
        "receipts_by_method": {f"{k[0]} {k[1]}": v for k, v in sorted(methods.items())},
        "settlement_branches": dict(rcases),
        "receiver_behaviours": dict(replies),
        "ft_on_transfer_outcomes": dict(on_status),
        "interleaving": dict(inter),
    }
    print(json.dumps(res, indent=1))
    if out_path:
        with open(out_path, "w") as f:
            json.dump(res, f, indent=1)
    return 0 if res["verdict"] == "EXACT" else 1


if __name__ == "__main__":
    sys.exit(main())
