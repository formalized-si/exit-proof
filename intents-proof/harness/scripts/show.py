#!/usr/bin/env python3
"""show.py <traces.jsonl> <trace id> [op index]: prints a trace (or one operation of it) for reading."""
import json, sys
path, tid = sys.argv[1], int(sys.argv[2])
only = int(sys.argv[3]) if len(sys.argv) > 3 else None
for line in open(path):
    t = json.loads(line)
    if t["id"] != tid:
        continue
    if "sim_panic" in t:
        print("simulator panic:", t["sim_panic"]); break
    for o in t["ops"]:
        if only is not None and o["i"] != only:
            continue
        extra = ""
        if o["gas_tgas"]: extra += f" gas={o['gas_tgas']}T"
        if o["faults"]: extra += f" faults={o['faults']}"
        print(f"op {o['i']} @h{o['h']} [{o['kind']}] {o['label']}{extra}")
        for s in t["steps"]:
            if s["op"] != o["i"]:
                continue
            res = ""
            if s["callback"]:
                res = " results=" + json.dumps([("FAILED" if not r.get("ok", False) else r.get("json", r.get("hex"))) for r in s["results"]])
            ret = s["ret"]
            rv = "" if ret is None else (json.dumps(ret.get("json")) if ret["kind"] == "value" else ret["kind"])
            mv = " moves=" + json.dumps(s["moves"]) if s["moves"] else ""
            flt = f" FAULT[{s['fault']}]" if s["fault"] else ""
            print(f"    h{s['h']} #{s['i']} {s['pred']} -> {s['recv']}::{s['method']} args={json.dumps(s['args'])[:160]} dep={s['deposit']}"
                  f" => {'ok ' + rv if s['ok'] else 'FAIL ' + s['status'][:90]}{res}{flt}{mv}")
    if only is None:
        print("final state:", json.dumps(t["obs"][-1]["state"]))
    break
