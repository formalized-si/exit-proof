"""Print the aggregated contracts census as a table (weakest guard per capability)."""
import json
import sys

ORDER = ["single-key", "multi-key account", "contract", "unknown", "multisig", "dao"]
rows = json.load(open(sys.argv[1]))


def weakest(items):
    ws = [x["guard"]["weakest"] for x in items if x["guard"]["weakest"]]
    if not items:
        return "-"
    if not ws:
        return "guard?"
    return min(ws, key=ORDER.index)


for r in sorted(rows, key=lambda r: -r.get("near", 0)):
    if "error" in r:
        print(f"{r['account'][:44]:44s} ERROR {r['error'][:60]}")
        continue
    nc = r.get("no_code_change_path_found", r.get("immutable_code"))
    c = r["capabilities"]
    print(f"{r['account'][:44]:44s} {r['near']:>12,.0f} NEAR  code-path={'no ' if nc else 'YES'}  "
          f"code={weakest(c['code_change']):17s} funds={weakest(c['funds_control']):17s} "
          f"freeze={weakest(c['freeze']):17s} deploys={r.get('deployments', '?')} last={r.get('last_deploy', '')}")
