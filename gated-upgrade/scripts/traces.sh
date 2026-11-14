#!/usr/bin/env bash
# Random traces with the monitor (harness/src/main.rs, `gu-test traces`), in parallel.
#   traces.sh [<dir with gated_vault_v{1,2,3}.wasm and exitproof_registry.wasm>]   default: contract/out
# Environment: TRACES (default 2000), SEED (default 20261113), JOBS (default 8), OUT (default runs/traces).
# Writes $OUT/traces.json (the merged summary). Exit status 0 only if no violation was reported.
set -euo pipefail
KIT=$(cd "$(dirname "$0")/.." && pwd)
source "$KIT/scripts/env.sh"
W=${1:-$KIT/contract/out}
TRACES=${TRACES:-2000}; SEED=${SEED:-20261113}; JOBS=${JOBS:-8}; OUT=${OUT:-$KIT/runs/traces}
GU="$CARGO_TARGET_DIR/release/gu-test"
mkdir -p "$OUT"; rm -f "$OUT"/part-*.json "$OUT/traces.json"
PER=$(( (TRACES + JOBS - 1) / JOBS ))
pids=()
for j in $(seq 0 $((JOBS - 1))); do
  start=$((j * PER)); n=$PER
  [ $((start + n)) -le "$TRACES" ] || n=$((TRACES - start))
  [ "$n" -gt 0 ] || continue
  "$GU" traces "$W/gated_vault_v1.wasm" "$W/gated_vault_v2.wasm" "$W/gated_vault_v3.wasm" "$W/exitproof_registry.wasm" \
    "$SEED" "$start" "$n" > "$OUT/part-$j.json" 2> "$OUT/part-$j.err" &
  pids+=($!)
done
rc=0
for p in "${pids[@]}"; do wait "$p" || rc=1; done
python3 -I - "$OUT" "$TRACES" <<'PY' || rc=1
import glob, json, sys
out, want = sys.argv[1], int(sys.argv[2])
tot = {"seed": None, "traces": 0, "blocks": 0, "receipts": 0, "violations": 0, "violation_samples": [], "counts": {}}
for p in sorted(glob.glob(out + "/part-*.json")):
    try:
        j = json.load(open(p))
    except ValueError:
        print("no result in", p); sys.exit(1)
    tot["seed"] = j["seed"]
    for k in ("traces", "blocks", "receipts", "violations"):
        tot[k] += j[k]
    tot["violation_samples"] += j["violation_samples"]
    for k, v in j["counts"].items():
        tot["counts"][k] = tot["counts"].get(k, 0) + v
tot["violation_samples"] = tot["violation_samples"][:20]
tot["counts"] = dict(sorted(tot["counts"].items()))
json.dump(tot, open(out + "/traces.json", "w"), indent=1)
c = tot["counts"]
print(f"{tot['traces']} traces, {tot['receipts']} receipts, {tot['blocks']} blocks: {tot['violations']} violations; "
      f"{c.get('code hash changes', 0)} code changes, {c.get('callback: deployment started', 0)} deployments started, "
      f"{sum(v for k, v in c.items() if k.startswith('callback refused'))} callbacks refused, "
      f"{c.get('direct up_deploy_code refused', 0)} direct deploy calls refused")
sys.exit(0 if tot["traces"] == want and tot["violations"] == 0 else 1)
PY
exit $rc
