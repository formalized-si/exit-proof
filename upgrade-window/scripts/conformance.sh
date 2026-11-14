#!/usr/bin/env bash
# conformance.sh [<dir holding vault_v1.wasm vault_v2.wasm vault_v3.wasm>]
#
# Runs random traces of the example vault on near-contract-sim (the nearcore runtime), replays
# every receipt through the Lean model and compares (scripts/compare.py). Writes
# $OUT/conformance.json; exit status 0 iff the wasm and the model agree everywhere and no
# model-free monitor fired.
#
# Environment: TRACES (default 1000), SEED (default 20261112), JOBS (default 8),
#              OUT (default runs/conformance in this directory), KEEP=1 keeps the traces,
#              CARGO_TARGET_DIR and LIBCLANG_PATH as in scripts/env.sh,
#              UW_UNCHECKED=1: the wasm was built without overflow checks; compare with the
#              model of that build (lean/UpgradeWindow/Unchecked.lean).
set -euo pipefail
KIT=$(cd "$(dirname "$0")/.." && pwd)
source "$KIT/scripts/env.sh"
W=$(cd "${1:-$KIT/contract/out}" && pwd)
N=${TRACES:-1000}; SEED=${SEED:-20261112}; J=${JOBS:-8}
OUT=${OUT:-$KIT/runs/conformance}
G=$CARGO_TARGET_DIR/release/uw-gen
M=$KIT/lean/.lake/build/bin/uwmodel
[ -x "$G" ] || (cd "$KIT/harness" && cargo build --release --locked -q)
[ -x "$M" ] || (cd "$KIT/lean" && lake build uwmodel > /dev/null)
mkdir -p "$OUT"
T=$(mktemp -d "$OUT/work.XXXXXX")
trap '[ "${KEEP:-0}" = 1 ] || rm -rf "$T"' EXIT
PER=$(( (N + J - 1) / J ))
pids=()
for ((k = 0; k < J; k++)); do
  S=$((k * PER)); C=$(( N - S < PER ? N - S : PER ))
  if [ "$C" -gt 0 ]; then
    "$G" traces "$W/vault_v1.wasm" "$W/vault_v2.wasm" "$W/vault_v3.wasm" "$SEED" "$S" "$C" > "$T/sim_$k.jsonl" & pids+=($!)
  fi
done
for p in "${pids[@]}"; do wait "$p" || { echo "FAIL: the trace generator stopped with an error"; exit 1; }; done
cat "$T"/sim_*.jsonl > "$T/sim.jsonl"
FLAG=(); [ "${UW_UNCHECKED:-0}" = 1 ] && FLAG=(--unchecked)
"$M" ${FLAG[@]+"${FLAG[@]}"} < "$T/sim.jsonl" > "$T/model.jsonl"
# the result is written next to the traces first: $OUT/conformance.json is replaced only by a complete one
rm -f "$T/conformance.json"
python3 -I "$KIT/scripts/compare.py" "$T/sim.jsonl" "$T/model.jsonl" --json "$T/conformance.json" ${FLAG[@]+"${FLAG[@]}"} > /dev/null && RC=0 || RC=$?
[ -s "$T/conformance.json" ] || { echo "FAIL: no conformance result"; exit 1; }
python3 -I - "$T/conformance.json" "$W" "$N" "$SEED" <<'PY'
import hashlib, json, sys
p, w, n, seed = sys.argv[1:5]
r = json.load(open(p))
r["wasm_sha256"] = {f"vault_v{i}.wasm": hashlib.sha256(open(f"{w}/vault_v{i}.wasm", "rb").read()).hexdigest() for i in (1, 2, 3)}
r["requested_traces"], r["seed"] = int(n), int(seed)
json.dump(r, open(p, "w"), indent=1)
print(json.dumps({k: r[k] for k in ("ok", "traces", "receipts", "calls", "deploy_batches", "blocks", "diverging_traces", "monitor_violations")}))
PY
cp "$T/conformance.json" "$OUT/conformance.json"
exit $RC
