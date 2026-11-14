#!/bin/bash
# run.sh — the main run: random traces on the deployed wasm, the monitors, then the same
# generator on the mock token to show that the backing monitor can fire.
#
# Environment: TRACES (default 4000), MOCK_TRACES (default 400), SEED (default 20261112),
#              JOBS (default 16), OUT (default results), SAMPLE (default 12).
# Needs: the harness binary intents-gen (./build.sh), wasm/intents.wasm (./fetch-wasm.sh),
#        wasm/ft.wasm, wasm/w_near.wasm, wasm/mock_fee_token.wasm (./build-mock.sh).
set -euo pipefail
cd "$(dirname "$0")"
source scripts/env.sh
N=${TRACES:-4000}; M=${MOCK_TRACES:-400}; SEED=${SEED:-20261112}; J=${JOBS:-16}; OUT=${OUT:-results}; SAMPLE=${SAMPLE:-12}
G=$CARGO_TARGET_DIR/release/intents-gen   # scripts/env.sh: target/ here unless CARGO_TARGET_DIR is set
mkdir -p runs
W=$(mktemp -d runs/work.XXXXXX)
trap 'rm -rf "$W"' EXIT
mkdir -p "$OUT/sample" "$OUT/mock"
sha256sum wasm/intents.wasm wasm/ft.wasm wasm/w_near.wasm wasm/mock_fee_token.wasm > "$OUT/wasm.sha256"
$G probe wasm/intents.wasm wasm/ft.wasm wasm/w_near.wasm > "$OUT/probe.json"

gen() { # gen <count> <prefix> <ft wasm> [mock]
  local n=$1 pre=$2 ft=$3 mock=${4:-}
  local per=$(( (n + J - 1) / J )) pids=() k s c
  for ((k = 0; k < J; k++)); do
    s=$((k * per)); c=$(( n - s < per ? n - s : per ))
    if [ "$c" -gt 0 ]; then
      $G traces wasm/intents.wasm "$ft" wasm/w_near.wasm "$SEED" "$s" "$c" $mock > "$W/${pre}_$k.jsonl" & pids+=($!)
    fi
  done
  for p in "${pids[@]}"; do wait "$p" || { echo "FAIL: a generator process stopped with an error"; exit 1; }; done
}

date -u +"start %FT%TZ"
gen "$N" real wasm/ft.wasm
python3 -I scripts/monitor.py --out "$OUT/summary.json" --violations "$OUT/violations.jsonl" \
  --sample-dir "$OUT/sample" --sample "$SAMPLE" "$W"/real_*.jsonl > /dev/null
rm -f "$W"/real_*.jsonl
gen "$M" mock wasm/mock_fee_token.wasm mock
python3 -I scripts/monitor.py --out "$OUT/mock/summary.json" --violations "$OUT/mock/violations.jsonl" \
  --sample-dir "$OUT/mock" --keep-violating 2 "$W"/mock_*.jsonl > /dev/null
# the monitors themselves: every kind must fire on a doctored copy of a clean trace
$G traces wasm/intents.wasm wasm/ft.wasm wasm/w_near.wasm "$SEED" 0 80 > "$W/self.jsonl"
python3 -I scripts/selftest.py "$W/self.jsonl" > "$OUT/selftest.log" || { echo "FAIL: monitor self-test"; cat "$OUT/selftest.log"; exit 1; }
date -u +"end %FT%TZ"
python3 -I - "$OUT" "$SEED" <<'PY'
import json, sys
out, seed = sys.argv[1], sys.argv[2]
s = json.load(open(f"{out}/summary.json")); m = json.load(open(f"{out}/mock/summary.json"))
print(f"seed {seed}")
print(f"deployed wasm: {s['traces']} traces, {s['receipts']} receipts, violations {s['violations']}, harness {s['simulator_and_harness_failures']}")
print(f"mock token:    {m['traces']} traces, {m['receipts']} receipts, violations {m['violations']}, traces with violations {m['traces_with_violations']}")
print("monitor self-test:", open(f"{out}/selftest.log").read().strip().splitlines()[-1])
PY
