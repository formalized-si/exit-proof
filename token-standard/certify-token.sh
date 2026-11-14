#!/bin/bash
# certify-token.sh <token.wasm> [<init_method> <init_args_json>]
#
# Deploys the token wasm on near-contract-sim, initializes it with its own #[init] call, runs
# random multi-account traces against the executable Lean model of near-contract-standards
# 5.29.0 and writes certificate.json (PASS/FAIL, properties, first divergence).
#
# The init arguments must give the initial supply to owner.near (one of the harness accounts).
# Default: new_default_meta '{"owner_id":"owner.near","total_supply":"1000000000000000000000000000000"}'
#
# Environment: TRACES (default 1000), SEED (default 20261112), JOBS (default 8),
#              OUT (output dir, default ./cert-<first 12 hex of the wasm sha256>), KEEP=1 keeps traces,
#              CARGO_TARGET_DIR and LIBCLANG_PATH as in scripts/env.sh.
# Exit status: 0 iff the certificate's result is PASS.
set -euo pipefail
KIT=$(cd "$(dirname "$0")" && pwd)
source "$KIT/scripts/env.sh"
if [ $# -lt 1 ]; then sed -n 2,13p "$0"; exit 2; fi
WASM=$(realpath "$1")
IM=${2:-new_default_meta}
IA=${3:-'{"owner_id":"owner.near","total_supply":"1000000000000000000000000000000"}'}
N=${TRACES:-1000}; SEED=${SEED:-20261112}; J=${JOBS:-8}
G=$CARGO_TARGET_DIR/release/ftcert-gen
M=$KIT/lean/.lake/build/bin/ftmodel
[ -x "$G" ] || (cd "$KIT/harness" && cargo build --release --locked -q)
[ -x "$M" ] || (cd "$KIT/lean" && lake build ftmodel > /dev/null)
SHA=$(sha256sum "$WASM" | cut -c1-12)
OUT=${OUT:-$PWD/cert-$SHA}
mkdir -p "$OUT"
W=$(mktemp -d "$OUT/work.XXXXXX")
trap '[ "${KEEP:-0}" = 1 ] || rm -rf "$W"' EXIT
"$G" probe "$WASM" "$IM" "$IA" > "$OUT/probe.json"
CONF=""
if python3 -I -c 'import json,sys; sys.exit(0 if json.load(open(sys.argv[1]))["ok"] else 1)' "$OUT/probe.json"; then
  PER=$(( (N + J - 1) / J ))
  pids=()
  for ((k = 0; k < J; k++)); do
    S=$((k * PER)); C=$(( N - S < PER ? N - S : PER ))
    if [ "$C" -gt 0 ]; then "$G" traces "$WASM" "$IM" "$IA" "$SEED" "$S" "$C" > "$W/sim_$k.jsonl" & pids+=($!); fi
  done
  for p in "${pids[@]}"; do wait "$p" || { echo "FAIL: the trace generator stopped with an error"; exit 1; }; done
  cat "$W"/sim_*.jsonl > "$W/sim.jsonl"
  "$M" < "$W/sim.jsonl" > "$W/model.jsonl"
  # a MISMATCH verdict is not an error here: it is recorded in conformance.json and cert.py turns it into FAIL
  python3 -I "$KIT/scripts/compare.py" "$W/sim.jsonl" "$W/model.jsonl" --json "$OUT/conformance.json" > /dev/null || true
  [ -s "$OUT/conformance.json" ] || { echo "FAIL: no conformance result"; exit 1; }
  CONF="$OUT/conformance.json"
fi
set +e
python3 -I "$KIT/scripts/cert.py" --wasm "$WASM" --init-method "$IM" --init-args "$IA" --traces "$N" --seed "$SEED" \
  --probe "$OUT/probe.json" --conformance "$CONF" --properties "$KIT/properties.json" --lean "$KIT/lean" \
  --out "$OUT/certificate.json"
RC=$?
set -e
exit $RC
