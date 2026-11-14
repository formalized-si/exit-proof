#!/usr/bin/env bash
# Reproduces the pool-proof results in one command, from this directory alone:
#   ./check.sh [N_NORMAL=1000] [N_FAULTS=100] [N_OVERFLOW=50] [SEED=20261112]
# 1. builds the Lean model, the proofs and the non-vacuity example (no sorry; the axioms of the
#    theorems are written to out/axioms.txt and must be among propext, Classical.choice, Quot.sound),
# 2. builds the Rust harness against the public near-contract-sim (pinned in harness/Cargo.toml),
# 3. runs random traces of the deployed wasm (wasm/staking_pool.wasm, bytes hash-checked against
#    J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY) on the simulator,
# 4. runs the executable Lean model (poolmodel) on the same traces,
# 5. compares model vs simulator after every step (out/results.json), writes out/summary.json.
# Exit status: 0 only if the verdict is EXACT (every trace matches the model at every step, every
# error text matches, no environment check is violated). Anything else exits non-zero.
#
# Environment (all optional):
#   POOL_WASM         the staking-pool wasm (default: wasm/staking_pool.wasm)
#   OUT_DIR           output directory (default: out)
#   CARGO_TARGET_DIR  cargo target directory of the harness (default: harness/target)
#   THREADS           simulator threads (default 8);  JOBS: cargo build jobs (default 8)
#   LIBCLANG_PATH     see harness/env.sh
# Needs: elan (Lean 4.35.0 is fetched from lean/lean-toolchain), rustup/cargo (Rust 1.95.0 from
# harness/rust-toolchain.toml), a C/C++ toolchain with cmake and libclang, python3, git.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
N_NORMAL="${1:-1000}"
N_FAULTS="${2:-100}"
N_OVERFLOW="${3:-50}"
SEED="${4:-20261112}"
THREADS="${THREADS:-8}"
JOBS="${JOBS:-8}"
cd "$ROOT"
. harness/env.sh
WASM="${POOL_WASM:-wasm/staking_pool.wasm}"
OUT="${OUT_DIR:-out}"
mkdir -p "$OUT"
[ -f "$WASM" ] || { echo "FAIL: $WASM not found (run ./fetch-wasm.sh)"; exit 1; }

echo "== lean: build model + proofs + non-vacuity example"
t0=$(date +%s)
if ! (cd lean && lake build) > "$OUT/lean-build.log" 2>&1; then
  tail -30 "$OUT/lean-build.log"; echo "FAIL: lake build"; exit 1
fi
tail -1 "$OUT/lean-build.log"
if grep -rnwE 'sorry|admit|native_decide' lean/StakingPool lean/StakingPool.lean lean/Main.lean; then
  echo "FAIL: sorry/admit/native_decide found"; exit 1
fi
if grep -rnE '^axiom ' lean/StakingPool lean/Main.lean lean/Review; then echo "FAIL: axiom declared"; exit 1; fi
(cd lean && lake env lean scripts/Axioms.lean) > "$OUT/axioms.txt" 2>&1
cat "$OUT/axioms.txt"
python3 -I - "$OUT/axioms.txt" <<'PY'
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = [l.strip() for l in open(sys.argv[1]) if l.strip()]
bad = []
for l in lines:
    m = re.fullmatch(r"'(\S+)' depends on axioms: \[(.*)\]", l)
    if m:
        extra = {a.strip() for a in m.group(2).split(",")} - allowed
        if extra:
            bad.append(f"{m.group(1)}: {sorted(extra)}")
    elif not re.fullmatch(r"'\S+' does not depend on any axioms", l):
        bad.append("unexpected line: " + l)
if bad or not lines:
    print("FAIL: axioms", bad)
    sys.exit(1)
print(f"axioms: {len(lines)} theorems, all within {sorted(allowed)}")
PY
T_LEAN=$(( $(date +%s) - t0 ))

echo "== build harness"
(cd harness && nice cargo build --release --locked -j "$JOBS" 2>&1 | tail -1)
GEN="$CARGO_TARGET_DIR/release/gen"

echo "== sim: $N_NORMAL normal + $N_FAULTS faults + $N_OVERFLOW overflow traces (seed $SEED, $THREADS threads)"
t0=$(date +%s)
rm -f "$OUT/traces.jsonl.errors"
nice "$GEN" --wasm "$WASM" --traces "$N_NORMAL" --faults "$N_FAULTS" --overflow "$N_OVERFLOW" \
  --steps-min 30 --steps-max 80 --threads "$THREADS" --seed "$SEED" --out "$OUT/traces.jsonl" 2> "$OUT/gen.log.raw"
# keep the log free of machine-specific paths (panic locations inside cargo's git checkouts) and thread ids
sed -E -e 's#/[^ ]*/(near-contract-sim|nearcore)-[0-9a-f]+/[0-9a-f]+/#\1/#g' \
       -e "s#$ROOT/##g" -e 's#^(thread .<unnamed>.) \([0-9]+\)#\1#' "$OUT/gen.log.raw" > "$OUT/gen.log"
rm -f "$OUT/gen.log.raw"
head -1 "$OUT/gen.log"
tail -1 "$OUT/gen.log"
T_SIM=$(( $(date +%s) - t0 ))
# A trace that aborts inside the simulator is tolerated only in the overflow family, where the
# injected balance near u128::MAX overflows nearcore's own validator accounting.
python3 -I - "$OUT/traces.jsonl.errors" <<'PY'
import json, os, sys
errs = [json.loads(l) for l in open(sys.argv[1])] if os.path.exists(sys.argv[1]) else []
bad = [e for e in errs if not (e["family"] == "overflow" and "UnexpectedIntegerOverflow" in e["panic"])]
if errs:
    print(f"simulator aborted on {len(errs)} trace(s); {len(errs) - len(bad)} of them overflow-family "
          "(nearcore's own overflow on an injected balance), excluded from the comparison")
if bad:
    print("FAIL: unexpected simulator aborts:", json.dumps(bad)[:1000])
    sys.exit(1)
PY

echo "== lean model on the same traces"
t0=$(date +%s)
lean/.lake/build/bin/poolmodel < "$OUT/traces.jsonl" > "$OUT/model.jsonl"
T_MODEL=$(( $(date +%s) - t0 ))

echo "== compare"
RC=0
python3 -I scripts/compare.py "$OUT/traces.jsonl" "$OUT/model.jsonl" "$OUT/results.json" > "$OUT/compare.txt" || RC=$?
head -40 "$OUT/compare.txt"
python3 -I scripts/summary.py "$OUT/results.json" "$OUT/axioms.txt" "$OUT/gen.log" "$T_LEAN" "$T_SIM" "$T_MODEL" \
  "$N_NORMAL" "$N_FAULTS" "$N_OVERFLOW" "$SEED" > "$OUT/summary.json"
echo "== summary: $OUT/summary.json"
python3 -I -c 'import json,sys; s=json.load(open(sys.argv[1])); print(json.dumps({k: s[k] for k in ("verdict","problems","traces","calls","exact_traces","mismatch_traces","errtext_mismatch","env")}, indent=1))' "$OUT/summary.json"
if [ "$RC" -ne 0 ]; then echo "RESULT: NOT EXACT (see $OUT/results.json)"; exit 1; fi
echo "RESULT: EXACT"
