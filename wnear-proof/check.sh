#!/usr/bin/env bash
# wrap.near exit proof: rebuild and re-check everything, from this directory alone.
#   ./check.sh          proofs + axioms + non-vacuity example + deterministic checks on the deployed
#                       wasm + 2000-trace conformance against the Lean model
#   ./check.sh --all    also the 8 model mutants, the pre-upgrade code's invariant run, and the
#                       read-only mainnet RPC check (needs network)
# Exit status: 0 only if the proofs build without sorry, the axioms are among propext,
# Classical.choice, Quot.sound, the deterministic checks hold and the conformance verdict is EXACT
# (with --all: also every mutant is caught, the old code shows 0 violations, and the mainnet
# solvency hypothesis holds). Anything else exits non-zero.
#
# Environment (all optional):
#   WNEAR_WASM        the deployed wasm (default: wasm/w_near.wasm; its code hash is checked)
#   OLD_WASM          the pre-upgrade wasm (default: evidence/old_9kQaNisc.wasm)
#   OUT_DIR           directory for traces and other bulky output (default: out)
#   CARGO_TARGET_DIR  cargo target directory of the harness (default: harness/target)
#   JOBS              cargo build jobs (default 8);  LIBCLANG_PATH: see scripts/env.sh
# Needs: elan (Lean 4.35.0 from lean/lean-toolchain), rustup/cargo (Rust 1.95.0 from
# harness/rust-toolchain.toml), a C/C++ toolchain with cmake and libclang, python3, git.
set -euo pipefail
cd "$(dirname "$0")"
source scripts/env.sh
W="${WNEAR_WASM:-wasm/w_near.wasm}"
OLD="${OLD_WASM:-evidence/old_9kQaNisc.wasm}"
OUT="${OUT_DIR:-out}"
JOBS="${JOBS:-8}"
G="$CARGO_TARGET_DIR/release/wnear-gen"
mkdir -p "$OUT" evidence
[ -f "$W" ] || { echo "FAIL: $W not found (run ./fetch-wasm.sh)"; exit 1; }

echo "== 1. Lean: build (model, proofs, non-vacuity example), no sorry, axioms"
if ! (cd lean && lake build) > "$OUT/lean-build.log" 2>&1; then
  tail -30 "$OUT/lean-build.log"; echo "FAIL: lake build"; exit 1
fi
tail -1 "$OUT/lean-build.log"
if grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide' lean/WNear/*.lean lean/WNear.lean lean/Main.lean; then
  echo "FAIL: sorry/axiom found"; exit 1
fi
if grep -nE '^axiom ' lean/Review/*.lean; then echo "FAIL: axiom declared"; exit 1; fi
(cd lean && lake env lean Axioms.lean) > "$OUT/axioms.txt"
cp "$OUT/axioms.txt" evidence/axioms.txt; cat evidence/axioms.txt
python3 -I - evidence/axioms.txt <<'PY'
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

echo "== 2. harness build, deployed wasm hash, deterministic checks"
(cd harness && cargo build --release --locked -j "$JOBS" 2>&1 | tail -1)
"$G" checks "$W" > "$OUT/checks.json"   # evidence/checks.json is replaced only by a complete result
cp "$OUT/checks.json" evidence/checks.json
python3 -I - evidence/checks.json <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
print("code hash:", r["wasm_sha256_base58"], "| foreign resolve (user):", r["resolve_by_user"],
      "| as callback:", r["resolve_as_foreign_callback"]["status"], "| re-init:", r["new_again"])
private = "Method ft_resolve_transfer is private"
before, after = r["bob_balance_before_after_attack"]
ok = (r["wasm_sha256_base58"] == r["sim_code_hash"] == "DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1"
      and private in r["resolve_by_user"] and private in r["resolve_by_contract"]
      and private in r["resolve_as_foreign_callback"]["status"] and before == after
      and "already been initialized" in r["new_again"]
      and r["exit_withdraw"]["ok"] and r["exit_unregister"]["ok"])
print("deterministic checks:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
PY

echo "== 3. conformance: 2000 random traces on the deployed wasm vs the Lean model"
pids=()
for k in 0 1 2 3; do "$G" traces "$W" 20261111 $((k*500)) 500 > "$OUT/sim_part$k.jsonl" & pids+=($!); done
for p in "${pids[@]}"; do wait "$p" || { echo "FAIL: trace generator"; exit 1; }; done
cat "$OUT"/sim_part{0,1,2,3}.jsonl > "$OUT/sim.jsonl" && rm "$OUT"/sim_part*.jsonl
lean/.lake/build/bin/wnearmodel < "$OUT/sim.jsonl" > "$OUT/model.jsonl"
RC=0
python3 -I scripts/compare.py "$OUT/sim.jsonl" "$OUT/model.jsonl" --json evidence/conformance.json > /dev/null || RC=$?
python3 -I -c 'import json; r=json.load(open("evidence/conformance.json")); print(r["verdict"], r["counts"], "mismatches:", r["mismatches"])'
if [ "$RC" -ne 0 ]; then echo "RESULT: NOT EXACT (see evidence/conformance.json)"; exit 1; fi

if [ "${1:-}" = "--all" ]; then
  echo "== 4. mutants (each must MISMATCH)"
  OUT_DIR="$OUT" bash scripts/mutants.sh 400 | tee evidence/mutants.txt
  if [ "$(grep -c ': conformance MISMATCH ' evidence/mutants.txt)" -ne 8 ] || [ "$(wc -l < evidence/mutants.txt)" -ne 8 ]; then
    echo "FAIL: not every mutant was caught"; exit 1
  fi
  echo "== 5. pre-upgrade code 9kQaNisc: invariant after every block, 1000 traces"
  pids=()
  for k in 1 2 3 4; do "$G" oldinv "$OLD" $((7000+k)) 250 > "$OUT/old_$k.json" & pids+=($!); done
  for p in "${pids[@]}"; do wait "$p" || { echo "FAIL: old-code run"; exit 1; }; done
  python3 -I - "$OUT" evidence/old_code_invariant.json <<'PY'
import json, sys
t = [json.load(open(f"{sys.argv[1]}/old_{k}.json")) for k in (1, 2, 3, 4)]
calls = {}
for x in t:
    for m, n in x["calls"].items():
        c = calls.setdefault(m, [0, 0])
        c[0] += x["succeeded"].get(m, 0)
        c[1] += n
res = {"traces": sum(x["traces"] for x in t), "blocks_checked": sum(x["blocks_checked"] for x in t),
       "violations": sum(x["violations"] for x in t), "code": t[0]["code"],
       "calls_ok_of_total": dict(sorted(calls.items()))}
json.dump(res, open(sys.argv[2], "w"), indent=1)
print("traces", res["traces"], "blocks", res["blocks_checked"], "violations", res["violations"])
sys.exit(0 if res["violations"] == 0 and res["traces"] == 1000 else 1)
PY
  echo "== 6. mainnet (read-only RPC; the snapshot the report quotes stays in evidence/mainnet_check.json)"
  python3 -I scripts/mainnet_check.py "$W" | tee "$OUT/mainnet_check.json"
  python3 -I -c '
import json, sys
r = json.load(open(sys.argv[1]))
ok = (r["hypothesis_supply_plus_2stake_le_amount"] and r["access_keys"] == 0
      and r["code_hash"] == "DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1")
print("mainnet check at block", r["block_height"], ":", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)' "$OUT/mainnet_check.json"
fi
echo "RESULT: EXACT"
