#!/usr/bin/env bash
# Exit window of the near-plugins `Upgradable` plugin: rebuild and re-check everything, from this
# directory alone.
#   ./check.sh            proofs + axioms + pinned plugin source + example vault (committed wasm
#                         against the pinned hashes, rebuild from source when cargo-near is
#                         installed) + witness scenarios on the wasm + conformance (1000 random
#                         traces), also for the build without overflow checks against its own model
#   ./check.sh --mutants  also the 13 mutant builds (M0 control + 12 one-line mutations of the
#                         plugin); needs cargo-near
# Exit status: 0 only if the proofs build without sorry, the axioms are among propext,
# Classical.choice, Quot.sound, the plugin source matches PLUGIN_PIN.json, the vault wasm files have
# the pinned hashes (and so does a rebuild, when one is made), every witness scenario holds and both
# conformance runs report no divergence and no monitor violation (with --mutants: also the control
# passes and every mutant is detected in the expected statement). Anything else exits non-zero.
#
# Environment (all optional):
#   CARGO_TARGET_DIR, UW_CONTRACT_TARGET, LIBCLANG_PATH   see scripts/env.sh
#   TRACES, SEED, JOBS                                    as in scripts/conformance.sh
# Needs: elan (Lean 4.35.0 from lean/lean-toolchain), rustup/cargo (Rust 1.95.0 for the harness,
# 1.86.0 for the vault: rust-toolchain.toml files), a C/C++ toolchain with cmake and libclang,
# python3, git; cargo-near 0.22 for the vault rebuild and the mutants.
set -euo pipefail
cd "$(dirname "$0")"
source scripts/env.sh
mkdir -p evidence runs
echo "== 1. Lean: build, no sorry, axioms"
if ! (cd lean && lake build) > runs/lean-build.log 2>&1; then
  tail -30 runs/lean-build.log; echo "FAIL: lake build"; exit 1
fi
tail -1 runs/lean-build.log
if grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide' lean/UpgradeWindow/*.lean lean/UpgradeWindow.lean lean/Main.lean; then
  echo "FAIL: sorry/axiom found"; exit 1
fi
(cd lean && lake env lean Axioms.lean) > runs/axioms.txt
cp runs/axioms.txt evidence/axioms.txt; cat evidence/axioms.txt
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
echo "== 2. pinned plugin source"
./scripts/fetch-plugin.sh
echo "== 3. example vault (near-plugins v0.5.1, near-sdk 5.26.1, Rust 1.86.0), three versions"
O=contract/out; U=contract/out-unchecked
(cd $O && sha256sum -c ../VAULT_WASM_SHA256 > /dev/null) \
  || { echo "FAIL: $O does not have the pinned hashes (contract/VAULT_WASM_SHA256)"; exit 1; }
(cd $U && sha256sum -c ../VAULT_UNCHECKED_WASM_SHA256 > /dev/null) \
  || { echo "FAIL: $U does not have the pinned hashes (contract/VAULT_UNCHECKED_WASM_SHA256)"; exit 1; }
(cd $O && sha256sum vault_v1.wasm vault_v2.wasm vault_v3.wasm) > runs/vault_wasm_sha256.txt
cp runs/vault_wasm_sha256.txt evidence/vault_wasm_sha256.txt; cat evidence/vault_wasm_sha256.txt
echo "the committed wasm files have the pinned hashes (contract/VAULT_WASM_SHA256, contract/VAULT_UNCHECKED_WASM_SHA256)"
if command -v cargo-near > /dev/null 2>&1; then
  # Rebuilds go to runs/ (the committed wasm files are never overwritten) and must give the same bytes.
  ./scripts/build-contract.sh contract/vault runs/rebuild > /dev/null
  (cd runs/rebuild && sha256sum -c ../../contract/VAULT_WASM_SHA256 > /dev/null) \
    || { echo "FAIL: the rebuild from source differs from the pinned builds (runs/rebuild)"; exit 1; }
  echo "rebuild from source with cargo-near: same bytes as the pinned builds"
  UW_OVERFLOW_CHECKS=0 ./scripts/build-contract.sh contract/vault runs/rebuild-unchecked > /dev/null
  (cd runs/rebuild-unchecked && sha256sum -c ../../contract/VAULT_UNCHECKED_WASM_SHA256 > /dev/null) \
    || { echo "FAIL: the rebuild without overflow checks differs from the pinned builds (runs/rebuild-unchecked)"; exit 1; }
  echo "   ... and without overflow checks (cargo's default release profile): same bytes as the pinned builds"
else
  echo "cargo-near not installed: the rebuild from source is skipped, the committed wasm files are used"
fi
echo "== 4. harness"
(cd harness && cargo build --release --locked -j "${JOBS:-8}" 2>&1 | tail -1)
echo "== 5. witness scenarios on the wasm"
rm -f runs/witness.json
"$CARGO_TARGET_DIR/release/uw-gen" witness $O/vault_v1.wasm $O/vault_v2.wasm $O/vault_v3.wasm \
  $U/vault_v1.wasm $U/vault_v2.wasm $U/vault_v3.wasm > runs/witness.json && WRC=0 || WRC=$?
python3 -I - runs/witness.json <<'PY' || { echo "FAIL: no complete witness result"; exit 1; }
import json, sys
w = json.load(open(sys.argv[1]))
for s in w["scenarios"]:
    print(("ok  " if s["ok"] else "FAIL"), s["scenario"], "(%d checks)" % len(s["checks"]))
PY
cp runs/witness.json evidence/witness.json
python3 -I -c 'import json,sys; w=json.load(open(sys.argv[1])); sys.exit(0 if w["scenarios"] and all(s["ok"] for s in w["scenarios"]) else 1)' runs/witness.json \
  && [ "$WRC" = 0 ] || { echo "FAIL: a witness scenario did not hold"; exit 1; }
echo "== 6. conformance: wasm on near-contract-sim against the Lean model"
rm -f runs/conformance/conformance.json runs/conformance-unchecked/conformance.json
OUT=$PWD/runs/conformance ./scripts/conformance.sh $O && CRC=0 || CRC=$?
[ -s runs/conformance/conformance.json ] || { echo "FAIL: the conformance run gave no result"; exit 1; }
cp runs/conformance/conformance.json evidence/conformance.json
[ "$CRC" = 0 ] || { echo "FAIL: the wasm and the model disagree (evidence/conformance.json)"; exit 1; }
echo "   ... the build without overflow checks against the model of that build"
UW_UNCHECKED=1 OUT=$PWD/runs/conformance-unchecked ./scripts/conformance.sh $U && URC=0 || URC=$?
[ -s runs/conformance-unchecked/conformance.json ] || { echo "FAIL: the conformance run gave no result"; exit 1; }
cp runs/conformance-unchecked/conformance.json evidence/conformance_unchecked.json
[ "$URC" = 0 ] || { echo "FAIL: the unchecked wasm and its model disagree (evidence/conformance_unchecked.json)"; exit 1; }
if [ "${1:-}" = "--mutants" ]; then
  echo "== 7. mutants (each must FAIL; M0_control must PASS)"
  command -v cargo-near > /dev/null 2>&1 || { echo "FAIL: the mutant builds need cargo-near"; exit 1; }
  python3 -I scripts/mutants.py "$PWD" || { echo "RESULT: the mutant run is not as expected"; exit 1; }
fi
echo "RESULT: PASS"
