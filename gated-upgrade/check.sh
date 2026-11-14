#!/usr/bin/env bash
# Gated upgrades: rebuild and re-check everything, from this directory alone.
#   ./check.sh            proofs + axioms + the plugin model unchanged + contracts (committed wasm
#                         against the pinned hashes, rebuild from source when cargo-near is
#                         installed) + the scenarios on the wasm + random traces with the monitor
#   ./check.sh --mutants  also the mutant builds of the vault (control + 11 one-line changes);
#                         needs cargo-near
#   ./check.sh --testnet  also reads the testnet example back from the chain (read-only RPC) and
#                         compares it with testnet/tx.jsonl and the pinned hashes
# Exit status: 0 only if the proofs build without sorry, the axioms are among propext,
# Classical.choice, Quot.sound, the copied plugin model has the pinned hashes, the wasm files have
# the pinned hashes (and so does a rebuild, when one is made), every scenario check holds and the
# trace monitor reports no violation (with --mutants: also the control passes and every mutant is
# detected; with --testnet: also the chain shows what TESTNET.md says). Anything else exits non-zero.
#
# Environment (all optional): CARGO_TARGET_DIR, GU_CONTRACT_TARGET, LIBCLANG_PATH (scripts/env.sh);
# TRACES, SEED, JOBS (scripts/traces.sh).
# Needs: elan (Lean 4.35.0 from lean/lean-toolchain), rustup/cargo (Rust 1.95.0 for the harness,
# 1.86.0 for the vault: rust-toolchain.toml files), a C/C++ toolchain with cmake and libclang,
# python3; cargo-near 0.22 for the rebuild and the mutants.
set -euo pipefail
cd "$(dirname "$0")"
source scripts/env.sh
MUTANTS=0; TESTNET=0
for a in "$@"; do case "$a" in --mutants) MUTANTS=1;; --testnet) TESTNET=1;; *) echo "unknown option $a"; exit 2;; esac; done
mkdir -p evidence runs
echo "== 1. Lean: build, no sorry, axioms"
if ! (cd lean && lake build) > runs/lean-build.log 2>&1; then
  tail -30 runs/lean-build.log; echo "FAIL: lake build"; exit 1
fi
tail -1 runs/lean-build.log
if grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide' lean/UpgradeWindow/*.lean lean/UpgradeWindow.lean lean/GatedUpgrade/*.lean lean/GatedUpgrade.lean; then
  echo "FAIL: sorry/axiom found"; exit 1
fi
(cd lean && lake env lean Axioms.lean) > runs/axioms.txt
cp runs/axioms.txt evidence/axioms.txt
python3 -I - evidence/axioms.txt <<'PY'
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
need = {"GatedUpgrade.gated_code_change", "GatedUpgrade.gated_no_deploy_before", "GatedUpgrade.uncertified_never_installed",
        "GatedUpgrade.uncertified_never_current", "GatedUpgrade.aclInv_run", "GatedUpgrade.init_fresh"}
lines = [l.strip() for l in open(sys.argv[1]) if l.strip()]
bad, seen = [], set()
for l in lines:
    m = re.fullmatch(r"'(\S+)' depends on axioms: \[(.*)\]", l)
    if m:
        seen.add(m.group(1))
        extra = {a.strip() for a in m.group(2).split(",")} - allowed
        if extra:
            bad.append(f"{m.group(1)}: {sorted(extra)}")
    elif re.fullmatch(r"'(\S+)' does not depend on any axioms", l):
        seen.add(l.split("'")[1])
    else:
        bad.append("unexpected line: " + l)
if need - seen:
    bad.append(f"not listed: {sorted(need - seen)}")
if bad or not lines:
    print("FAIL: axioms", bad)
    sys.exit(1)
print(f"axioms: {len(lines)} theorems, all within {sorted(allowed)}")
PY
echo "== 2. the plugin model is the exit-window kit's, unchanged"
(cd lean && sha256sum -c UPGRADE_WINDOW_SHA256 > /dev/null) \
  || { echo "FAIL: lean/UpgradeWindow differs from the pinned hashes (lean/UPGRADE_WINDOW_SHA256)"; exit 1; }
echo "lean/UpgradeWindow*: $(wc -l < lean/UPGRADE_WINDOW_SHA256) files with the pinned hashes"
echo "== 3. contracts: gated vault (near-plugins v0.5.1, near-sdk 5.26.1, Rust 1.86.0), three versions; the registry"
O=contract/out
(cd $O && sha256sum -c ../WASM_SHA256 > /dev/null) \
  || { echo "FAIL: $O does not have the pinned hashes (contract/WASM_SHA256)"; exit 1; }
cat contract/WASM_SHA256
grep -q "^$(cat contract/REGISTRY_MAINNET_SHA256)  exitproof_registry.wasm$" contract/WASM_SHA256 \
  || { echo "FAIL: the registry build is not the wasm recorded for registry.exitproof.near (contract/REGISTRY_MAINNET_SHA256)"; exit 1; }
echo "the registry wasm is the one recorded for the mainnet registry (contract/REGISTRY_MAINNET_SHA256)"
(cd contract/registry && sha256sum -c ../REGISTRY_SOURCE_SHA256 > /dev/null) \
  || { echo "FAIL: contract/registry differs from the pinned source (contract/REGISTRY_SOURCE_SHA256)"; exit 1; }
if command -v cargo-near > /dev/null 2>&1; then
  # Rebuilds go to runs/ (the committed wasm files are never overwritten) and must give the same bytes.
  rm -rf runs/rebuild
  ./scripts/build-contract.sh runs/rebuild > runs/rebuild.log 2>&1 \
    || { tail -40 runs/rebuild.log; echo "FAIL: the rebuild from source did not finish (runs/rebuild.log)"; exit 1; }
  grep "^build-contract.sh:" runs/rebuild.log || true
  for f in runs/rebuild/*.wasm; do
    grep -q "^$(sha256sum "$f" | cut -d' ' -f1)  $(basename "$f")\$" contract/WASM_SHA256 \
      || { echo "FAIL: the rebuild of $(basename "$f") differs from the pinned build (contract/WASM_SHA256)"; exit 1; }
  done
  echo "rebuild from source with cargo-near: $(ls runs/rebuild/*.wasm | wc -l) of 4 builds made, same bytes as the pinned ones"
else
  echo "cargo-near not installed: the rebuild from source is skipped, the committed wasm files are used"
fi
echo "== 4. harness"
(cd harness && cargo build --release --locked -j "${JOBS:-8}" 2>&1 | tail -1)
GU="$CARGO_TARGET_DIR/release/gu-test"
echo "== 5. scenarios on the wasm (nearcore runtime)"
rm -f runs/scenarios.json
"$GU" scenarios $O/gated_vault_v1.wasm $O/gated_vault_v2.wasm $O/gated_vault_v3.wasm $O/exitproof_registry.wasm > runs/scenarios.json && SRC=0 || SRC=$?
python3 -I - runs/scenarios.json <<'PY' || { echo "FAIL: no complete scenario result"; exit 1; }
import json, sys
w = json.load(open(sys.argv[1]))
for s in w["scenarios"]:
    print(("ok  " if s["ok"] else "FAIL"), s["scenario"], "(%d checks)" % len(s["checks"]))
    for c in s["checks"]:
        if not c["holds"]:
            print("       does not hold:", c["check"])
print(f"{w['scenarios_total']} scenarios, {w['checks_total']} checks")
PY
cp runs/scenarios.json evidence/scenarios.json
python3 -I -c 'import json,sys; w=json.load(open(sys.argv[1])); sys.exit(0 if w["scenarios"] and all(s["ok"] for s in w["scenarios"]) else 1)' runs/scenarios.json \
  && [ "$SRC" = 0 ] || { echo "FAIL: a scenario check did not hold"; exit 1; }
echo "== 6. random traces with the monitor"
OUT=$PWD/runs/traces ./scripts/traces.sh $O && TRC=0 || TRC=$?
[ -s runs/traces/traces.json ] || { echo "FAIL: the trace run gave no result"; exit 1; }
cp runs/traces/traces.json evidence/traces.json
[ "$TRC" = 0 ] || { echo "FAIL: the monitor reported a violation (evidence/traces.json)"; exit 1; }
if [ "$MUTANTS" = 1 ]; then
  echo "== 7. mutants (each must be DETECTED; M0_control must PASS)"
  command -v cargo-near > /dev/null 2>&1 || { echo "FAIL: the mutant builds need cargo-near"; exit 1; }
  python3 -I -u scripts/mutants.py "$PWD" || { echo "RESULT: the mutant run is not as expected"; exit 1; }
fi
if [ "$TESTNET" = 1 ]; then
  echo "== 8. the testnet example, read back from the chain"
  python3 -I testnet/verify.py || { echo "FAIL: the chain does not show what TESTNET.md says"; exit 1; }
fi
echo "RESULT: PASS"
