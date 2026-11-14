#!/usr/bin/env bash
# Proved Token Standard: rebuild and re-check everything, from this directory alone.
#   ./check.sh          proofs + axioms + properties.json + example token (pinned hash, rebuild from
#                       source when cargo-near is installed) + certificate (1000 traces)
#   ./check.sh --all    also the 11 mutant builds (M0 control + 10 one-line mutations), each
#                       certified (needs cargo-near and network: the library crate is downloaded)
# Exit status: 0 only if the proofs build without sorry, the axioms are among propext,
# Classical.choice, Quot.sound, properties.json matches the Lean sources, the example token's wasm
# has the pinned hash and its certificate is PASS (with --all: also M0 is PASS and every mutant is
# FAIL with the expected property). Anything else exits non-zero.
#
# Environment (all optional):
#   TOKEN_WASM        the example token's wasm (default: token/out/fungible_token.wasm)
#   CARGO_TARGET_DIR  cargo target directory (default: harness/target)
#   TRACES, SEED, JOBS  as in certify-token.sh;  LIBCLANG_PATH: see scripts/env.sh
# Needs: elan (Lean 4.35.0 from lean/lean-toolchain), rustup/cargo (Rust 1.95.0 for the harness,
# 1.93.0 for the token: rust-toolchain.toml files), a C/C++ toolchain with cmake and libclang,
# python3; cargo-near 0.22 for the token rebuild and the mutants.
set -euo pipefail
cd "$(dirname "$0")"
source scripts/env.sh
TOKEN="${TOKEN_WASM:-token/out/fungible_token.wasm}"
mkdir -p evidence runs
echo "== 1. Lean: build, no sorry, axioms"
if ! (cd lean && lake build) > runs/lean-build.log 2>&1; then
  tail -30 runs/lean-build.log; echo "FAIL: lake build"; exit 1
fi
tail -1 runs/lean-build.log
if grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide' lean/ProvedFT/*.lean lean/ProvedFT.lean lean/Main.lean; then
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
echo "== 2. properties.json matches the Lean sources"
python3 -I scripts/properties.py check lean properties.json
echo "== 3. example token (near-sdk-rs examples/fungible-token/ft, tag near-sdk-v5.29.0)"
PINNED=$(cut -d' ' -f1 token/EXAMPLE_WASM_SHA256)
sha256sum "$TOKEN" | tee evidence/example_wasm_sha256.txt
if [ "$(cut -d' ' -f1 evidence/example_wasm_sha256.txt)" != "$PINNED" ]; then
  echo "FAIL: $TOKEN does not have the pinned hash (token/EXAMPLE_WASM_SHA256)"; exit 1
fi
echo "the committed wasm has the pinned hash (token/EXAMPLE_WASM_SHA256)"
if command -v cargo-near > /dev/null 2>&1; then
  # Rebuild from source into runs/rebuild (the committed wasm is never overwritten). rustc embeds
  # the cargo registry path in panic locations, so this machine's registry path is mapped to the
  # one of the pinned build (read from the committed wasm itself) with --remap-path-prefix;
  # "-C link-arg=-s" is cargo-near's own default. The token gets its own target subdirectory.
  REG_HERE="${CARGO_HOME:-$HOME/.cargo}/registry/src"
  REG_PINNED=$(grep -a -o -m1 '/[A-Za-z0-9_./-]*/registry/src/' "$TOKEN" | head -1 | sed 's#/$##')
  touch token/example-ft/src/lib.rs
  (cd token/example-ft && CARGO_TARGET_DIR="$CARGO_TARGET_DIR/token-build" \
    cargo near build non-reproducible-wasm --no-abi \
    --env "RUSTFLAGS=-C link-arg=-s --remap-path-prefix=$REG_HERE=$REG_PINNED" \
    --out-dir ../../runs/rebuild 2>&1 | grep -E "SHA-256|Size" || true)
  [ -f runs/rebuild/fungible_token.wasm ] || { echo "FAIL: the token did not build"; exit 1; }
  if [ "$(sha256sum runs/rebuild/fungible_token.wasm | cut -d' ' -f1)" = "$PINNED" ]; then
    echo "rebuild from source: same bytes as the pinned build"
  else
    echo "FAIL: the rebuild from source differs from the pinned build (runs/rebuild/fungible_token.wasm)"; exit 1
  fi
else
  echo "cargo-near not installed: the rebuild from source is skipped, the committed wasm is used"
fi
echo "== 4. harness"
(cd harness && cargo build --release --locked -j "${JOBS:-8}" 2>&1 | tail -1)
echo "== 5. certify the example token"
OUT=runs/example ./certify-token.sh "$TOKEN" || { echo "RESULT: the example token's certificate is not PASS"; exit 1; }
cp runs/example/certificate.json evidence/certificate_example.json
cp runs/example/conformance.json evidence/conformance_example.json
cp runs/example/probe.json evidence/probe_example.json
if [ "${1:-}" = "--all" ]; then
  echo "== 6. mutants (each must FAIL; M0_control must PASS)"
  python3 -I scripts/mutants.py "$PWD" || { echo "RESULT: the mutant run is not as expected"; exit 1; }
fi
echo "RESULT: PASS"
