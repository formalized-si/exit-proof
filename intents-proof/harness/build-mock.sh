#!/bin/bash
# Builds the mock token used only to show that the backing monitor can fire (wasm/mock_fee_token.wasm).
# Source: mock-token/ (the near-sdk fungible-token example 5.29.0 with a fee on ft_transfer_call
# that the receiver is not told about). Needs cargo-near.
set -euo pipefail
cd "$(dirname "$0")"
command -v cargo > /dev/null 2>&1 || PATH="$HOME/.cargo/bin:$PATH"
export PATH
mkdir -p mock-token/out
(cd mock-token && CARGO_TARGET_DIR="${MOCK_TARGET_DIR:-$PWD/target}" \
  cargo near build non-reproducible-wasm --no-abi --out-dir out 2>&1 | grep -E "SHA-256|Size|error|warning: unused" || true)
[ -f mock-token/out/fungible_token.wasm ] || { echo "FAIL: the mock did not build"; exit 1; }
cp mock-token/out/fungible_token.wasm wasm/mock_fee_token.wasm
sha256sum wasm/mock_fee_token.wasm
