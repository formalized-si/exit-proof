#!/usr/bin/env bash
# Ties the example token in this directory to its public source and verifies the committed wasm.
#   ./fetch-wasm.sh            check the committed wasm against the pinned hash, download the
#                              example's source from github.com/near/near-sdk-rs at the pinned
#                              commit (tag near-sdk-v5.29.0) and compare it with token/example-ft
#   ./fetch-wasm.sh --verify   offline: only check the hash of the committed wasm
# The wasm itself is re-derived by building token/example-ft with cargo-near: ./check.sh, step 3.
# Exit status is non-zero on any mismatch. Needs git and sha256sum.
set -euo pipefail
cd "$(dirname "$0")"
REPO=https://github.com/near/near-sdk-rs
COMMIT=1aac824cc543b2f201831f888c85396529716742   # tag near-sdk-v5.29.0
SRC=examples/fungible-token/ft/src/lib.rs
DST=token/example-ft/src/lib.rs
WASM=token/out/fungible_token.wasm

PINNED=$(cut -d' ' -f1 token/EXAMPLE_WASM_SHA256)
GOT=$(sha256sum "$WASM" | cut -d' ' -f1)
if [ "$GOT" != "$PINNED" ]; then echo "FAIL: $WASM has sha256 $GOT, pinned $PINNED"; exit 1; fi
echo "ok: $WASM: sha256 $PINNED (token/EXAMPLE_WASM_SHA256)"
if [ "${1:-}" = "--verify" ]; then exit 0; fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
git -C "$tmp" init -q
git -C "$tmp" fetch -q --depth 1 "$REPO" "$COMMIT"
git -C "$tmp" cat-file blob "FETCH_HEAD:$SRC" > "$tmp/lib.rs"
cmp "$tmp/lib.rs" "$DST" || { echo "FAIL: $DST differs from the upstream example"; exit 1; }
echo "ok: $DST is byte-identical to $SRC"
echo "    source: $REPO commit $COMMIT"
