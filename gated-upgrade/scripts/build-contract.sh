#!/usr/bin/env bash
# Builds the contracts with cargo-near into <out-dir>:
#   gated_vault_v1.wasm, gated_vault_v2.wasm, gated_vault_v3.wasm   contract/gated-vault (v2 / v3
#                                         are feature builds that differ only in `version()`)
#   exitproof_registry.wasm               contract/registry (an unchanged copy of the registry source)
#   build-contract.sh [<out-dir>]         default out-dir: runs/rebuild
# The committed builds in contract/out are never written: this script refuses that directory.
# check.sh compares what is built here with contract/WASM_SHA256.
#
# Both crates are built with their committed Cargo.lock (--locked).
# The vault (Rust 1.86.0, contract/gated-vault/rust-toolchain.toml): rustc embeds the path of
# cargo's home in panic locations; it is mapped to /cargo with --remap-path-prefix so that the
# bytes do not depend on the home directory. "-C link-arg=-s" is cargo-near's own default.
# The registry is built as its own instructions say (`cargo near build non-reproducible-wasm`). The
# crate has no toolchain file, so the result depends on the compiler; the pinned hash was produced
# with rustc 1.99.1 and cargo-near 0.22.0 and is the hash of the registry deployed on mainnet as
# registry.exitproof.near. This script selects that compiler when it is installed and skips the
# registry otherwise.
set -euo pipefail
KIT=$(cd "$(dirname "$0")/.." && pwd)
source "$KIT/scripts/env.sh"
OUT=${1:-$KIT/runs/rebuild}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
[ "$OUT" != "$KIT/contract/out" ] || { echo "build-contract.sh: $OUT holds the committed builds; choose another output directory"; exit 2; }
HOME_HERE=$(cd "${CARGO_HOME:-$HOME/.cargo}" && pwd)
build() {  # <crate dir> <produced file> <output name> [cargo-near arguments]
  local crate=$1 produced=$2 name=$3; shift 3
  local T; T=$(mktemp -d "$OUT/build.XXXXXX")
  # the contracts keep their own release profile: no profile overrides from the caller's environment
  (cd "$crate" && env -u CARGO_PROFILE_RELEASE_LTO -u CARGO_PROFILE_DEV_DEBUG CARGO_TARGET_DIR="$GU_CONTRACT_TARGET" \
    cargo near build non-reproducible-wasm --locked --out-dir "$T" "$@" > "$T/log" 2>&1) \
    || { tail -40 "$T/log"; exit 1; }
  mv "$T/$produced" "$OUT/$name"
  rm -rf "$T"
}
VAULT_FLAGS=(--no-abi --env "RUSTFLAGS=-C link-arg=-s --remap-path-prefix=$HOME_HERE=/cargo")
# Compile the two contract crates anew every time (their dependencies stay cached). cargo keeps one
# fingerprint and one output file per crate name in a target directory, whatever directory the
# source is in: without this, a build of another copy of the crate made in the same target
# directory could be taken for a fresh build of this one.
rm -rf "$GU_CONTRACT_TARGET"/wasm32-unknown-unknown/release/.fingerprint/gated-vault-* \
       "$GU_CONTRACT_TARGET"/wasm32-unknown-unknown/release/.fingerprint/exitproof-registry-*
build "$KIT/contract/gated-vault" gated_vault.wasm gated_vault_v1.wasm "${VAULT_FLAGS[@]}"
build "$KIT/contract/gated-vault" gated_vault.wasm gated_vault_v2.wasm "${VAULT_FLAGS[@]}" --features v2
build "$KIT/contract/gated-vault" gated_vault.wasm gated_vault_v3.wasm "${VAULT_FLAGS[@]}" --features v3
# The registry crate has no toolchain file, so its bytes depend on the compiler: it is rebuilt only with the
# compiler that produced the pinned hash, and left out (with a message) when that compiler is not installed.
REG_RUSTC=1.99.1
REG_TC=""
# Only toolchains that are already installed are asked: asking rustup for a missing one would install it.
for tc in $(rustup toolchain list 2> /dev/null | cut -d' ' -f1); do
  [ "$(rustup run "$tc" rustc --version 2> /dev/null | cut -d' ' -f2)" = "$REG_RUSTC" ] || continue
  rustup target list --installed --toolchain "$tc" 2> /dev/null | grep -qx wasm32-unknown-unknown || continue
  REG_TC=$tc; break
done
if [ -n "$REG_TC" ]; then
  RUSTUP_TOOLCHAIN=$REG_TC build "$KIT/contract/registry" exitproof_registry.wasm exitproof_registry.wasm
else
  echo "build-contract.sh: no installed toolchain is rustc $REG_RUSTC with the wasm32-unknown-unknown target (rustup toolchain install $REG_RUSTC --target wasm32-unknown-unknown): the registry is not rebuilt" >&2
fi
(cd "$OUT" && sha256sum *.wasm)
