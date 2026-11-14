#!/usr/bin/env bash
# Builds the example vault three times with cargo-near (v1, and the v2 / v3 feature builds that
# differ only in `version()`), into <out-dir>/vault_v{1,2,3}.wasm.
#   build-contract.sh [<crate-dir> [<out-dir>]]        default out-dir: runs/rebuild
# The committed builds in contract/out and contract/out-unchecked are never written: this script
# refuses those two directories. check.sh compares what is built here with the pinned hashes.
# Uses the committed Cargo.lock (--locked): the dependency versions of sweat-token@75dc5b48.
#
# rustc embeds the path of cargo's home in panic locations (the registry and the git checkout of
# the plugin). It is mapped to the cargo home of the pinned builds, read from the committed wasm
# itself, with --remap-path-prefix, so the bytes do not depend on where cargo keeps its sources.
# "-C link-arg=-s" is cargo-near's own default for RUSTFLAGS.
set -euo pipefail
KIT=$(cd "$(dirname "$0")/.." && pwd)
source "$KIT/scripts/env.sh"
CRATE=${1:-$KIT/contract/vault}
OUT=${2:-$KIT/runs/rebuild}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
case "$OUT" in
  "$KIT/contract/out"|"$KIT/contract/out-unchecked")
    echo "build-contract.sh: $OUT holds the committed builds; choose another output directory"; exit 2;;
esac
# UW_LOCKED=0: let cargo rewrite Cargo.lock (the mutant builds patch the plugin to a local path)
LOCKED=--locked; [ "${UW_LOCKED:-1}" = 1 ] || LOCKED=
# UW_OVERFLOW_CHECKS=0: build as cargo's default release profile does, without overflow checks
OC=(); [ "${UW_OVERFLOW_CHECKS:-1}" = 1 ] || OC=(CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=false)
HOME_HERE=$(cd "${CARGO_HOME:-$HOME/.cargo}" && pwd)
HOME_PINNED=$( (grep -a -o '/[A-Za-z0-9_./-]*/registry/src/' "$KIT/contract/out/vault_v1.wasm" || true) \
  | sort | uniq -c | sort -rn | awk 'NR == 1 { print $2 }' | sed 's#/registry/src/$##')
[ -n "$HOME_PINNED" ] || HOME_PINNED=$HOME_HERE
for v in 1 2 3; do
  F=(); [ "$v" = 1 ] || F=(--features "v$v")
  T=$(mktemp -d "$OUT/build.XXXXXX")
  # the contract keeps its own release profile: no profile overrides from the caller's environment
  (cd "$CRATE" && env -u CARGO_PROFILE_RELEASE_LTO -u CARGO_PROFILE_DEV_DEBUG CARGO_TARGET_DIR="$UW_CONTRACT_TARGET" ${OC[@]+"${OC[@]}"} \
    cargo near build non-reproducible-wasm $LOCKED --no-abi \
    --env "RUSTFLAGS=-C link-arg=-s --remap-path-prefix=$HOME_HERE=$HOME_PINNED" \
    --out-dir "$T" ${F[@]+"${F[@]}"} > "$T/log" 2>&1) \
    || { tail -40 "$T/log"; exit 1; }
  mv "$T/uw_vault.wasm" "$OUT/vault_v$v.wasm"
  rm -rf "$T"
done
(cd "$OUT" && sha256sum vault_v1.wasm vault_v2.wasm vault_v3.wasm)
