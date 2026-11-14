#!/bin/bash
# Builds the harness binary (target/release/intents-gen).
set -euo pipefail
cd "$(dirname "$0")"
# libclang is needed at build time by nearcore's RocksDB bindings: set LIBCLANG_PATH if it is not installed
# system-wide (for example the `clang/native` directory of `python3 -m pip install libclang`).
source scripts/env.sh
# cargo decides what to rebuild by file times, and a tree copied with its times kept (rsync -a, tar) can look
# older than the last build: the hash of the sources of the last build is kept next to the binary, and a
# difference forces the rebuild. A check must never run a generator older than its source.
SRC_HASH=$(cat src/*.rs Cargo.toml Cargo.lock rust-toolchain.toml | sha256sum | cut -d" " -f1)
STAMP=$CARGO_TARGET_DIR/release/intents-gen.sources
[ "$(cat "$STAMP" 2> /dev/null)" = "$SRC_HASH" ] || touch src/main.rs
cargo build --release --locked 2>&1 | grep -E "^(error|warning: unused)|^\s+-->|Finished|^error" -A 12 | head -${LINES_MAX:-80}
[ -x "$CARGO_TARGET_DIR/release/intents-gen" ] && echo "$SRC_HASH" > "$STAMP"
