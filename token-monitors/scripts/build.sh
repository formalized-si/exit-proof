#!/usr/bin/env bash
# Builds the trace generator (harness/ -> $CARGO_TARGET_DIR/release/ftmon) unless it is already
# built from the current sources. The first build compiles the nearcore runtime and takes
# 5-20 minutes; later builds take seconds. Dependencies are pinned by harness/Cargo.lock.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/env.sh"
STAMP="$CARGO_TARGET_DIR/ftmon.sources.sha256"
CUR=$(cd "$ROOT/harness" && cat Cargo.toml Cargo.lock rust-toolchain.toml src/main.rs | sha256sum | cut -d' ' -f1)
if [ -x "$FTMON" ] && [ "$(cat "$STAMP" 2> /dev/null)" = "$CUR" ]; then
  exit 0
fi
echo "building the trace generator (the first build compiles the nearcore runtime: 5-20 minutes)" >&2
LOG="$TOKEN_MONITORS_BUILD/harness-build.log"
if ! (cd "$ROOT/harness" && cargo build --release --locked -j "$JOBS") > "$LOG" 2>&1; then
  tail -30 "$LOG" >&2
  echo "the trace generator did not build; the full log is $LOG" >&2
  exit 3
fi
tail -1 "$LOG" >&2
echo "$CUR" > "$STAMP"
