#!/bin/bash
# Builds the Intents contract from the commit its own `contract_source_metadata` names, with the command of the
# reproducible flow (cargo-near starts the pinned image itself and passes the build metadata the contract
# embeds), and compares the result with harness/wasm/intents.wasm. Needs git, docker, cargo-near 0.22.
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
export PATH="$HOME/.cargo/bin:$PATH"
C=16d04f6ec4401263f8914638710260da50bb46b0
R=${REBUILD_DIR:-$ROOT/runs/rebuild}; mkdir -p "$R"; cd "$R"
[ -d src/.git ] || git clone -q https://github.com/near/intents src
cd src && git fetch -q origin $C 2>/dev/null; git checkout -q -f $C && git clean -fdxq && echo "source commit $(git rev-parse HEAD)"
(cd contracts/defuse && cargo near build reproducible-wasm > "$R/build.log" 2>&1); echo "cargo-near exit status $?"
W=target/near/defuse/defuse.wasm
[ -f "$W" ] || { echo "RESULT: NO WASM"; tail -12 "$R/build.log"; exit 1; }
echo "rebuilt:  $(sha256sum $W | cut -d' ' -f1) $(stat -c %s $W) bytes"
echo "deployed: $(sha256sum "$ROOT/harness/wasm/intents.wasm" | cut -d' ' -f1) $(stat -c %s "$ROOT/harness/wasm/intents.wasm") bytes"
if cmp -s $W "$ROOT/harness/wasm/intents.wasm"; then echo "RESULT: BYTE-IDENTICAL"; else echo "RESULT: DIFFERENT"; exit 1; fi
