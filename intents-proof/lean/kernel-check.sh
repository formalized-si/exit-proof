#!/usr/bin/env bash
# Re-checks the compiled proofs outside the elaborator:
#   1. leanchecker --fresh replays every declaration of Intents, of IntentsW and of their imports in
#      the Lean kernel;
#   2. leanexport writes all declarations to .lake/intents.ndjson, and nanoda_bin, an independent kernel
#      written in Rust, checks them (configuration: nanoda.json).
# The three tools ship with the Lean toolchain pinned in lean-toolchain. Exit status 0 only if all checks
# pass. The export is several hundred MB; it is removed at the end unless KEEP_EXPORT=1.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
lake build Intents IntentsW > /dev/null
lake env leanchecker --fresh Intents
echo "leanchecker --fresh Intents: ok"
lake env leanchecker --fresh IntentsW
echo "leanchecker --fresh IntentsW: ok"
lake env leanexport Intents IntentsW > .lake/intents.ndjson
touch .lake/intents.pp.txt
lake env nanoda_bin nanoda.json | tee .lake/nanoda.log
grep -q "Checked [0-9]* declarations with no errors" .lake/nanoda.log
[ "${KEEP_EXPORT:-0}" = 1 ] || rm -f .lake/intents.ndjson
