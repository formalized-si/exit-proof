#!/usr/bin/env bash
# Re-checks the compiled proofs outside the elaborator (the checks of the independent review):
#   1. leanchecker --fresh replays every declaration of StakingPool and of its imports in the Lean kernel;
#   2. leanexport writes all declarations to .lake/pool.ndjson, and nanoda_bin, an independent
#      kernel written in Rust, checks them (configuration: nanoda.json).
# The three tools ship with the Lean toolchain pinned in lean-toolchain. Needs about 400 MB of
# disk in .lake/ and a few minutes. Exit status: 0 only if both checks pass.
set -euo pipefail
cd "$(dirname "$0")"
lake build StakingPool
lake env leanchecker --fresh StakingPool
echo "leanchecker --fresh StakingPool: ok"
lake env leanexport StakingPool > .lake/pool.ndjson
touch .lake/pool.pp.txt          # nanoda_bin does not create its pretty-printer output file
lake env nanoda_bin nanoda.json | tee .lake/nanoda.log
grep -q "Checked [0-9]* declarations with no errors" .lake/nanoda.log
echo "the statements nanoda_bin checked are printed in .lake/pool.pp.txt"
