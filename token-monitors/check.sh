#!/usr/bin/env bash
# check.sh [--traces N]
#
# Rebuilds what the kit needs and re-checks the kit itself:
#   1. builds the trace generator (harness/) and, with cargo-near, the reference token
#      (near-sdk-rs fungible-token example, near-contract-standards 5.29.0) and its mutants;
#   2. the reference token must get a PASS certificate;
#   3. every mutant marked FAIL in reference/mutants.json must fail with the monitors listed for
#      it; every mutant marked OUTSIDE must stay silent and is reported as outside the monitors
#      with the reason; the unmutated control must pass;
#   4. every example config of examples/examples.json must get a PASS certificate (the wasm of a
#      mainnet example is fetched with a read-only view_code query and checked against its sha256);
#   5. the guard cases of tests/guards must end INCONCLUSIVE or be refused, never PASS;
#   6. the configs of tests/setup, which together use every key of the config format, must be
#      set up (or refused) as expected;
#   7. the reference certificate must verify, and an altered copy of it must not.
# Results: $TOKEN_MONITORS_BUILD/check/summary.md and summary.json (default build/check/ here).
# Exit status: 0 only if all of that holds.
#
# Environment (optional): TOKEN_MONITORS_BUILD, CARGO_TARGET_DIR, TOKEN_TARGET_DIR, JOBS,
# LIBCLANG_PATH (scripts/env.sh), NEAR_RPC_URL. --traces N lowers the traces per run (default 1000).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
case "${1:-}" in -h|--help) sed -n '2,21p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;; esac
source "$ROOT/scripts/env.sh"
exec python3 -I -B "$ROOT/scripts/selfcheck.py" "$@"
