#!/usr/bin/env bash
# verify-certificate.sh <certificate.json> <token.wasm> [--rerun]
# Checks that a certificate belongs to this wasm and to this copy of the kit: the wasm hashes, the
# hash of the embedded config, the kit's bundle hash and the certificate's own result digest.
# With --rerun it also repeats the run (same config, traces and seed) and compares the result
# digest: the traces are deterministic, so an honest certificate is reproduced exactly.
# Exit status: 0 everything matches, 1 something does not, 3 invalid input.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ $# -ge 2 ] && [ -f "$1" ] && [ -f "$2" ] || { sed -n '2,7p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 3; }
exec python3 -I -B "$ROOT/scripts/verify_certificate.py" "$@"
