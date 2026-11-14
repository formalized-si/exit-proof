#!/usr/bin/env bash
# fetch-code.sh <account> <out.wasm> [--sha256 HEX] [--rpc URL]
# Downloads the contract code of a NEAR mainnet account with one read-only RPC query (view_code)
# and prints its sha256 and NEAR code hash. Signs nothing, sends no transaction. Use it to certify
# the code that is actually deployed, or to compare a deployed code hash with a certificate.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ $# -ge 2 ] || { sed -n '2,5p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 3; }
exec python3 -I -B "$ROOT/scripts/fetch_code.py" "$@"
