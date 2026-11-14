#!/usr/bin/env bash
# inspect.sh <token.wasm>
# Prints the sha256 and the NEAR code hash of a wasm file and the methods it exports: the standard
# ones (present / missing), the others, and the likely init methods. Runs nothing.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ $# -eq 1 ] && [ -f "$1" ] || { sed -n '2,4p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 3; }
exec python3 -I -B "$ROOT/scripts/inspect_wasm.py" "$1"
