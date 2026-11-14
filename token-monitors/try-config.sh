#!/usr/bin/env bash
# try-config.sh <token.wasm> <config.json>
# Validates the config, deploys the wasm in the simulator, makes the init and setup calls and
# prints what happened: every call with its failure text, the supply, who holds tokens, who will
# hand them out. Use it while writing a config; it runs no trace and writes no certificate.
# Exit status: 0 the token is set up and certify.sh can run, 2 the set-up failed, 3 invalid input.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ $# -eq 2 ] && [ -f "$1" ] && [ -f "$2" ] || { sed -n '2,6p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 3; }
source "$ROOT/scripts/env.sh"
python3 -I -B "$ROOT/scripts/check_config.py" "$2" > /dev/null || exit 3
"$ROOT/scripts/build.sh" || exit 3
W=$(mktemp -d "${TMPDIR:-/tmp}/token-monitors.XXXXXX")
trap 'rm -rf "$W"' EXIT
if ! "$FTMON" try "$1" "$2" > "$W/setup.json" 2> "$W/try.err"; then
  echo "the trace generator stopped while setting the token up:" >&2; tail -5 "$W/try.err" >&2; exit 3
fi
python3 -I -B "$ROOT/scripts/show_setup.py" "$W/setup.json"
