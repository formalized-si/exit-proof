#!/usr/bin/env bash
# certify.sh <token.wasm> <config.json> [--traces N] [--out certificate.json]
#            [--seed S] [--jobs J] [--keep-traces DIR]
#
# Deploys the wasm in a local simulator (near-contract-sim, nearcore runtime), sets the token up as
# the config says (CONFIG.md), runs N random multi-account traces (default 1000) and checks the
# model-free monitors (monitors/monitors.py) on what an outside observer sees. Writes a
# certificate (default: certificate.json in the current directory). Nothing is sent to any network.
#
# Exit status:
#   0  PASS          every monitor made checks and none was a violation
#   1  FAIL          a monitor found a violation (examples are in the certificate)
#   2  INCONCLUSIVE  no violation, but the token could not be set up, or a monitor made no check,
#                    or a kind of step the checks depend on never happened (reasons in the certificate)
#   3  the run did not happen: bad arguments, an invalid config, or the tools failed; no certificate
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
usage() { sed -n '2,16p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 3; }
WASM=""; CFG=""; N=1000; SEED=20261112; OUT="certificate.json"; KEEP=""; J=""
while [ $# -gt 0 ]; do
  case "$1" in
    --traces) N="${2:-}"; shift 2 || usage ;;
    --seed) SEED="${2:-}"; shift 2 || usage ;;
    --out) OUT="${2:-}"; shift 2 || usage ;;
    --jobs) J="${2:-}"; shift 2 || usage ;;
    --keep-traces) KEEP="${2:-}"; shift 2 || usage ;;
    -h|--help) usage ;;
    -*) echo "unknown option $1" >&2; usage ;;
    *) if [ -z "$WASM" ]; then WASM="$1"; elif [ -z "$CFG" ]; then CFG="$1"; else usage; fi; shift ;;
  esac
done
[ -n "$WASM" ] && [ -n "$CFG" ] && [ -n "$OUT" ] || usage
case "$N" in ''|*[!0-9]*|0) echo "--traces must be a positive integer" >&2; exit 3 ;; esac
case "$SEED" in ''|*[!0-9]*) echo "--seed must be a non-negative integer" >&2; exit 3 ;; esac
[ -f "$WASM" ] || { echo "no such file: $WASM" >&2; exit 3; }
[ -f "$CFG" ] || { echo "no such file: $CFG" >&2; exit 3; }
source "$ROOT/scripts/env.sh"
[ -n "$J" ] || J="$JOBS"
case "$J" in ''|*[!0-9]*|0) echo "--jobs must be a positive integer" >&2; exit 3 ;; esac
python3 -I -B "$ROOT/scripts/check_config.py" "$CFG" > /dev/null || exit 3
"$ROOT/scripts/build.sh" || exit 3
W=$(mktemp -d "${TMPDIR:-/tmp}/token-monitors.XXXXXX")
trap 'rm -rf "$W"' EXIT
if ! "$FTMON" try "$WASM" "$CFG" > "$W/setup.json" 2> "$W/try.err"; then
  echo "the trace generator stopped while setting the token up:" >&2; tail -5 "$W/try.err" >&2; exit 3
fi
MON=()
if python3 -I -B -c 'import json,sys; sys.exit(0 if json.load(open(sys.argv[1]))["ok"] else 1)' "$W/setup.json"; then
  PER=$(( (N + J - 1) / J ))
  pids=()
  for ((k = 0; k < J; k++)); do
    S=$((k * PER)); C=$(( N - S < PER ? N - S : PER ))
    if [ "$C" -gt 0 ]; then
      "$FTMON" run "$WASM" "$CFG" "$SEED" "$S" "$C" > "$W/t_$k.jsonl" 2> "$W/err_$k.txt" &
      pids+=($!)
    fi
  done
  bad=0
  for p in "${pids[@]}"; do wait "$p" || bad=1; done
  if [ "$bad" = 1 ]; then
    echo "the trace generator stopped with an error:" >&2; cat "$W"/err_*.txt | tail -5 >&2; exit 3
  fi
  rc=0
  python3 -I -B "$ROOT/monitors/monitors.py" "$W"/t_*.jsonl --json "$W/monitors.json" > "$W/monitors.brief" 2> "$W/monitors.err" || rc=$?
  if [ "$rc" -gt 2 ] || [ ! -s "$W/monitors.json" ]; then
    echo "the monitors stopped with an error:" >&2; tail -5 "$W/monitors.err" >&2; exit 3
  fi
  MON=(--monitors "$W/monitors.json")
  if [ -n "$KEEP" ]; then
    mkdir -p "$KEEP"; cp "$W"/t_*.jsonl "$W/setup.json" "$W/monitors.json" "$KEEP/"
  fi
fi
rc=0
python3 -I -B "$ROOT/scripts/certificate.py" --wasm "$WASM" --config "$CFG" --setup "$W/setup.json" "${MON[@]}" \
  --traces "$N" --seed "$SEED" --out "$OUT" || rc=$?
exit "$rc"
