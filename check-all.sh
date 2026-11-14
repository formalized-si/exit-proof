#!/usr/bin/env bash
# One command for the whole repository.
#
#   ./check-all.sh            the fast part (minutes, Python 3 only, read-only RPC):
#                               tools/numbers_check.py   the numbers the documents quote, against the evidence files
#                               tools/selftest.py        attested hashes, stage rules, MCP server, live stages and
#                                                        token verdicts, registry pins
#   ./check-all.sh --proofs   also the check.sh of every proof directory (about 70 minutes on a machine with nothing
#                             built; needs Linux x86-64, elan, rustup, a C/C++ compiler, cmake, libclang, java):
#                               pool-proof  wnear-proof  token-standard  upgrade-window      in scratch copies
#                               intents-proof (--mutants --tla)  gated-upgrade  token-monitors   in place
#                             The four directories pinned by hash in the on-chain registry are checked in copies under
#                             runs/all/, because a check writes run logs into its directory.
#   ./check-all.sh --proofs --offline    the same without the parts that read the chain
#
# Environment: CARGO_TARGET_DIR (default runs/all/target, shared by all harness builds), JOBS, LIBCLANG_PATH — see
# the scripts/env.sh of each directory. ONLY="pool-proof intents-proof" restricts --proofs to the named directories.
# The token kit builds into runs/all/token-monitors-build (TOKEN_MONITORS_BUILD).
# Exit status 0 only if every part passed. The table printed at the end is saved to runs/all/summary.txt.
set -uo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT"
PROOFS=0; OFFLINE=0
for a in "$@"; do case "$a" in --proofs) PROOFS=1;; --offline) OFFLINE=1;; *) sed -n 2,19p "$0"; exit 2;; esac; done
W=$ROOT/runs/all
mkdir -p "$W"
: > "$W/summary.txt"
fail=0
part() {  # part <name> <log file> <command...>
  local name=$1 log=$2; shift 2
  local t0=$SECONDS
  "$@" > "$log" 2>&1
  local rc=$?
  printf '%-34s %-5s %5ss   %s\n' "$name" "$([ $rc = 0 ] && echo PASS || echo "FAIL")" "$((SECONDS - t0))" "$(tail -1 "$log" | cut -c1-90)" | tee -a "$W/summary.txt"
  [ $rc = 0 ] || fail=1
}
part "numbers in the documents" "$W/numbers.log" python3 tools/numbers_check.py
if [ $OFFLINE = 1 ]; then
  part "self-test (offline part)" "$W/selftest.log" python3 tools/selftest.py --offline
else
  part "self-test" "$W/selftest.log" python3 tools/selftest.py
fi
if [ $PROOFS = 1 ]; then
  mkdir -p "${CARGO_TARGET_DIR:-$W/target}"
  CARGO_TARGET_DIR=$(cd "${CARGO_TARGET_DIR:-$W/target}" && pwd); export CARGO_TARGET_DIR
  want() { [ -z "${ONLY:-}" ] || case " $ONLY " in *" $1 "*) return 0;; *) return 1;; esac; }
  for d in pool-proof wnear-proof token-standard upgrade-window; do
    want $d || continue
    rm -rf "$W/$d"
    # a copy without build products and earlier run output, as a fresh checkout has it
    tar -C "$ROOT" --exclude=target --exclude=.lake --exclude=runs --exclude=mutants --exclude=plugin -cf - "$d" | tar -C "$W" -xf -
    part "$d/check.sh (copy)" "$W/$d.log" "$W/$d/check.sh"
  done
  if want intents-proof; then
    part "intents-proof/check.sh --mutants --tla" "$W/intents-proof.log" intents-proof/check.sh --mutants --tla
  fi
  if want gated-upgrade; then
    if [ $OFFLINE = 1 ]; then part "gated-upgrade/check.sh" "$W/gated-upgrade.log" gated-upgrade/check.sh
    else part "gated-upgrade/check.sh --testnet" "$W/gated-upgrade.log" gated-upgrade/check.sh --testnet; fi
  fi
  if want token-monitors; then
    export TOKEN_MONITORS_BUILD=${TOKEN_MONITORS_BUILD:-$W/token-monitors-build}
    part "token-monitors/check.sh" "$W/token-monitors.log" token-monitors/check.sh
  fi
fi
echo "RESULT: $([ $fail = 0 ] && echo PASS || echo FAIL)   (logs in runs/all/)" | tee -a "$W/summary.txt"
exit $fail
