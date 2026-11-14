#!/usr/bin/env bash
# Is the replay sensitive to the two ledger functions of the wNEAR world?
# Each mutant changes one line of IntentsW/World.lean in a scratch copy of ../lean, rebuilds only
# the executable (Main importing IntentsW.World, so the proofs are not needed) and replays a trace
# file. A mutant is "caught" when the replay reports at least one disagreement.
#
# usage: replay_mutants.sh <traces.jsonl | traces.jsonl.gz>
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
traces="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
export PATH="$HOME/.elan/bin:$PATH"
work="$here/../mut"
rm -rf "$work"
cp -r "$here/../lean" "$work"
cd "$work"
sed -i 's/^import IntentsW$/import IntentsW.World/' Main.lean
cp IntentsW/World.lean World.orig

feed() { case "$traces" in *.gz) gzip -dc "$traces";; *) cat "$traces";; esac; }

run() {  # name, sed expression
  cp World.orig IntentsW/World.lean
  [ -z "$2" ] || sed -i "$2" IntentsW/World.lean
  if cmp -s World.orig IntentsW/World.lean && [ -n "$2" ]; then echo "$1: THE EDIT DID NOT APPLY"; return 1; fi
  lake build intentsmodel > build.log 2>&1 || { echo "$1: BUILD FAILED"; tail -5 build.log; return 1; }
  line="$(feed | ./.lake/build/bin/intentsmodel --summary | tail -1 || true)"
  echo "$1: $line"
}

run "unchanged" ""
run "M1 unwrap debits one unit more" \
  's/x ≤ U128_MAX then debit L owner x false else none/x ≤ U128_MAX then debit L owner (x + 1) false else none/'
run "M2 storage deposit of a wNEAR withdrawal not debited" \
  's/| some d => if d ≤ U128_MAX then debit L1 w.owner d via.forced else none/| some d => if d ≤ U128_MAX then some L1 else none/'
run "M3 unwrap ignores the pause of intents" \
  's/if L.ctl.isPaused "intents" = false ∧ x ≤ U128_MAX then debit L owner x false else none/if x ≤ U128_MAX then debit L owner x false else none/'
run "M4 unwrap ignores the account lock" \
  's/x ≤ U128_MAX then debit L owner x false else none/x ≤ U128_MAX then debit L owner x true else none/'
cd "$here"
rm -rf "$work"
