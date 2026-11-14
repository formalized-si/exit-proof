#!/usr/bin/env bash
# Builds the models and proofs (standard token: Intents; wNEAR: IntentsW), prints the axioms of
# every theorem, and replays the harness traces that are present
# (../harness/runs/*.jsonl of the original tree if this copy sits next to it, and ../runs/*.jsonl).
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
lake build 2>&1 | grep -E "error|sorry|Build completed" || true
lake env lean Axioms.lean | tee axioms.txt
if grep -q -v -E "depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]|does not depend on any axioms" axioms.txt; then
  echo "UNEXPECTED AXIOMS"; exit 1
fi
if grep -R -n -E "\bsorry\b|native_decide" Intents IntentsW WNear ProvedFT Main.lean Axioms.lean; then
  echo "FORBIDDEN TOKEN"; exit 1
fi
if grep -R -n -E "^\s*axiom\b" Intents IntentsW WNear ProvedFT Main.lean; then
  echo "AXIOM DECLARED"; exit 1
fi
status=0
for f in ../harness/runs/*.jsonl ../runs/*.jsonl ../runs/*.jsonl.gz; do
  case "$f" in *.viol.jsonl|*.summary.jsonl) continue;; esac
  [ -f "$f" ] || continue
  case "$f" in
    *.gz) line="$(gzip -dc "$f" | ./.lake/build/bin/intentsmodel --summary | tail -1)" || status=1;;
    *) line="$(./.lake/build/bin/intentsmodel --summary < "$f" | tail -1)" || status=1;;
  esac
  echo "replay $f: $line"
done
exit $status
