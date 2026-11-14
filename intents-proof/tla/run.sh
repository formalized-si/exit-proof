#!/bin/bash
# Model-checks the three configurations with TLC (LARGE=1 adds the fourth). Needs java. TLC itself (tla2tools.jar of
# release v1.8.0) is downloaded into this directory when it is not there and checked against a pinned sha256;
# TLA_JAR points to another build. Exit status 0 only if the standard configuration has no violation and each of
# the two variants violates Backing.
set -uo pipefail
cd "$(dirname "$0")"
JAR=${TLA_JAR:-tla2tools.jar}; W=${WORKERS:-16}; mkdir -p out
URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
SHA=e1f11b75c4b5bc4478ba0ac5cb6ae28e40a01b0016bc33e0aa97da22dfdbcd7f
command -v java > /dev/null 2>&1 || { echo "FAIL: java is not installed (TLC needs Java 11 or newer)"; exit 1; }
if [ ! -f "$JAR" ]; then
  echo "TLC not found at $JAR: downloading $URL"
  curl -fsSL -o "$JAR.part" "$URL" && mv "$JAR.part" "$JAR" \
    || { rm -f "$JAR.part"; echo "FAIL: the download did not succeed; put tla2tools.jar into tla/ or set TLA_JAR"; exit 1; }
fi
if [ -z "${TLA_JAR:-}" ]; then
  echo "$SHA  $JAR" | sha256sum -c - > /dev/null 2>&1 \
    || { echo "FAIL: $JAR is not the TLC build these results were produced with (sha256 $SHA); remove it to download that build, or set TLA_JAR to use another one"; exit 1; }
fi
# $2 = number of workers: one worker makes TLC search breadth-first, so a counterexample is a shortest one
run() { java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC -deadlock -workers "${2:-$W}" -metadir "out/states-$1" -config "$1.cfg" IntentsLedger.tla > "out/$1.log" 2>&1; }
ok=0
run Standard
if grep -q "Model checking completed. No error has been found" out/Standard.log; then
  echo "Standard: no violation; $(grep -E "distinct states found" out/Standard.log | tail -1)"
else echo "Standard: FAILED"; grep -E "Error|violated" out/Standard.log | head -5; ok=1; fi
for v in FeeToken RefundFailedCall; do
  run $v 1
  if grep -q "Invariant Backing is violated" out/$v.log; then
    echo "$v: Backing violated, as expected; counterexample of $(grep -c "^State [0-9]*:" out/$v.log) states"
  else echo "$v: NO VIOLATION FOUND (expected one)"; ok=1; fi
done
if [ "${LARGE:-0}" = 1 ]; then   # the larger scope: about 79 million distinct states, minutes and tens of GB of memory
  run Large
  if grep -q "Model checking completed. No error has been found" out/Large.log; then
    echo "Large: no violation; $(grep -E "distinct states found" out/Large.log | tail -1)"
  else echo "Large: FAILED"; ok=1; fi
fi
rm -rf out/states-* IntentsLedger_TTrace_*
exit $ok
