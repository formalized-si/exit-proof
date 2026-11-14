#!/usr/bin/env bash
# Sensitivity of the pool replay: does the comparison of pool-proof/ notice a model that is wrong by one line?
#   pool-mutants/run.sh [WORK_DIR]
# 1. copies pool-proof/ to WORK_DIR (default: a new temporary directory); pool-proof/ itself is not touched, so its
#    bundle hash, which the registry pins, stays the same;
# 2. runs ./check.sh there: the 1149 traces of the exact staking pool wasm and the unchanged model, RESULT EXACT;
# 3. for each line of mutants.txt (id|what|old line|new line) puts the change into the model, builds the executable
#    model alone (the proofs would fail, which is the point of a wrong model), replays the same traces and compares;
# 4. writes WORK_DIR/results.txt and WORK_DIR/res-<id>.json.
# A mutant is noticed when at least one trace differs from the model. Needs what pool-proof/check.sh needs.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
W="${1:-$(mktemp -d)}"
mkdir -p "$W"
rm -rf "$W/pool-proof" && cp -a "$HERE/../pool-proof" "$W/pool-proof"
P="$W/pool-proof"
(cd "$P" && ./check.sh) > "$W/check.log" 2>&1 || { tail -20 "$W/check.log"; echo "FAIL: pool-proof/check.sh"; exit 1; }
M="$W/model"
rm -rf "$M" && mkdir -p "$M" && cp -a "$P/lean/." "$M/" && rm -rf "$M/.lake"
python3 -I "$HERE/mkdefs.py" "$M/StakingPool/World.lean" "$M/StakingPool/WorldDefs.lean"
sed -i.bak 's/^import StakingPool.World$/import StakingPool.WorldDefs/' "$M/Main.lean"
cp "$M/StakingPool/Model.lean" "$W/Model.orig.lean"
res="$W/results.txt"; : > "$res"
run_one() { # id what
  (cd "$M" && lake build poolmodel > "$W/build-$1.log" 2>&1) || { echo "$1|BUILD-FAIL|$2" >> "$res"; return; }
  "$M/.lake/build/bin/poolmodel" < "$P/out/traces.jsonl" > "$W/model-$1.jsonl"
  rc=0; (cd "$P" && python3 -I scripts/compare.py out/traces.jsonl "$W/model-$1.jsonl" "$W/res-$1.json" > "$W/cmp-$1.txt") || rc=$?
  echo "$1|rc=$rc|$2|$(grep -m1 '^VERDICT' "$W/cmp-$1.txt")" >> "$res"
}
run_one P0 "control: the model unchanged"
while IFS='|' read -r id what old new; do
  [ -n "$id" ] || continue
  cp "$W/Model.orig.lean" "$M/StakingPool/Model.lean"
  python3 -I - "$M/StakingPool/Model.lean" "$old" "$new" <<'PY' || { echo "$id|PATCH-FAIL|$what" >> "$res"; continue; }
import sys
p, o, n = sys.argv[1:4]
s = open(p).read()
assert s.count(o) == 1, (o, s.count(o))
open(p, "w").write(s.replace(o, n))
PY
  run_one "$id" "$what"
done < "$HERE/mutants.txt"
cat "$res"
noticed=$(grep -c '^P[1-9].*VERDICT MISMATCH' "$res" || true)
total=$(grep -c . "$HERE/mutants.txt")
control=$(grep -c '^P0|rc=0|.*VERDICT EXACT' "$res" || true)
echo "control EXACT: $control; mutants noticed: $noticed of $total"
[ "$control" = 1 ] && [ "$noticed" = "$total" ]
