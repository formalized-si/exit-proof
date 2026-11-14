#!/usr/bin/env bash
# proofs/check.sh
# Re-checks the proofs behind the properties (optional; ../check.sh does not need it):
#   1. builds the Lean sources of lean/ (Lean 4.35.0 from lean/lean-toolchain, no dependencies)
#      in a copy under $TOKEN_MONITORS_BUILD/proofs (default ../build/proofs), so that nothing is
#      built inside the kit;
#   2. refuses `sorry`, `admit`, `native_decide` and new axioms in the sources;
#   3. prints the axioms of the 16 theorems and requires them to be among propext,
#      Classical.choice, Quot.sound;
#   4. checks that the statements quoted in properties.json are the statements in the sources.
# Needs elan (https://github.com/leanprover/elan). Exit status: 0 only if all four hold.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/../scripts/env.sh"
command -v lake > /dev/null 2>&1 || PATH="$HOME/.elan/bin:$PATH"
WORK="$TOKEN_MONITORS_BUILD/proofs"
rm -rf "$WORK"
mkdir -p "$WORK"
cp -r "$HERE/lean" "$WORK/lean"
(cd "$WORK/lean" && lake build) | tail -1
if grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide' "$HERE"/lean/ProvedFT/*.lean "$HERE/lean/ProvedFT.lean"; then
  echo "FAIL: sorry, admit, native_decide or an axiom in the sources"; exit 1
fi
(cd "$WORK/lean" && lake env lean Axioms.lean) | tee "$WORK/axioms.txt"
python3 -I -B - "$WORK/axioms.txt" <<'PY'
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = [l.strip() for l in open(sys.argv[1]) if l.strip()]
bad = []
for l in lines:
    m = re.fullmatch(r"'(\S+)' depends on axioms: \[(.*)\]", l)
    if m:
        extra = {a.strip() for a in m.group(2).split(",")} - allowed
        if extra:
            bad.append(f"{m.group(1)}: {sorted(extra)}")
    elif not re.fullmatch(r"'\S+' does not depend on any axioms", l):
        bad.append("unexpected line: " + l)
if bad or len(lines) != 16:
    print("FAIL: axioms", bad, len(lines)); sys.exit(1)
print(f"axioms: {len(lines)} theorems, all within {sorted(allowed)}")
PY
python3 -I -B "$HERE/properties.py" check "$HERE/lean" "$HERE/properties.json"
echo "PROOFS: OK"
