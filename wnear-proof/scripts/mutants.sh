#!/bin/bash
# Sensitivity check of the conformance comparison: each mutant changes one rule of the Lean
# model; replaying the same sim traces must then report MISMATCH.
# usage: scripts/mutants.sh [N_TRACES=300]   (after check.sh has written $OUT_DIR/sim.jsonl; GNU sed, bash 4)
set -u
cd "$(dirname "$0")/.."
source scripts/env.sh
N=${1:-300}
OUT="${OUT_DIR:-out}"
head -n "$N" "$OUT/sim.jsonl" > "$OUT/sim_mut.jsonl"
declare -A M
M[M1_refund_ignores_receiver_balance]='s/let refund := min (bal l r) (unusedOf amt res)/let refund := unusedOf amt res/'
M[M2_garbage_means_all_used]='s/  | .ok none => amt/  | .ok none => 0/'
M[M3_force_unregister_no_burn]='s/some ⟨⟨erase l p, sup - b, s.near⟩/some ⟨⟨erase l p, sup, s.near⟩/'
M[M4_withdraw_no_yocto_back]='s/some ⟨⟨l'"'"', sup'"'"', s.near⟩, \[(p, x + 1)\], \[\], none⟩/some ⟨⟨l'"'"', sup'"'"', s.near⟩, [(p, x)], [], none⟩/'
M[M5_deposit_keeps_storage_fee]='s/else match iDeposit (set l p 0) sup p (d - E.minBal) with/else match iDeposit (set l p 0) sup p d with/'
M[M6_resolve_not_private]='s/if p ≠ E.self then none   -- #\[private\]/if False then none --/'
M[M7_storage_refund_to_target]='s/(if 0 < d - E.minBal then \[(p, d - E.minBal)\] else \[\])/(if 0 < d - E.minBal then [(a, d - E.minBal)] else [])/'
M[M8_unregister_without_force]='s/if b = 0 ∨ force = some true then/if True then/'
for k in $(printf '%s\n' "${!M[@]}" | sort); do
  d=mutants/$k
  rm -rf "$d"; mkdir -p "$d"; cp -a lean/. "$d/"; rm -f "$d"/.lake/*.ndjson
  sed -i "${M[$k]}" "$d/WNear/Model.lean"
  if cmp -s lean/WNear/Model.lean "$d/WNear/Model.lean"; then echo "$k: PATCH DID NOT APPLY"; continue; fi
  if (cd "$d" && lake build WNear > proofs.log 2>&1); then pr="proofs still compile"; else pr="proofs BREAK ($(grep -o 'error: WNear/[A-Za-z]*.lean:[0-9]*' "$d/proofs.log" | head -1))"; fi
  (cd "$d" && lake build wnearmodel > build.log 2>&1) || { echo "$k: model build failed"; tail -5 "$d/build.log"; continue; }
  "$d/.lake/build/bin/wnearmodel" < "$OUT/sim_mut.jsonl" > "$d/model.jsonl"
  v=$(python3 -I scripts/compare.py "$OUT/sim_mut.jsonl" "$d/model.jsonl" | python3 -I -c 'import json,sys; r=json.load(sys.stdin); print(r["verdict"], r["mismatches"], (r["first_mismatches"][:1] or [""])[0])')
  echo "$k: conformance $v | $pr"
done
