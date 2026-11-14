#!/bin/bash
# check.sh [--mutants] [--rebuild] [--tla]
#
# Re-checks everything this directory claims about the token ledger of the NEAR Intents contract:
#   1. the wasm files are the pinned ones (the Intents code is the one deployed as intents.near);
#   2. the Lean model and theorems build, without `sorry`, on the axioms propext, Quot.sound, Classical.choice;
#   3. the harness builds;
#   4. on random traces of the deployed wasm no backing monitor fires, and on the mock token it does;
#   5. every receipt of fresh traces, replayed through the Lean model, gives the same result as the wasm: receipt by
#      receipt through the ledger functions, and token and contract together through the step function of the world;
#   --mutants  6. every one-line change of the model is noticed by the replay, or listed with the reason why no
#                 receipt can tell it apart;
#   --rebuild  7. the commit named by the contract's own metadata builds to the deployed bytes (needs docker).
#   --tla      8. the TLA+ specification of the same ledger is model-checked by TLC (needs java; tla/run.sh downloads TLC).
# Environment: TRACES (default 1000), MOCK_TRACES (default 200), SEED (default 20261112), JOBS (default 16),
#              CARGO_TARGET_DIR, LIBCLANG_PATH (see harness/scripts/env.sh).
# Exit status 0 only if every step holds. Needs: elan (Lean 4.35.0), rustup/cargo, a C/C++ compiler, cmake,
# libclang, python3. Read-only towards the chain; step 7 downloads the source and a docker image.
set -euo pipefail
cd "$(dirname "$0")"
ROOT=$PWD
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
N=${TRACES:-1000}; M=${MOCK_TRACES:-200}; SEED=${SEED:-20261112}; J=${JOBS:-16}
MUT=0; REB=0; TLA=0
for a in "$@"; do case "$a" in --mutants) MUT=1;; --rebuild) REB=1;; --tla) TLA=1;; *) sed -n 2,15p "$0"; exit 2;; esac; done
mkdir -p evidence runs

echo "== 1. pinned wasm files"
(cd harness/wasm && sha256sum -c SHA256SUMS)

echo "== 2. Lean: build, no sorry, axioms"
(cd lean && ./check.sh) > runs/lean_check.txt 2>&1 || { tail -20 runs/lean_check.txt; echo "FAIL: Lean check"; exit 1; }
grep -q "Build completed successfully" runs/lean_check.txt || { tail -20 runs/lean_check.txt; echo "FAIL: Lean build"; exit 1; }
grep -E "depends on axioms|does not depend" runs/lean_check.txt > evidence/axioms.txt
echo "   $(wc -l < evidence/axioms.txt) statements, axioms within propext, Quot.sound, Classical.choice"

echo "== 3. harness"
(cd harness && ./build.sh) > runs/harness_build.txt 2>&1 || { tail -20 runs/harness_build.txt; echo "FAIL: harness build"; exit 1; }
[ -x harness/target/release/intents-gen ] || [ -x "${CARGO_TARGET_DIR:-/nonexistent}/release/intents-gen" ] || { tail -20 runs/harness_build.txt; echo "FAIL: no harness binary"; exit 1; }

echo "== 4. monitors on $N traces of the deployed wasm, $M of the mock token"
(cd harness && TRACES=$N MOCK_TRACES=$M SEED=$SEED JOBS=$J OUT=results ./run.sh) > runs/monitors.txt 2>&1 || { tail -20 runs/monitors.txt; echo "FAIL: monitor run"; exit 1; }
python3 -I - harness/results <<'PY'
import json, sys
out = sys.argv[1]
s = json.load(open(f"{out}/summary.json")); m = json.load(open(f"{out}/mock/summary.json"))
must_be_zero = ["overcredit", "tx_overcredit", "quiescent_gap", "supply_mismatch", "private_ran", "failed_changed",
                "ran_while_paused", "locked_spent", "unauthorized_ran", "auth_off_ran", "holdings_taken",
                "unknown_ledger_token", "derive_mismatch"]
bad = {k: v for k, v in s["violations"].items() if k in must_be_zero and v}
fails = {k: v for k, v in s["simulator_and_harness_failures"].items() if v}
fired = sum(v for k, v in m["violations"].items() if k in ("overcredit", "tx_overcredit", "quiescent_gap"))
print(f"   deployed wasm: {s['traces']} traces, {s['receipts']} receipts, {s['backing_inequalities_checked_after_receipts']} backing checks; "
      f"backing and access monitors that fired: {bad or 'none'}; simulator failures: {fails or 'none'}")
print(f"   guarded calls by accounts without the permission: {s['guarded_calls_by_accounts_without_the_permission']}, "
      f"calls with the auth-by-predecessor flag off: {s['calls_by_accounts_with_auth_by_predecessor_off']}; none ran")
print(f"   mock token: backing monitors fired {fired} times on {m['traces_with_violations']} of {m['traces']} traces")
sys.exit(0 if not bad and not fails and fired > 0 and s['guarded_calls_by_accounts_without_the_permission'] > 0 else 1)
PY

echo "== 5. replay through the Lean model"
# the check writes its own result to runs/; evidence/conformance.json keeps the full run quoted in README.md
CONF_OUT=$ROOT/runs/conformance_check.json TRACES=$N MOCK_TRACES=$M SEED=$SEED JOBS=$J scripts/conformance.sh > runs/conformance.txt 2>&1 || { tail -20 runs/conformance.txt; echo "FAIL: replay"; exit 1; }
python3 -I - runs/conformance_check.json <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); ok = True
for k, r in c["replay"].items():
    print(f"   {k}: {r['contract_steps']} receipts on the contract, agree {r['agree']}, disagree {r['disagree']}, "
          f"outcome not compared: {r['auth'] + r['env'] + r['skipped']} {json.dumps(r['not_compared'])}")
    ok = ok and r["disagree"] == 0 and r["skipped"] == 0 and r["agree"] > 0
    w = r.get("world") or {}
    if w.get("traces"):
        print(f"   {k}, token and contract in one world: {w['token_receipts']} receipts on the token, {w['contract_receipts']} on the "
              f"contract; agree {w['agree']}, disagree {w['disagree']}, failed for gas with nothing changed {w['env']}")
        ok = ok and w["disagree"] == 0 and w["agree"] > 0
ok = ok and (c["replay"]["standard_token"].get("world") or {}).get("agree", 0) > 0
sys.exit(0 if ok else 1)
PY

if [ $MUT = 1 ]; then
  echo "== 6. one-line changes of the model"
  G=${CARGO_TARGET_DIR:-harness/target}/release/intents-gen
  $G traces harness/wasm/intents.wasm harness/wasm/ft.wasm harness/wasm/w_near.wasm $SEED 0 50 > runs/mut_std1.jsonl &
  $G traces harness/wasm/intents.wasm harness/wasm/ft.wasm harness/wasm/w_near.wasm $SEED 50 50 > runs/mut_std2.jsonl &
  $G traces harness/wasm/intents.wasm harness/wasm/mock_fee_token.wasm harness/wasm/w_near.wasm $SEED 0 70 mock > runs/mut_fee.jsonl &
  $G traces harness/wasm/intents.wasm harness/wasm/mock_reply_token.wasm harness/wasm/w_near.wasm $SEED 0 70 mock > runs/mut_reply.jsonl &
  wait
  cat runs/mut_std1.jsonl runs/mut_std2.jsonl runs/mut_fee.jsonl runs/mut_reply.jsonl > runs/mut_all.jsonl
  rm -f runs/mut_std1.jsonl runs/mut_std2.jsonl runs/mut_fee.jsonl runs/mut_reply.jsonl
  python3 scripts/model_mutants.py lean runs/mut_all.jsonl runs/mutants-work evidence/model_mutants.json | tail -1 | tee runs/mutants.txt
  grep -q "not detected or failed: 0 \[\]; control: PASS" runs/mutants.txt || { echo "FAIL: a model mutant was not noticed"; exit 1; }
  rm -rf runs/mut_all.jsonl runs/mutants-work
fi

if [ $REB = 1 ]; then
  echo "== 7. rebuild from the source the contract names"
  scripts/rebuild.sh | tee evidence/rebuild_run.log | tail -4
  grep -q "RESULT: BYTE-IDENTICAL" evidence/rebuild_run.log || { echo "FAIL: the rebuild differs from the deployed bytes"; exit 1; }
fi
if [ $TLA = 1 ]; then
  echo "== 8. TLA+ specification, model-checked by TLC"
  tla/run.sh | tee runs/tla_run.txt || { echo "FAIL: TLC"; exit 1; }
fi
echo "RESULT: PASS"
