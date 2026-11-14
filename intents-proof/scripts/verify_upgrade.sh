#!/bin/bash
# verify_upgrade.sh <git commit of near/intents | path to a wasm | --tree <built source tree>> [traces]
#
# The upgrade gate. Takes a candidate version of the Intents contract and answers, before it is deployed:
# do the proved properties of the token ledger carry over to it?
#
# Static part (needs the source, i.e. a commit):
#   S1 the source files the model mirrors are unchanged since the certified commit;
#   S2 no place in the contract writes the ledger that did not write it before (call sites of the ledger
#      primitives across the contract and its crates);
#   S3 the exported methods of the wasm are the same.
# Dynamic part:
#   D1 the candidate is run on the nearcore runtime on random traces; the backing and access monitors stay silent;
#   D2 every receipt agrees with the Lean model in ../lean, in both replays: receipt by receipt through the ledger
#      functions, and token and contract together through the step function of the two-contract world.
#
# Verdicts (written to evidence/upgrade_<code hash>.json):
#   IDENTICAL       the candidate is byte for byte the certified code
#   CARRIES OVER    S1-S3 and D1-D2 all hold: the code the proof is about is unchanged and behaves the same
#   NEEDS REVIEW    D1-D2 hold but S1, S2 or S3 does not: the listed changes touch what the proof is about; the model
#                   has to be compared with the new source before the certificate is reused
#   DIVERGES        D1 or D2 fails
#   For a wasm file without source the static part is S3 only, and the best verdict is
#   SAME ON THE RUN: no difference was observed, which is weaker than CARRIES OVER.
#
# What the dynamic part cannot see, and why the static part exists: a change that acts only on particular inputs,
# a new entry point the traces never call, a permission check removed on a path the traces do not probe.
# Exit status 0 only for IDENTICAL and CARRIES OVER. Environment: SEED, JOBS, REBUILD_DIR (clone of near/intents).
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
ARG=${1:?usage: verify_upgrade.sh <commit | wasm | --tree dir> [traces]}; N=${2:-400}; SEED=${SEED:-20261112}; J=${JOBS:-16}
CERT_COMMIT=16d04f6ec4401263f8914638710260da50bb46b0
# the source the model mirrors, and the functions through which the contract writes the ledger
SCOPE="contracts/defuse/src/contract/tokens contracts/defuse/src/contract/state contracts/defuse/src/contract/accounts contracts/defuse/src/contract/intents contracts/defuse/src/tokens contracts/defuse/src/accounts.rs contracts/defuse/core/src/engine contracts/defuse/core/src/intents contracts/defuse/core/src/accounts"
PRIMS='(\.|::)(deposit|withdraw|internal_add_balance|internal_sub_balance|resolve_deposit_internal|internal_mt_batch_transfer)\(|total_supplies'
HAVE_SOURCE=0
H=$ROOT/harness; MODEL=$ROOT/lean/.lake/build/bin/intentsmodel
source "$H/scripts/env.sh"
G=$CARGO_TARGET_DIR/release/intents-gen
[ -x "$G" ] && [ -x "$MODEL" ] || { echo "build first: ./check.sh"; exit 2; }
OUT=$ROOT/runs/upgrade; rm -rf "$OUT"; mkdir -p "$OUT" "$ROOT/evidence"
SRC_NOTE="wasm file"; CHANGED=""
static_facts() { # static_facts <source tree>: S1 and S2 of the tree against the certified commit
  ( cd "$1"
    git diff --name-only $CERT_COMMIT -- $SCOPE > "$OUT/scope_changed.txt"
    norm() { sed -E 's/^([^:]+):[0-9]+:[[:space:]]*/\1: /' | grep -v '/tests/' | sort; }
    # the contract crate and its core; calls that only attach a NEAR deposit to a promise are not ledger writes
    grep -rnE "$PRIMS" --include='*.rs' contracts/defuse 2>/dev/null | grep -v 'deposit(NearToken' | norm > "$OUT/callsites_candidate.txt"
    git grep -nE "$PRIMS" $CERT_COMMIT -- contracts/defuse 2>/dev/null | sed -E "s/^$CERT_COMMIT://" | grep '\.rs:' | grep -v 'deposit(NearToken' | norm > "$OUT/callsites_certified.txt"
    CHANGED=$(git diff --shortstat $CERT_COMMIT -- contracts crates | sed 's/^ *//'); echo "$CHANGED" > "$OUT/changed.txt" )
  HAVE_SOURCE=1; CHANGED=$(cat "$OUT/changed.txt")
}
if [ "$ARG" = "--tree" ]; then
  # a source tree that is already built (used for trees that are not commits, e.g. deliberate one-line changes)
  T=${2:?usage: verify_upgrade.sh --tree <dir> [traces]}; N=${3:-400}
  [ -f "$T/target/near/defuse/defuse.wasm" ] || { echo "no built wasm in $T/target/near/defuse/"; exit 2; }
  cp "$T/target/near/defuse/defuse.wasm" "$OUT/candidate.wasm"
  SRC_NOTE="source tree (not a commit)"; static_facts "$T"
elif [ -f "$ARG" ]; then
  cp "$ARG" "$OUT/candidate.wasm"
else
  R=${REBUILD_DIR:-$ROOT/runs/rebuild}; mkdir -p "$R"
  [ -d "$R/src/.git" ] || git clone -q https://github.com/near/intents "$R/src"
  cd "$R/src" && git fetch -q origin && git checkout -q -f "$ARG" && git clean -fdxq || { echo "cannot check out $ARG"; exit 2; }
  COMMIT=$(git rev-parse HEAD); SRC_NOTE="near/intents@$COMMIT ($(git log -1 --format=%cs))"
  # cargo-near looks for the artifact under CARGO_TARGET_DIR, which the harness environment points elsewhere
  (cd contracts/defuse && env -u CARGO_TARGET_DIR cargo near build reproducible-wasm > "$OUT/build.log" 2>&1) || { echo "the candidate does not build"; tail -5 "$OUT/build.log"; exit 2; }
  cp target/near/defuse/defuse.wasm "$OUT/candidate.wasm"
  static_facts "$R/src"
fi
cd "$H"
gen() { # gen <prefix> <ft wasm> <count> [mock]
  local pre=$1 ft=$2 n=$3 mock=${4:-} per=$(( ($3 + J - 1) / J )) k s c pids=()
  for ((k = 0; k < J; k++)); do
    s=$((k * per)); c=$(( n - s < per ? n - s : per )); [ "$c" -gt 0 ] || continue
    "$G" traces "$OUT/candidate.wasm" "$ft" wasm/w_near.wasm "$SEED" "$s" "$c" $mock > "$OUT/${pre}_$k.jsonl" & pids+=($!)
  done
  for p in "${pids[@]}"; do wait "$p" || { echo "the candidate cannot be driven by the harness (init or a call failed)"; return 1; }; done
}
gen std wasm/ft.wasm "$N" || exit 1
gen reply wasm/mock_reply_token.wasm $(( N / 4 )) mock || exit 1
python3 -I scripts/monitor.py --out "$OUT/monitors.json" --violations "$OUT/violations.jsonl" --sample-dir "$OUT/sample" --sample 0 "$OUT"/std_*.jsonl > /dev/null
for f in "$OUT"/std_*.jsonl "$OUT"/reply_*.jsonl; do "$MODEL" --summary --world < "$f" | tail -1 > "$f.replay"; done
python3 -I - "$OUT" "$ROOT/evidence" "$SRC_NOTE" "${CHANGED:-}" "$HAVE_SOURCE" "$N" "$H/wasm/intents.wasm" <<'PY'
import glob, hashlib, json, os, sys
out, ev, src, changed, have_source, n, cert = sys.argv[1:8]
A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58(b):
    x = int.from_bytes(b, "big"); s = ""
    while x: x, r = divmod(x, 58); s = A[r] + s
    return s
def exports(path):
    """Names of the exported functions of a wasm module (the methods of the contract)."""
    b = open(path, "rb").read(); i = 8; names = []
    def leb(i):
        r = sh = 0
        while True:
            c = b[i]; i += 1; r |= (c & 0x7F) << sh; sh += 7
            if c < 0x80: return r, i
    while i < len(b):
        sec = b[i]; i += 1; size, i = leb(i); end = i + size
        if sec == 7:
            cnt, i = leb(i)
            for _ in range(cnt):
                ln, i = leb(i); name = b[i:i + ln].decode(errors="replace"); i += ln
                kind = b[i]; i += 1; _, i = leb(i)
                if kind == 0: names.append(name)
        i = end
    return set(names)
def lines(p):
    return [l.rstrip("\n") for l in open(p)] if os.path.exists(p) else []
cand_path = f"{out}/candidate.wasm"
cand = open(cand_path, "rb").read(); d = hashlib.sha256(cand).digest()
same = cand == open(cert, "rb").read()
e_new, e_old = exports(cand_path), exports(cert)
exp_added, exp_removed = sorted(e_new - e_old), sorted(e_old - e_new)
static = {"S3_exports_added": exp_added, "S3_exports_removed": exp_removed}
if have_source == "1":
    scope = [l for l in lines(f"{out}/scope_changed.txt") if l.strip()]
    c_new, c_old = lines(f"{out}/callsites_candidate.txt"), lines(f"{out}/callsites_certified.txt")
    def diff(a, b):
        b = list(b); r = []
        for x in a:
            if x in b: b.remove(x)
            else: r.append(x)
        return r
    static.update({"S1_modelled_files_changed": scope, "S2_ledger_write_sites": len(c_old),
                   "S2_sites_added": diff(c_new, c_old)[:20], "S2_sites_removed": diff(c_old, c_new)[:20]})
else:
    static["S1_S2"] = "not available: a wasm file was given, there is no source to compare"
mon = json.load(open(f"{out}/monitors.json"))
must = ["overcredit", "tx_overcredit", "quiescent_gap", "supply_mismatch", "private_ran", "failed_changed", "ran_while_paused",
        "locked_spent", "unauthorized_ran", "auth_off_ran", "holdings_taken", "unknown_ledger_token", "derive_mismatch"]
fired = {k: v for k, v in mon["violations"].items() if k in must and v}
fails = {k: v for k, v in mon["simulator_and_harness_failures"].items() if v}
tot = {"contract_steps": 0, "agree": 0, "disagree": 0, "auth": 0, "env": 0, "skipped": 0, "not_compared": {}, "world": {}}
for p in glob.glob(f"{out}/*.jsonl.replay"):
    last = json.load(open(p))
    for k, v in list(last["total"].items()) + [("world", last.get("world", {}))]:
        if isinstance(v, dict):
            for why, cnt in v.items(): tot[k][why] = tot[k].get(why, 0) + cnt
        else: tot[k] = tot.get(k, 0) + v
dyn_ok = (not fired and not fails and tot["disagree"] == 0 and tot["skipped"] == 0 and tot["agree"] > 0
          and tot["world"].get("disagree", 0) == 0 and tot["world"].get("agree", 0) > 0)
static_ok = not exp_added and not exp_removed and (have_source != "1" or not (static["S1_modelled_files_changed"] or static["S2_sites_added"] or static["S2_sites_removed"]))
if same: verdict = "IDENTICAL"
elif not dyn_ok: verdict = "DIVERGES"
elif not static_ok: verdict = "NEEDS REVIEW"
elif have_source == "1": verdict = "CARRIES OVER"
else: verdict = "SAME ON THE RUN"
res = {"candidate": src, "code_hash": b58(d), "sha256": d.hex(), "bytes": len(cand),
       "source_changes_since_certified_commit": changed or None, "static": static,
       "traces": int(n) + int(n) // 4, "receipts": mon["receipts"], "backing_checks": mon["backing_inequalities_checked_after_receipts"],
       "monitors_fired": fired, "simulator_failures": fails, "replay": tot, "verdict": verdict}
json.dump(res, open(f"{ev}/upgrade_{res['code_hash'][:12]}.json", "w"), indent=1)
print(json.dumps(res, indent=1))
sys.exit(0 if verdict in ("IDENTICAL", "CARRIES OVER") else 1)
PY
RC=$?
rm -f "$OUT"/std_*.jsonl "$OUT"/reply_*.jsonl
exit $RC
