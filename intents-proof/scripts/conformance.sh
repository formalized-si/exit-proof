#!/bin/bash
# Replays every receipt of freshly generated traces of the deployed wasm through the Lean model (intentsmodel):
# receipt by receipt through the ledger functions, and, for the traces of the standard token, the receipts of the
# token and of the contract together through the step function of the two-contract world (`--world`).
# Traces are streamed, not stored. Writes evidence/conformance.json (or CONF_OUT). Fails if any part of the run is
# missing: a generator or model process that stopped, or fewer traces replayed than asked for.
# Environment: TRACES (default 4000), MOCK_TRACES (default 400), SEED (default 20261112), JOBS (default 16).
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
N=${TRACES:-4000}; M=${MOCK_TRACES:-400}; SEED=${SEED:-20261112}; J=${JOBS:-16}
H=$ROOT/harness; MODEL=$ROOT/lean/.lake/build/bin/intentsmodel
source "$H/scripts/env.sh"
G=$CARGO_TARGET_DIR/release/intents-gen
[ -x "$G" ] || { echo "no harness binary: run harness/build.sh"; exit 1; }
[ -x "$MODEL" ] || { echo "no model binary: run lean/check.sh"; exit 1; }
OUT=$ROOT/runs/conformance; mkdir -p "$OUT" "$ROOT/evidence"; rm -f "$OUT"/part_*
DEST=${CONF_OUT:-$ROOT/evidence/conformance.json}
cd "$H"
run() { # run <count> <prefix> <ft wasm> [mock]
  local n=$1 pre=$2 ft=$3 mock=${4:-} per=$(( ($1 + J - 1) / J )) k s c pids=()
  for ((k = 0; k < J; k++)); do
    s=$((k * per)); c=$(( n - s < per ? n - s : per ))
    [ "$c" -gt 0 ] || continue
    ( set -o pipefail
      "$G" traces wasm/intents.wasm "$ft" wasm/w_near.wasm "$SEED" "$s" "$c" $mock \
        | tee >(wc -l > "$OUT/part_${pre}_$k.count") | "$MODEL" --summary --world | tail -1 > "$OUT/part_${pre}_$k.json"
      echo "${PIPESTATUS[0]} ${PIPESTATUS[2]} $c" > "$OUT/part_${pre}_$k.rc" ) & pids+=($!)
  done
  for p in "${pids[@]}"; do wait "$p"; done
}
run "$N" standard_token wasm/ft.wasm
run "$M" fee_mock wasm/mock_fee_token.wasm mock
run "$M" reply_mock wasm/mock_reply_token.wasm mock
python3 -I - "$OUT" "$N" "$M" "$SEED" "$H/wasm/intents.wasm" "$DEST" <<'PY'
import glob, hashlib, json, sys
out, n, m, seed, wasm, dest = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
res = {}; bad = []
want = {"standard_token": n, "fee_mock": m, "reply_mock": m}
for pre in ("standard_token", "fee_mock", "reply_mock"):
    tot = {"agree": 0, "disagree": 0, "auth": 0, "env": 0, "skipped": 0, "contract_steps": 0}
    traces = 0
    for p in sorted(glob.glob(f"{out}/part_{pre}_*.rc")):
        gen_rc, model_rc, asked = open(p).read().split()
        base = p[:-3]
        got = int(open(base + ".count").read().strip() or 0)
        if gen_rc != "0" or model_rc != "0" or got != int(asked):
            bad.append(f"{pre}: a part asked for {asked} traces, got {got} (generator exit {gen_rc}, model exit {model_rc})")
            continue
        traces += got
        last = json.load(open(base + ".json"))
        for k, v in list(last["total"].items()) + [("world", last.get("world", {}))]:
            if isinstance(v, dict):
                d = tot.setdefault(k, {})
                for why, cnt in v.items():
                    d[why] = d.get(why, 0) + cnt
            else:
                tot[k] = tot.get(k, 0) + v
    tot["traces_replayed"] = traces
    if traces != want[pre]:
        bad.append(f"{pre}: {traces} traces replayed, {want[pre]} asked for")
    res[pre] = tot
summary = {"seed": seed, "traces_standard_token": n, "traces_each_mock": m,
           "intents_wasm_sha256": hashlib.sha256(open(wasm, "rb").read()).hexdigest(), "replay": res}
if bad:
    print("FAIL: the run is incomplete:\n  " + "\n  ".join(bad)); sys.exit(1)
json.dump(summary, open(dest, "w"), indent=1)
print(json.dumps(summary))
PY
