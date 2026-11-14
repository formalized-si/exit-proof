"""Compact summary of a check.sh run (reads compare.py's results.json)."""
import json
import sys

res_p, ax_p, log_p, t_lean, t_sim, t_model, n, nf, no, seed = sys.argv[1:11]
r = json.load(open(res_p))
axioms = [l.strip() for l in open(ax_p) if l.strip()]
log = open(log_p).read().splitlines()
wasm = next((l for l in log if l.startswith("wasm ")), "")
env = r.get("env", {})
out = {
    "contract": "near/core-contracts staking-pool @ 1cacc9d (deployed by poolv1.near)",
    "wasm": wasm,
    "seed": int(seed),
    "requested": {"normal": int(n), "faults": int(nf), "overflow": int(no)},
    "traces": r["traces"], "steps": r["steps"], "calls": r["calls"],
    "verdict": r.get("verdict"), "problems": r.get("problems"),
    "exact_traces": r["exact_traces"], "mismatch_traces": r["mismatch_traces"],
    "model_missing": r["model_missing"],
    "errtext_match": r["errtext_match"], "errtext_mismatch": r["errtext_mismatch_count"],
    "families": r.get("families"),
    "fault_step_outcomes": r.get("fault_step_outcomes"),
    "env": {k: env.get(k) for k in (
        "conservation_violations", "model_vs_sim_transfer_mismatch", "pua_checked", "pua_violations",
        "pua_obs_only_violations", "lean_pua_checked", "lean_pua_violations", "lean_cons_violations",
        "negative_R", "calls_crossing_epoch", "env_negative_delta")},
    "sim_fail_model_ok": len(env.get("sim_fail_model_ok", [])),
    "ok_fail_per_method": r.get("ok_fail_per_method"),
    "error_histogram_top": dict(list(r.get("error_histogram", {}).items())[:30]),
    "axioms": axioms,
    "seconds": {"lean_build_and_axioms": int(t_lean), "sim": int(t_sim), "model": int(t_model)},
}
json.dump(out, sys.stdout, indent=1)
print()
