#!/usr/bin/env python3
"""Adequacy of the conformance run: one-line mutations of the pinned plugin source
(near-plugins-derive/src/upgradable.rs, v0.5.1), each compiled into the example vault with
cargo-near (all three builds); the run must report a divergence for each, and name the statement.

usage: mutants.py KIT_DIR [ids...]
Needs plugin/near-plugins (scripts/fetch-plugin.sh). Builds into $UW_CONTRACT_TARGET; writes
KIT_DIR/evidence/mutants.json and KIT_DIR/evidence/mutants.diff. M0_control is the unmutated
source built the same way (path patch) and must pass.
Exit status: 0 iff M0_control passes and every other mutant fails with its first divergence in
the expected statement.
"""
import difflib
import hashlib
import json
import os
import shutil
import subprocess
import sys

FILE = "near-plugins-derive/src/upgradable.rs"
TS_CHECK = "                if ::near_sdk::env::block_timestamp() < staging_timestamp {"
STAGE_TS = "                    let timestamp = ::near_sdk::env::block_timestamp().saturating_add(duration);"
UPD_TS = "                let staging_duration_timestamp = ::near_sdk::env::block_timestamp() + current_staging_duration;"

# (id, pattern, which occurrence (1-based), replacement, expected statement, what it does)
MUTANTS = [
    ("M0_control", None, 0, None, "-", "unmutated source through the same path patch"),
    ("M1_deploy_check_flipped", TS_CHECK, 1,
     "                if ::near_sdk::env::block_timestamp() > staging_timestamp {",
     "W1", "up_deploy_code: comparison flipped (deploy allowed only before the staging timestamp)"),
    ("M2_deploy_one_ns_early", TS_CHECK, 1,
     "                if ::near_sdk::env::block_timestamp().saturating_add(1) < staging_timestamp {",
     "W1", "up_deploy_code: accepted one nanosecond before the staging timestamp"),
    ("M3_stage_ignores_duration", STAGE_TS, 1,
     "                    let timestamp = ::near_sdk::env::block_timestamp().saturating_add(duration.min(0));",
     "W1", "up_stage_code: staging timestamp = block timestamp, the duration is not added"),
    ("M4_hash_check_removed", "                if hash != expected_hash {", 1,
     "                if false && hash != expected_hash {",
     "W2", "up_deploy_code: the hash argument is not checked"),
    ("M5_duration_update_no_delay", UPD_TS, 1,
     "                let staging_duration_timestamp = ::near_sdk::env::block_timestamp() + current_staging_duration.min(0);",
     "W3", "up_stage_update_staging_duration: the update is applicable at once"),
    ("M6_duration_update_written_directly",
     "                self.up_set_duration(__UpgradableStorageKey::NewStagingDuration, staging_duration);", 1,
     "                self.up_set_duration(__UpgradableStorageKey::StagingDuration, staging_duration);",
     "W3", "up_stage_update_staging_duration: writes the staging duration itself"),
    ("M7_apply_check_removed", TS_CHECK, 2,
     "                if false {",
     "W3", "up_apply_update_staging_duration: the timestamp is not checked"),
    ("M8_reinit_allowed",
     "                ::near_sdk::require!(self.up_get_duration(__UpgradableStorageKey::StagingDuration).is_none(), \"Upgradable: staging duration was already initialized\");", 1,
     "                ::near_sdk::require!(self.up_get_duration(__UpgradableStorageKey::StagingDuration).is_none() || true, \"Upgradable: staging duration was already initialized\");",
     "W3", "up_init_staging_duration: allowed when a duration is already set"),
    ("M9_update_timestamp_wraps", UPD_TS, 1,
     "                let staging_duration_timestamp = ::near_sdk::env::block_timestamp().wrapping_add(current_staging_duration);",
     "W3", "up_stage_update_staging_duration: wrapping instead of checked addition"),
    ("M10_stage_timestamp_wraps", STAGE_TS, 1,
     "                    let timestamp = ::near_sdk::env::block_timestamp().wrapping_add(duration);",
     "W1", "up_stage_code: wrapping instead of saturating addition"),
    ("M11_removal_keeps_timestamp",
     "                    ::near_sdk::env::storage_remove(self.up_storage_key(__UpgradableStorageKey::StagingTimestamp).as_ref());", 1,
     "                    let _ = self.up_storage_key(__UpgradableStorageKey::StagingTimestamp);",
     "W1", "up_stage_code with empty input: the staging timestamp is left in storage"),
    ("M12_deploy_guarded_by_stager_roles",
     "            #[#cratename::access_control_any(roles(#(#acl_roles_code_deployers),*))]", 1,
     "            #[#cratename::access_control_any(roles(#(#acl_roles_code_stagers),*))]",
     "ACL", "up_deploy_code: checks the code stagers' roles instead of the deployers'"),
]


def run(cmd, cwd=None, env=None):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)


def replace_nth(src, old, nth, new):
    parts = src.split(old)
    if len(parts) - 1 < nth:
        return None
    return old.join(parts[:nth]) + new + old.join(parts[nth:])


def main():
    kit = os.path.abspath(sys.argv[1])
    only = set(sys.argv[2:])
    plugin = os.path.join(kit, "plugin", "near-plugins")
    vault = os.path.join(kit, "contract", "vault")
    env = dict(os.environ)
    env["UW_LOCKED"] = "0"
    results, diffs = [], []
    for mid, old, nth, new, expect, what in MUTANTS:
        if only and mid not in only:
            continue
        d = os.path.join(kit, "mutants", mid)
        shutil.rmtree(d, ignore_errors=True)
        os.makedirs(d)
        shutil.copytree(plugin, os.path.join(d, "near-plugins"), ignore=shutil.ignore_patterns(".git", "target"))
        shutil.copytree(vault, os.path.join(d, "vault"), ignore=shutil.ignore_patterns("target"))
        with open(os.path.join(d, "vault", "Cargo.toml"), "a") as f:
            f.write('\n[patch."https://github.com/near/near-plugins.git"]\n'
                    'near-plugins = { path = "../near-plugins/near-plugins" }\n')
        target = os.path.join(d, "near-plugins", FILE)
        src = open(target).read()
        if old is not None:
            mut = replace_nth(src, old, nth, new)
            if mut is None:
                results.append({"id": mid, "error": f"pattern occurs {src.count(old)} times, wanted occurrence {nth}"})
                continue
            open(target, "w").write(mut)
            diffs.append("".join(difflib.unified_diff(src.splitlines(True), mut.splitlines(True),
                                                      f"a/{FILE}", f"b/{FILE} ({mid})", n=1)))
        # The shared target directory keys the plugin's artifacts by crate, not by this copy's
        # path, and cargo trusts file times: give every source file of the copy (and the vault) a
        # new time, so that no build - the control included - reuses another mutant's artifact.
        for root, _, files in os.walk(os.path.join(d, "near-plugins")):
            for f in files:
                if f.endswith(".rs") or f == "Cargo.toml":
                    os.utime(os.path.join(root, f))
        os.utime(os.path.join(d, "vault", "src", "lib.rs"))
        out = os.path.join(d, "out")
        b = run([os.path.join(kit, "scripts", "build-contract.sh"), os.path.join(d, "vault"), out], env=env)
        wasms = [os.path.join(out, f"vault_v{i}.wasm") for i in (1, 2, 3)]
        if b.returncode != 0 or not all(os.path.exists(w) for w in wasms):
            results.append({"id": mid, "error": "build failed", "log": (b.stdout + b.stderr)[-1500:]})
            print(f"{mid}: build failed", flush=True)
            continue
        cenv = dict(os.environ)
        cenv["OUT"] = os.path.join(d, "run")
        c = run([os.path.join(kit, "scripts", "conformance.sh"), out], env=cenv)
        conf = json.load(open(os.path.join(d, "run", "conformance.json")))
        fd = conf.get("first_divergence") or {}
        r = {"id": mid, "mutation": what, "file": FILE, "expected": expect,
             "wasm_sha256_v1": hashlib.sha256(open(wasms[0], "rb").read()).hexdigest(),
             "result": "PASS" if conf["ok"] else "FAIL",
             "traces": conf["traces"], "diverging_traces": conf["diverging_traces"],
             "diverging_traces_by_first_property": conf["diverging_traces_by_first_property"],
             "first_divergence": {k: fd.get(k) for k in ("trace", "h", "kind", "property", "method", "field", "pred", "args", "detail")} if fd else None,
             "monitor_violations": conf["monitor_violations"],
             "exit_status": c.returncode}
        results.append(r)
        print(f"{mid}: {r['result']} diverging={r['diverging_traces']} by={r['diverging_traces_by_first_property']} "
              f"first={fd.get('property')} {fd.get('kind')} {fd.get('method') or fd.get('field')} "
              f"monitors={r['monitor_violations']} | expected {expect}", flush=True)
        # keep the wasm and the run summary, drop the source copies
        shutil.rmtree(os.path.join(d, "vault"), ignore_errors=True)
        shutil.rmtree(os.path.join(d, "near-plugins"), ignore_errors=True)
    hashes = [r.get("wasm_sha256_v1") for r in results if r.get("wasm_sha256_v1")]
    stale = len(hashes) != len(set(hashes))
    if stale:
        print("FAIL: two mutant builds produced the same wasm (stale build artifact?)")
    os.makedirs(os.path.join(kit, "evidence"), exist_ok=True)
    tag = "" if not only else "_partial"
    json.dump(results, open(os.path.join(kit, "evidence", f"mutants{tag}.json"), "w"), indent=1)
    open(os.path.join(kit, "evidence", f"mutants{tag}.diff"), "w").write("\n".join(diffs))
    def as_expected(r):
        if r.get("error"):
            return False
        if r["id"] == "M0_control":
            return r["result"] == "PASS"
        return r["result"] == "FAIL" and (r.get("first_divergence") or {}).get("property") == r["expected"]
    bad = [r["id"] for r in results if not as_expected(r)] + (["duplicate wasm"] if stale else [])
    if not results:
        bad.append("no mutant was run")
    print("mutants: " + ("all detected, control passes" if not bad else f"UNEXPECTED: {bad}"))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
