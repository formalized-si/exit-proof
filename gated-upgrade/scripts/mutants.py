"""Mutants of the gated vault: one changed line of contract/gated-vault/src/lib.rs each, the v1
build recompiled, the scenarios and a batch of random traces run against it.

usage: python3 scripts/mutants.py <kit directory>      (from check.sh --mutants)
A mutant is detected when a scenario check fails or the trace monitor reports a violation. The
control (the unchanged source, built the same way) must pass both and give the pinned v1 bytes.
Writes evidence/mutants.json; exit status 0 only if the control passes and every mutant is detected.
Needs cargo-near. Environment: TRACES_MUTANT (default 300), SEED (default 20261113).
"""
import glob
import hashlib
import json
import os
import shutil
import subprocess
import sys

KIT = os.path.abspath(sys.argv[1])
SRC = os.path.join(KIT, "contract", "gated-vault")
OUT = os.path.join(KIT, "contract", "out")
WORK = os.path.join(KIT, "runs", "mutants")
GU = os.path.join(os.environ["CARGO_TARGET_DIR"], "release", "gu-test")
TRACES = os.environ.get("TRACES_MUTANT", "300")
SEED = os.environ.get("SEED", "20261113")

MUTANTS = [
    ("M0_control", "no change", None, None),
    ("M1_any_attestor", "on_certificates: the attestor of a certificate is not checked",
     " && self.gate.attestors.contains(&c.attestor)", ""),
    ("M2_revoked_counts", "on_certificates: a revoked certificate counts",
     "!c.revoked && c.code_hash == hash", "c.code_hash == hash"),
    ("M3_any_kind", "on_certificates: the kind of a certificate is not checked",
     " && c.body.kind == self.gate.kind &&", " &&"),
    ("M4_any_hash", "on_certificates: the hash of a certificate is not checked",
     "!c.revoked && c.code_hash == hash &&", "!c.revoked &&"),
    ("M5_public_callback", "on_certificates is not #[private]",
     "    #[private]\n    pub fn on_certificates(", "    pub fn on_certificates("),
    ("M6_stager_deploys", "the plugin's deploy method also accepts the code stagers' role",
     "code_deployers(Role::CodeDeployer),", "code_deployers(Role::CodeDeployer, Role::CodeStager),"),
    ("M7_no_early_check", "deploy_certified asks the registry before the delay has passed",
     "if env::block_timestamp() < staging_timestamp {", "if false && env::block_timestamp() < staging_timestamp {"),
    ("M8_deploys_what_is_staged_now", "on_certificates deploys whatever is staged at callback time, not the hash that was checked",
     "        self.up_deploy_code(hash, None)", "        self.up_deploy_code(self.up_staged_code_hash().unwrap_or(hash), None)"),
    ("M9_public_init", "new is not #[private]",
     "    #[init]\n    #[private]\n", "    #[init]\n"),
    ("M10_deployer_role_to_stagers", "new grants the deployer role to the stagers as well",
     "                contract.acl_grant_role(Role::CodeStager.into(), stager).is_some(),",
     "                contract.acl_grant_role(Role::CodeDeployer.into(), stager.clone()).is_some() && contract.acl_grant_role(Role::CodeStager.into(), stager).is_some(),"),
    ("M11_any_certificate", "on_certificates: any certificate in the answer counts",
     "            !c.revoked && c.code_hash == hash", "            true || !c.revoked && c.code_hash == hash"),
]


def sha256(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def build(name, old, new):
    d = os.path.join(WORK, name)
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(os.path.join(d, "src"))
    for f in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        shutil.copy(os.path.join(SRC, f), d)
    text = open(os.path.join(SRC, "src", "lib.rs")).read()
    if old is not None:
        if text.count(old) != 1:
            raise SystemExit(f"{name}: the line to change occurs {text.count(old)} times")
        text = text.replace(old, new)
    open(os.path.join(d, "src", "lib.rs"), "w").write(text)
    home = os.path.realpath(os.environ.get("CARGO_HOME", os.path.expanduser("~/.cargo")))
    # A target directory of their own, and the crate's fingerprint removed before every build:
    # cargo keeps one fingerprint and one output file per crate name, whatever directory the
    # source is in, so a mutant must never share them with the kit's crate or with another mutant.
    target = os.environ["GU_CONTRACT_TARGET"] + "-mutants"
    for fp in glob.glob(os.path.join(target, "wasm32-unknown-unknown", "release", ".fingerprint", "gated-vault-*")):
        shutil.rmtree(fp, ignore_errors=True)
    env = dict(os.environ, CARGO_TARGET_DIR=target)
    for k in ("CARGO_PROFILE_RELEASE_LTO", "CARGO_PROFILE_DEV_DEBUG"):
        env.pop(k, None)
    r = subprocess.run(["cargo", "near", "build", "non-reproducible-wasm", "--locked", "--no-abi", "--env",
                        f"RUSTFLAGS=-C link-arg=-s --remap-path-prefix={home}=/cargo", "--out-dir", os.path.join(d, "out")],
                       cwd=d, env=env, capture_output=True, text=True)
    wasm = os.path.join(d, "out", "gated_vault.wasm")
    if r.returncode != 0 or not os.path.exists(wasm):
        return None, (r.stdout + r.stderr)[-1500:]
    return wasm, ""


def run(wasm):
    codes = [wasm, os.path.join(OUT, "gated_vault_v2.wasm"), os.path.join(OUT, "gated_vault_v3.wasm"), os.path.join(OUT, "exitproof_registry.wasm")]
    s = subprocess.run([GU, "scenarios"] + codes, capture_output=True, text=True)
    failed, crashed = [], None
    try:
        w = json.loads(s.stdout)
        failed = [f"{sc['scenario']}: {c['check']}" for sc in w["scenarios"] for c in sc["checks"] if not c["holds"]]
    except ValueError:
        crashed = (s.stderr or s.stdout)[-400:]
    t = subprocess.run([GU, "traces"] + codes + [SEED, "0", TRACES], capture_output=True, text=True)
    try:
        tj = json.loads(t.stdout)
        violations, samples = tj["violations"], tj["violation_samples"][:3]
    except ValueError:
        violations, samples = -1, [(t.stderr or t.stdout)[-400:]]
    return failed, crashed, violations, samples


results, ok = [], True
for name, what, old, new in MUTANTS:
    wasm, err = build(name, old, new)
    if wasm is None:
        results.append({"mutant": name, "change": what, "result": "BUILD FAILED", "log": err})
        ok = False
        print(f"{name}: BUILD FAILED")
        continue
    failed, crashed, violations, samples = run(wasm)
    detected = bool(failed) or crashed is not None or violations != 0
    entry = {"mutant": name, "change": what, "wasm_sha256": sha256(wasm), "scenario_checks_failed": len(failed),
             "failed_checks": [f[:230] for f in failed[:6]], "trace_violations": violations, "violation_samples": [x[:300] for x in samples]}
    if crashed is not None:
        entry["scenarios_crashed"] = crashed
    if old is None:
        same = sha256(wasm) == sha256(os.path.join(OUT, "gated_vault_v1.wasm"))
        entry["same_bytes_as_pinned_v1"] = same
        entry["result"] = "PASS" if (not detected and same) else "FAIL"
        ok &= entry["result"] == "PASS"
    else:
        entry["result"] = "DETECTED" if detected else "NOT DETECTED"
        entry["old_line"], entry["new_line"] = old.strip(), new.strip()
        ok &= detected
    results.append(entry)
    print(f"{name}: {entry['result']} (scenario checks failed: {len(failed)}, trace violations: {violations})")
os.makedirs(os.path.join(KIT, "evidence"), exist_ok=True)
json.dump({"traces_per_mutant": int(TRACES), "seed": int(SEED), "ok": ok, "mutants": results},
          open(os.path.join(KIT, "evidence", "mutants.json"), "w"), indent=1)
sys.exit(0 if ok else 1)
