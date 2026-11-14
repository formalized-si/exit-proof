#!/usr/bin/env python3
"""Adequacy of the certification kit: one-line source mutations of near-contract-standards
5.29.0 (and of the example token's `#[private]`), each compiled into the official example token
with cargo-near; the kit must return FAIL for each and name the property.

usage: mutants.py KIT_DIR [ids...]
Builds into $CARGO_TARGET_DIR/token-build (default KIT_DIR/harness/target); writes
KIT_DIR/evidence/mutants.json, KIT_DIR/evidence/mutants.diff and a copy of every certificate in
KIT_DIR/evidence/mutants_certificates/. M0_control is the unmutated library built the same way
(path patch). The library source is KIT_DIR/std/near-contract-standards-5.29.0; if it is missing
it is downloaded from crates.io and checked against the checksum in token/example-ft/Cargo.lock.
Exit status: 0 iff M0_control is PASS and every other mutant is FAIL with its first divergence
attributed to the expected property.
"""
import difflib
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import urllib.request

STD = "near-contract-standards-5.29.0"
CORE = "src/fungible_token/core_impl.rs"
STOR = "src/fungible_token/storage_impl.rs"

MUTANTS = [
    ("M0_control", "std", CORE, None, None, "-", "unmutated library through the same path patch"),
    ("M1_refund_not_capped", "std", CORE, "            .min(amount.0);", "            .min(u128::MAX);",
     "P2", "unused amount no longer capped by the transferred amount"),
    ("M2_unparsable_means_used", "std", CORE, "            .unwrap_or(amount)", "            .unwrap_or(U128(0))",
     "P2", "an unparsable / failed / too long result counts as fully used"),
    ("M3_receiver_not_debited", "std", CORE,
     "                    self.accounts.insert(&receiver_id, &new_receiver_balance);",
     "                    let _ = new_receiver_balance;", "P2", "refund credited to the sender without debiting the receiver"),
    ("M4_storage_off_by_one", "std", CORE,
     "        self.account_storage_usage = env::storage_usage() - initial_storage_usage;",
     "        self.account_storage_usage = env::storage_usage() - initial_storage_usage - 1;",
     "P5", "storage minimum measured one byte short"),
    ("M5_resolve_gas_3tgas", "std", CORE, "const GAS_FOR_RESOLVE_TRANSFER: Gas = Gas::from_tgas(5);",
     "const GAS_FOR_RESOLVE_TRANSFER: Gas = Gas::from_tgas(3);", "P2", "settlement callback gets 3 Tgas instead of 5"),
    ("M6_withdraw_overdraft", "std", CORE, "        if let Some(new_balance) = balance.checked_sub(amount) {",
     "        if let Some(new_balance) = Some(balance.saturating_sub(amount)) {", "P4",
     "internal_withdraw saturates instead of refusing an overdraft"),
    ("M7_force_unregister_no_burn", "std", STOR, "                self.total_supply -= balance;",
     "                self.total_supply -= 0;", "P1", "force-unregister removes the balance but not from total_supply"),
    ("M8_unregister_default_force", "std", STOR, "        let force = force.unwrap_or(false);",
     "        let force = force.unwrap_or(true);", "P5", "storage_unregister without force burns a positive balance"),
    ("M9_deposit_refund_to_account", "std", STOR,
     "                Promise::new(env::predecessor_account_id()).transfer(refund).detach();",
     "                Promise::new(account_id.clone()).transfer(refund).detach();", "P5",
     "storage_deposit refunds the excess to the registered account instead of the payer"),
    ("M10_resolve_not_private", "example", "src/lib.rs", "    #[private]\n    fn ft_resolve_transfer(",
     "    fn ft_resolve_transfer(", "P3", "#[private] removed from the token's ft_resolve_transfer"),
]


def run(cmd, cwd=None, env=None):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)


def ensure_std(kit):
    """KIT/std/near-contract-standards-5.29.0: the crates.io release, checksum from the token's Cargo.lock."""
    d = os.path.join(kit, "std", STD)
    if os.path.isdir(d):
        return d
    lock = open(os.path.join(kit, "token", "example-ft", "Cargo.lock")).read()
    want = re.search(r'name = "near-contract-standards"\nversion = "5\.29\.0"\nsource = [^\n]*\nchecksum = "([0-9a-f]{64})"', lock).group(1)
    url = f"https://static.crates.io/crates/near-contract-standards/{STD}.crate"
    data = urllib.request.urlopen(url, timeout=120).read()
    got = hashlib.sha256(data).hexdigest()
    if got != want:
        raise SystemExit(f"{url}: sha256 {got}, Cargo.lock says {want}")
    os.makedirs(os.path.join(kit, "std"), exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as t:
        t.extractall(os.path.join(kit, "std"), filter="data") if sys.version_info >= (3, 12) else t.extractall(os.path.join(kit, "std"))
    print(f"downloaded {STD} from crates.io (sha256 {got})", flush=True)
    return d


def main():
    kit = os.path.abspath(sys.argv[1])
    only = set(sys.argv[2:])
    reg_std = ensure_std(kit)
    example = os.path.join(kit, "token", "example-ft")
    env = dict(os.environ)
    harness_target = env.get("CARGO_TARGET_DIR", os.path.join(kit, "harness", "target"))
    env["CARGO_TARGET_DIR"] = os.path.join(harness_target, "token-build")
    results, diffs = [], []
    unexpected = []
    certs_dir = os.path.join(kit, "evidence", "mutants_certificates")
    os.makedirs(certs_dir, exist_ok=True)
    for mid, where, rel, old, new, expect, what in MUTANTS:
        if only and mid not in only:
            continue
        d = os.path.join(kit, "mutants", mid)
        shutil.rmtree(d, ignore_errors=True)
        os.makedirs(d)
        ex = os.path.join(d, "example-ft")
        shutil.copytree(example, ex, ignore=shutil.ignore_patterns("target"))
        if where == "std":
            shutil.copytree(reg_std, os.path.join(d, STD))
            with open(os.path.join(ex, "Cargo.toml"), "a") as f:
                f.write(f'\n[patch.crates-io]\nnear-contract-standards = {{ path = "../{STD}" }}\n')
            target = os.path.join(d, STD, rel)
        else:
            target = os.path.join(ex, rel)
        src = open(target).read()
        if old is not None:
            if src.count(old) != 1:
                results.append({"id": mid, "error": f"pattern occurs {src.count(old)} times"})
                unexpected.append(mid)
                continue
            mut = src.replace(old, new)
            open(target, "w").write(mut)
            diffs.append("".join(difflib.unified_diff(src.splitlines(True), mut.splitlines(True),
                                                      f"a/{where}/{rel}", f"b/{where}/{rel} ({mid})", n=1)))
        os.utime(os.path.join(ex, "src", "lib.rs"))  # never reuse a fresh unit's stale artifact
        b = run(["cargo", "near", "build", "non-reproducible-wasm", "--no-abi", "--out-dir", os.path.join(d, "out")],
                cwd=ex, env=env)
        wasm = os.path.join(d, "out", "fungible_token.wasm")
        if b.returncode != 0 or not os.path.exists(wasm):
            results.append({"id": mid, "error": "build failed", "log": (b.stdout + b.stderr)[-1500:]})
            unexpected.append(mid)
            print(f"{mid}: build failed", flush=True)
            continue
        cenv = dict(env)
        cenv["OUT"] = os.path.join(d, "cert")
        cenv["CARGO_TARGET_DIR"] = harness_target
        c = run([os.path.join(kit, "certify-token.sh"), wasm], cwd=kit, env=cenv)
        cert = json.load(open(os.path.join(d, "cert", "certificate.json")))
        shutil.copyfile(os.path.join(d, "cert", "certificate.json"), os.path.join(certs_dir, mid + ".json"))
        fd = cert.get("first_divergence") or {}
        r = {"id": mid, "mutation": what, "file": f"{where}/{rel}", "expected_property": expect,
             "wasm_sha256": cert["wasm"]["sha256"], "result": cert["result"],
             "failed_properties": cert["failed_properties"],
             "first_divergence": {k: fd.get(k) for k in ("trace", "h", "kind", "property", "method", "pred", "args", "detail")} if fd else None,
             "divergences": cert.get("divergences"), "diverging_traces": cert.get("diverging_traces"),
             "diverging_traces_by_first_property": cert.get("diverging_traces_by_first_property"),
             "monitor_violations": cert.get("monitor_violations"), "reasons": cert["reasons"],
             "kit_output": c.stdout.strip().splitlines()[:3]}
        results.append(r)
        print(f"{mid}: {r['result']} failed={r['failed_properties']} first={fd.get('property')} {fd.get('kind')} "
              f"{fd.get('method')} | expected {expect}", flush=True)
        as_expected = (r["result"] == "PASS") if old is None else (r["result"] == "FAIL" and fd.get("property") == expect)
        if not as_expected:
            unexpected.append(mid)
        # keep the wasm and the certificate, drop the sources' copies
        shutil.rmtree(ex, ignore_errors=True)
        shutil.rmtree(os.path.join(d, STD), ignore_errors=True)
    hashes = [r.get("wasm_sha256") for r in results if r.get("wasm_sha256")]
    if len(hashes) != len(set(hashes)):
        print("FAIL: two mutant builds produced the same wasm (stale build artifact?)")
        unexpected.append("duplicate wasm")
    os.makedirs(os.path.join(kit, "evidence"), exist_ok=True)
    tag = "" if not only else "_partial"
    json.dump(results, open(os.path.join(kit, "evidence", f"mutants{tag}.json"), "w"), indent=1)
    open(os.path.join(kit, "evidence", f"mutants{tag}.diff"), "w").write("\n".join(diffs))
    if unexpected:
        print("FAIL: not as expected:", ", ".join(unexpected))
        return 1
    print(f"mutants: {len(results)} builds, all as expected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
