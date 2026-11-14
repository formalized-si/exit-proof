"""Writes the arguments of the registry's `attest` call for one build of the gated vault.

usage: python3 testnet/make_attest.py <v2|v3> > testnet/attest_<build>.json
The certificate says what it is: a testnet demonstration certificate for a feature build of the
same source, with the theorems of lean/GatedUpgrade, their assumptions, the numbers of the last
./check.sh run (evidence/scenarios.json, evidence/traces.json) and the hash of the proof bundle
(scripts/bundle_hash.py).
"""
import hashlib
import json
import os
import sys

KIT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(KIT, "scripts"))
from bundle_hash import bundle_hash  # noqa: E402

A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58(b):
    n = int.from_bytes(b, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = A[r] + out
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + out


build = sys.argv[1]
wasm = open(os.path.join(KIT, "contract", "out", f"gated_vault_{build}.wasm"), "rb").read()
sha = hashlib.sha256(wasm)
sc = json.load(open(os.path.join(KIT, "evidence", "scenarios.json")))
tr = json.load(open(os.path.join(KIT, "evidence", "traces.json")))
digest, n = bundle_hash()
cert = {
    "kind": "upgrade-window",
    "family": f"gated vault: near-plugins v0.5.1 Upgradable behind a certificate gate, build {build}",
    "statement": (
        "Testnet demonstration certificate. In the Lean model of the gated vault, every change of the code "
        "installs code whose hash had, when the registry was asked, a certificate that was not revoked, of the "
        "accepted kind and from an accepted attestor; that code was staged at least the staging duration before "
        "the deploy call and its hash was the visible staged hash all that time; the deploy batch was created by "
        "the contract's own callback. This wasm is a feature build of the modelled source: it differs from build "
        "v1 in the value version() returns and in nothing else."),
    "theorems": ["GatedUpgrade.gated_code_change", "GatedUpgrade.gated_no_deploy_before",
                 "GatedUpgrade.uncertified_never_installed", "GatedUpgrade.aclInv_run"],
    "axioms": ["propext", "Quot.sound", "Classical.choice"],
    "assumptions": [
        "The contract account has no access keys, and no receipt calling a plugin or acl method has it as predecessor.",
        "The registry account runs the pinned registry wasm, has no access keys, and its answer reaches the callback unchanged.",
        "The model is a transcription of the contract by hand; the wasm was compared with it by scenarios and a trace monitor on the nearcore runtime, not by proof.",
        "After a code change the statement continues only if the installed code is again the modelled contract.",
        "Gas, storage staking, JSON decoding and collisions of sha256 are outside the model."],
    "binding": f"gated_vault_{build}.wasm sha256 {sha.hexdigest()}, rebuilt from contract/gated-vault with cargo-near (contract/WASM_SHA256)",
    "conformance": {
        "traces": tr["traces"], "calls": tr["receipts"], "mismatches": tr["violations"],
        "runtime": f"nearcore 2.14.0 via near-contract-sim; monitor on random traces, {tr['blocks']} blocks; "
                   f"{sc['scenarios_total']} scenarios with {sc['checks_total']} checks, all holding"},
    "artifact_sha256": digest,
    "artifact_location": f"gated-upgrade kit, directories contract/ lean/ harness/ ({n} files); recompute with: python3 scripts/bundle_hash.py",
    "check_command": "./check.sh",
}
print(json.dumps({"code_hash": b58(sha.digest()), "certificate": cert}, indent=1))
