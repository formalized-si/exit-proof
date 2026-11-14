"""Attest the certificates in registry/certificates/*.json to the on-chain registry.

usage: NETWORK=mainnet REGISTRY=registry.exitproof.near ATTESTOR=exitproof.near python3 registry/attest.py [name ...] [--dry-run]
For each certificate file the `artifact_sha256` is computed from the proof directory with tools/bundle_hash.py, so
the value stored on chain can be recomputed by anyone from a checkout of the repository. Needs near-cli with
credentials of the attestor. The attached deposit covers storage; the contract refunds the excess.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
from bundle_hash import bundle_hash  # noqa: E402

net, reg, who = os.environ["NETWORK"], os.environ["REGISTRY"], os.environ["ATTESTOR"]
dry = "--dry-run" in sys.argv
names = [a for a in sys.argv[1:] if not a.startswith("--")]
cdir = os.path.join(ROOT, "registry", "certificates")
for fn in sorted(os.listdir(cdir)):
    name = fn[:-5]
    if not fn.endswith(".json") or (names and name not in names):
        continue
    spec = json.load(open(os.path.join(cdir, fn)))
    digest, n = bundle_hash(os.path.join(ROOT, spec["dir"]))
    cert = dict(spec["certificate"])
    cert["artifact_sha256"] = digest
    cert["artifact_location"] = (f"Exit Proof repository, directory {spec['dir']}/ ({n} files); recompute with: "
                                 f"python3 tools/bundle_hash.py {spec['dir']}")
    args = json.dumps({"code_hash": spec["code_hash"], "certificate": cert})
    print(name, spec["code_hash"][:12], cert["kind"], digest, f"{len(args)} bytes")
    if dry:
        continue
    r = subprocess.run(["near", "call", reg, "attest", args, "--accountId", who, "--deposit", "0.08",
                        "--gas", "100000000000000", "--networkId", net], capture_output=True, text=True)
    tail = [l for l in (r.stdout + r.stderr).strip().splitlines() if "Transaction Id" in l or "rror" in l]
    print("  ", r.returncode, tail[-2:])
