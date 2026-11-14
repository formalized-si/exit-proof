"""Certificates the on-chain registry holds for a code hash (read-only; no near CLI needed).

usage: registry_get.py <code hash, base58> [--all]
Prints the valid certificates of registry.exitproof.near (NEAR mainnet) for that code hash as JSON: kind, family,
statement, theorem names, axioms, assumptions, binding, conformance counts, the bundle hash of the proof directory
(compare with `python3 tools/bundle_hash.py <directory> --git`) and the re-check command. --all includes revoked ones.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402
import rpc  # noqa: E402

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) != 1:
        sys.exit(__doc__)
    method = "get" if "--all" in sys.argv else "get_valid"
    try:
        ok, v = exitproof.view(exitproof.REGISTRY, method, {"code_hash": args[0]}, eps=rpc.DEFAULT_RPC["mainnet"].split(","))
    except exitproof.RpcUnavailable as e:
        sys.exit(f"the public RPC did not answer ({e}); retry in a minute")
    if not ok:
        sys.exit(f"the registry did not answer: {v}")
    print(json.dumps(v, indent=1))
