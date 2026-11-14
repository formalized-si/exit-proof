"""Reads the testnet example back from the chain (read-only JSON-RPC, no keys).

usage: python3 testnet/read.py <vault account> [<registry account>]
Prints, for the final block: the vault's code hash and its access keys, version(), gate(),
up_get_delay_status(), up_staged_code_hash(), the access-control state, and — for the registry
named by gate() — its code hash, its access keys, and get_valid_kind for the vault's code hash
and for the staged hash.  --json prints one JSON object instead.
"""
import base64
import json
import os
import sys
import time
import urllib.request

RPCS = os.environ.get("NEAR_TESTNET_RPC", "https://rpc.testnet.fastnear.com,https://test.rpc.fastnear.com").split(",")
A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58decode(s):
    n = 0
    for ch in s:
        n = n * 58 + A.index(ch)
    return n.to_bytes(32, "big")


def rpc(params):
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": "query", "params": params}).encode()
    err = None
    for i in range(8):
        try:
            req = urllib.request.Request(RPCS[i % len(RPCS)], body, {"Content-Type": "application/json", "User-Agent": "read-only"})
            j = json.loads(urllib.request.urlopen(req, timeout=30).read())
            if "result" in j and "error" not in j["result"]:
                return j["result"]
            err = json.dumps(j.get("error") or j["result"].get("error"))[:300]
            if "does not exist" in err or "MethodNotFound" in err or "UNKNOWN_ACCOUNT" in err:
                return {"error": err}
        except Exception as e:  # transport: try again
            err = str(e)[:200]
        time.sleep(0.5 * (i + 1))
    return {"error": err}


def view(account, method, args):
    r = rpc({"request_type": "call_function", "finality": "final", "account_id": account, "method_name": method,
             "args_base64": base64.b64encode(json.dumps(args).encode()).decode()})
    if "error" in r:
        return {"error": r["error"]}
    return json.loads(bytes(r["result"]).decode())


def account(name):
    a = rpc({"request_type": "view_account", "finality": "final", "account_id": name})
    k = rpc({"request_type": "view_access_key_list", "finality": "final", "account_id": name})
    if "error" in a:
        return a
    return {"code_hash": a["code_hash"], "code_sha256": b58decode(a["code_hash"]).hex(), "balance_near": int(a["amount"]) / 1e24,
            "storage_bytes": a["storage_usage"], "access_keys": len(k.get("keys", [])) if "error" not in k else k,
            "block_height": a["block_height"]}


vault = sys.argv[1]
out = {"vault": vault, "account": account(vault)}
for m in ("version", "gate", "up_get_delay_status", "up_staged_code_hash", "acl_get_permissioned_accounts"):
    out[m] = view(vault, m, {})
out["balance_of_depositor"] = None
gate = out["gate"] if isinstance(out["gate"], dict) and "registry" in out["gate"] else {}
registry = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else gate.get("registry")
if registry:
    out["registry"] = {"account_id": registry, "account": account(registry), "attestors": view(registry, "attestors", {}),
                       "owner": view(registry, "owner", {}), "count": view(registry, "count", {})}
    kind = gate.get("kind", "upgrade-window")

    def certs(h):
        v = view(registry, "get_valid_kind", {"code_hash": h, "kind": kind})
        if isinstance(v, list):
            return [{"attestor": c["attestor"], "kind": c["body"]["kind"], "revoked": c["revoked"], "code_hash": c["code_hash"]} for c in v]
        return v
    if "code_hash" in out["account"]:
        out["registry"]["valid_certificates_for_running_code"] = certs(out["account"]["code_hash"])
    if isinstance(out["up_staged_code_hash"], str):
        out["registry"]["valid_certificates_for_staged_code"] = certs(out["up_staged_code_hash"])
del out["balance_of_depositor"]
if "--json" in sys.argv:
    print(json.dumps(out))
else:
    print(json.dumps(out, indent=1))
