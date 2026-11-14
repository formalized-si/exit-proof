"""Reads the testnet example back from the chain (read-only RPC, no keys) and compares it with
what TESTNET.md says.

usage: python3 testnet/verify.py            (also: ./check.sh --testnet)
Checks, at the final block:
  * every transaction of testnet/tx.jsonl still has the recorded final result (and, for a failure,
    the recorded panic text);
  * scenario 1: the deploy_certified transaction succeeded and one of its receipts is a batch
    [DeployContract, FunctionCall(up_verify_state)] on the vault, sent by the vault itself; the
    early one failed with "Gate: deploy too early";
  * scenario 2: deploy_certified failed with "Gate: no valid upgrade-window certificate", the
    stager's up_deploy_code failed with "Insufficient permissions", and neither has a DeployContract receipt;
  * the vault: code = the pinned v2 build, no access keys, version() = 2, the gate, the delay,
    the roles, the v3 build staged;
  * the registry: code = the pinned registry build (the mainnet registry's wasm), no access keys,
    exactly one valid upgrade-window certificate for the running code, by the accepted attestor,
    with artifact_sha256 = the hash of this kit's proof bundle; none for the staged code.
Exit status 0 only if all of it holds. Transactions older than a few days may be gone from
non-archival RPC nodes; then the first check fails and says so.
"""
import base64
import hashlib
import json
import os
import subprocess
import sys
import time
import urllib.request

KIT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RPCS = os.environ.get("NEAR_TESTNET_RPC", "https://rpc.testnet.fastnear.com,https://test.rpc.fastnear.com").split(",")
A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
bad = []


def b58(b):
    n = int.from_bytes(b, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = A[r] + out
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + out


def post(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
    err = None
    for i in range(8):
        try:
            req = urllib.request.Request(RPCS[i % len(RPCS)], body, {"Content-Type": "application/json", "User-Agent": "read-only"})
            j = json.loads(urllib.request.urlopen(req, timeout=40).read())
            if "result" in j:
                return j["result"]
            err = json.dumps(j.get("error"))[:200]
        except Exception as e:
            err = str(e)[:200]
        time.sleep(1 + i)
    return {"rpc_error": err}


def failure_text(status):
    if "SuccessValue" in status or "SuccessReceiptId" in status:
        return None
    s = json.dumps(status)
    i = s.find('"ExecutionError": "')
    return s[i + 19:i + 400] if i >= 0 else s[:400]


def check(what, ok):
    print(("ok   " if ok else "FAIL ") + what)
    if not ok:
        bad.append(what)


def wasm_sha(name):
    return hashlib.sha256(open(os.path.join(KIT, "contract", "out", name), "rb").read())


txs = [json.loads(l) for l in open(os.path.join(KIT, "testnet", "tx.jsonl")) if l.strip()]
vault = next(t["receiver"] for t in txs if t.get("method") == "deploy_certified")
parent = vault.split(".", 1)[1]
registry, attestor, gov = f"registry.{parent}", f"attestor.{parent}", f"gov.{parent}"
seen = {}
for t in txs:
    r = post("EXPERIMENTAL_tx_status", {"tx_hash": t["tx"], "sender_account_id": t["signer"], "wait_until": "FINAL"})
    if "rpc_error" in r:
        check(f"{t['label']} — {t['tx']}: the RPC knows the transaction ({r['rpc_error']})", False)
        continue
    f = failure_text(r["status"])
    same = (f is None) == (t["result"] == "success") and (f is None or t.get("failure", "")[:60] in f.replace('\\"', '"'))
    check(f"{t['label']} — {t['tx']}: {t['result']}" + (f" ({t.get('failure', '')[:90]})" if f else ""), same)
    deploys = [x for x in r.get("receipts", []) if x["receiver_id"] == vault and "Action" in x["receipt"]
               and any("DeployContract" in a for a in x["receipt"]["Action"]["actions"] if isinstance(a, dict))]
    ok_ids = {o["id"] for o in r["receipts_outcome"] if failure_text(o["outcome"]["status"]) is None}
    seen[t["label"]] = {"failure": f, "deploys": [(x["predecessor_id"], x["receipt_id"] in ok_ids,
                                                   [list(a)[0] if isinstance(a, dict) else a for a in x["receipt"]["Action"]["actions"]]) for x in deploys]}


def one(prefix):
    ks = [k for k in seen if k.startswith(prefix)]
    return seen[ks[-1]] if ks else {"failure": "no such transaction recorded", "deploys": []}


s = one("scenario 1: deploy_certified after the delay")
check("scenario 1: deploy_certified after the delay succeeded with a batch [DeployContract, FunctionCall] on the vault, sent by the vault, that succeeded",
      s["failure"] is None and s["deploys"] == [(vault, True, ["DeployContract", "FunctionCall"])])
s = one("scenario 1: deploy_certified before the delay")
check("scenario 1: deploy_certified before the delay failed with 'Gate: deploy too early' and deployed nothing",
      s["failure"] is not None and "Gate: deploy too early" in s["failure"] and not s["deploys"])
s = one("scenario 2: deploy_certified after the delay")
check("scenario 2: deploy_certified for the uncertified code failed with 'Gate: no valid upgrade-window certificate' and deployed nothing",
      s["failure"] is not None and "Gate: no valid upgrade-window certificate" in s["failure"] and not s["deploys"])
s = one("scenario 2: up_deploy_code by the stager")
check("scenario 2: up_deploy_code by the stager failed with 'Insufficient permissions' and deployed nothing",
      s["failure"] is not None and "Insufficient permissions" in s["failure"] and not s["deploys"])

st = json.loads(subprocess.run([sys.executable, "-I", os.path.join(KIT, "testnet", "read.py"), vault, "--json"],
                               capture_output=True, text=True).stdout)
v2, v3 = wasm_sha("gated_vault_v2.wasm"), wasm_sha("gated_vault_v3.wasm")
check(f"the vault runs the pinned v2 build ({v2.hexdigest()[:16]}…) and version() = 2",
      st["account"].get("code_sha256") == v2.hexdigest() and st["version"] == 2)
check("the vault has no access keys", st["account"].get("access_keys") == 0)
check("the gate: that registry, kind upgrade-window, that attestor",
      st["gate"] == {"registry": registry, "kind": "upgrade-window", "attestors": [attestor]})
d = st["up_get_delay_status"]
check("the delay: a staging duration of 180 s, no duration update staged",
      d.get("staging_duration") == 180000000000 and d.get("new_staging_duration") is None)
check("staged and not deployed: the v3 build", st["up_staged_code_hash"] == b58(v3.digest()))
acl = st["acl_get_permissioned_accounts"]
roles = {k: (sorted(v["admins"]), sorted(v["grantees"])) for k, v in acl.get("roles", {}).items()}
check("the roles: the vault is the only super-admin and code deployer, gov the code stager, nobody a duration manager, no admins",
      acl.get("super_admins") == [vault] and roles == {"CodeDeployer": ([], [vault]), "CodeStager": ([], [gov]), "DurationManager": ([], [])})
reg = st.get("registry", {})
pinned = open(os.path.join(KIT, "contract", "REGISTRY_MAINNET_SHA256")).read().strip()
check(f"the registry runs the wasm recorded for the mainnet registry ({pinned[:16]}…) and has no access keys",
      reg.get("account", {}).get("code_sha256") == pinned and reg.get("account", {}).get("access_keys") == 0)
cs = reg.get("valid_certificates_for_running_code")
check("the registry holds exactly one valid upgrade-window certificate for the running code, by the accepted attestor",
      isinstance(cs, list) and len(cs) == 1 and cs[0]["attestor"] == attestor and cs[0]["kind"] == "upgrade-window")
check("the registry holds no valid upgrade-window certificate for the staged code", reg.get("valid_certificates_for_staged_code") == [])
full = post("query", {"request_type": "call_function", "finality": "final", "account_id": registry, "method_name": "get_valid_kind",
                      "args_base64": base64.b64encode(json.dumps({"code_hash": b58(v2.digest()), "kind": "upgrade-window"}).encode()).decode()})
try:
    onchain = json.loads(bytes(full["result"]).decode())[0]["body"]["artifact_sha256"]
except Exception:
    onchain = None
now = subprocess.run([sys.executable, "-I", os.path.join(KIT, "scripts", "bundle_hash.py")], capture_output=True, text=True).stdout.split()[0]
check(f"the certificate's artifact_sha256 is the hash of this kit's proof bundle ({now[:16]}…)", onchain == now)
print("RESULT:", "the chain shows what TESTNET.md says" if not bad else f"{len(bad)} check(s) failed")
sys.exit(1 if bad else 0)
