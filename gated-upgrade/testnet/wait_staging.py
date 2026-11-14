"""Waits until the final block's timestamp has passed the vault's staging timestamp.

usage: python3 testnet/wait_staging.py <vault account> [extra seconds = 5]
Prints the staging timestamp, and the block timestamp it stopped at.
"""
import base64
import json
import sys
import time
import urllib.request

RPC = "https://rpc.testnet.fastnear.com"


def post(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
    for i in range(8):
        try:
            req = urllib.request.Request(RPC, body, {"Content-Type": "application/json", "User-Agent": "read-only"})
            j = json.loads(urllib.request.urlopen(req, timeout=30).read())
            if "result" in j:
                return j["result"]
        except Exception:
            pass
        time.sleep(1 + i)
    sys.exit("the RPC does not answer")


vault = sys.argv[1]
extra = int(sys.argv[2]) if len(sys.argv) > 2 else 5
r = post("query", {"request_type": "call_function", "finality": "final", "account_id": vault,
                   "method_name": "up_get_delay_status", "args_base64": base64.b64encode(b"{}").decode()})
ts = json.loads(bytes(r["result"]).decode())["staging_timestamp"]
if ts is None:
    sys.exit("nothing is staged")
print("staging timestamp:", ts)
while True:
    now = post("block", {"finality": "final"})["header"]["timestamp"]
    if now >= ts + extra * 10**9:
        print("final block timestamp:", now, f"({(now - ts) / 1e9:.1f} s after the staging timestamp)")
        break
    time.sleep(min(20, max(2, (ts + extra * 10**9 - now) / 1e9)))
