#!/usr/bin/env python3
"""Read-only archival lookup: the block where wrap.near's last access key disappeared, the
transaction that removed it, and the code hash around it. usage: keys_history.py LO HI"""
import json, sys, time, urllib.request

URL = "https://archival-rpc.mainnet.fastnear.com"
ACC = "wrap.near"

def rpc(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
    for _ in range(6):
        try:
            j = json.loads(urllib.request.urlopen(urllib.request.Request(URL, body, {"Content-Type": "application/json"}), timeout=60).read())
            if "result" in j:
                return j["result"]
            if "UNKNOWN_BLOCK" in json.dumps(j.get("error")):
                return None
            time.sleep(2)
        except Exception:
            time.sleep(2)
    return None

def keys_at(h):
    r = rpc("query", {"request_type": "view_access_key_list", "block_id": h, "account_id": ACC})
    return None if r is None else [(k["public_key"], "FullAccess" if k["access_key"]["permission"] == "FullAccess" else "FunctionCall") for k in r["keys"]]

def code_at(h):
    r = rpc("query", {"request_type": "view_account", "block_id": h, "account_id": ACC})
    return None if r is None else r["code_hash"]

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])   # keys(lo) nonempty, keys(hi) empty
    out = {"keys_at_lo": keys_at(lo), "keys_at_hi": keys_at(hi)}
    while hi - lo > 1:
        mid = (lo + hi) // 2
        k = keys_at(mid); n = 0
        while k is None and n < 20:
            mid += 1; k = keys_at(mid); n += 1
        if k is None: break
        if k and mid < hi: lo = mid
        else: hi = mid
    out.update({"last_with_keys": lo, "first_without_keys": hi, "keys_before": keys_at(lo),
                "code_before": code_at(lo), "code_after": code_at(hi)})
    txs = []
    for h in (hi, hi - 1):
        b = rpc("block", {"block_id": h})
        for ch in (b or {}).get("chunks", []):
            c = rpc("chunk", {"chunk_id": ch["chunk_hash"]})
            for t in (c or {}).get("transactions", []):
                if t["receiver_id"] == ACC or t["signer_id"] == ACC:
                    txs.append({"block": h, "hash": t["hash"], "signer": t["signer_id"], "receiver": t["receiver_id"],
                                "actions": [a if isinstance(a, str) else list(a.keys())[0] for a in t["actions"]]})
    out["txs"] = txs
    print(json.dumps(out, indent=1))

if __name__ == "__main__":
    main()
