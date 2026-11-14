#!/usr/bin/env python3
"""Read-only archival lookup: when did wrap.near's code become DL2f5…, which transaction did
it, and was the contract state fresh afterwards? usage: history_check.py LO HI"""
import base64, json, sys, time, urllib.request

URL = "https://archival-rpc.mainnet.fastnear.com"
ACC = "wrap.near"
NEW = "DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1"

def rpc(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
    for _ in range(6):
        try:
            j = json.loads(urllib.request.urlopen(urllib.request.Request(URL, body, {"Content-Type": "application/json"}), timeout=60).read())
            if "result" in j:
                return j["result"]
            err = j.get("error")
            if "UNKNOWN_BLOCK" in json.dumps(err) or "GARBAGE" in json.dumps(err):
                return None
            time.sleep(2)
        except Exception:
            time.sleep(2)
    return None

def code_at(h):
    r = rpc("query", {"request_type": "view_account", "block_id": h, "account_id": ACC})
    return None if r is None else (r["code_hash"], r["storage_usage"], r["amount"])

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])   # code(lo) != NEW, code(hi) == NEW
    while hi - lo > 1:
        mid = (lo + hi) // 2
        c = code_at(mid)
        while c is None:          # skipped height: move up
            mid += 1; c = code_at(mid)
            if mid >= hi: break
        if c is not None and c[0] == NEW and mid < hi: hi = mid
        else: lo = mid
    out = {"last_old_height": lo, "first_new_height": hi, "before": code_at(lo), "after": code_at(hi)}
    blk = rpc("block", {"block_id": hi})
    txs = []
    for ch in blk["chunks"]:
        c = rpc("chunk", {"chunk_id": ch["chunk_hash"]})
        for t in (c or {}).get("transactions", []):
            if t["receiver_id"] == ACC or t["signer_id"] == ACC:
                txs.append({"hash": t["hash"], "signer": t["signer_id"], "receiver": t["receiver_id"],
                            "actions": [a if isinstance(a, str) else list(a.keys())[0] +
                                        (":" + a.get("FunctionCall", {}).get("method_name", "") if "FunctionCall" in a else "")
                                        for a in t["actions"]]})
    # the deploy may be in the previous block's chunks (tx included one block before it executes)
    if not txs:
        prev = rpc("block", {"block_id": hi - 1})
        for ch in prev["chunks"]:
            c = rpc("chunk", {"chunk_id": ch["chunk_hash"]})
            for t in (c or {}).get("transactions", []):
                if t["receiver_id"] == ACC or t["signer_id"] == ACC:
                    txs.append({"hash": t["hash"], "signer": t["signer_id"], "receiver": t["receiver_id"],
                                "actions": [a if isinstance(a, str) else list(a.keys())[0] +
                                            (":" + a.get("FunctionCall", {}).get("method_name", "") if "FunctionCall" in a else "")
                                            for a in t["actions"]]})
    out["txs"] = txs
    for t in txs:
        st = rpc("EXPERIMENTAL_tx_status", {"tx_hash": t["hash"], "sender_account_id": t["signer"], "wait_until": "NONE"})
        if st:
            t["status"] = list(st["status"].keys())[0]
            t["receipt_logs"] = [l for ro in st.get("receipts_outcome", []) for l in ro["outcome"]["logs"]][:10]
            t["receipt_statuses"] = [json.dumps(ro["outcome"]["status"])[:160] for ro in st.get("receipts_outcome", [])]
    # state right after: supply and a STATE read
    def view(h, m):
        r = rpc("query", {"request_type": "call_function", "block_id": h, "account_id": ACC, "method_name": m,
                          "args_base64": base64.b64encode(b"{}").decode()})
        return None if r is None or "result" not in r else bytes(r["result"]).decode()
    out["ft_total_supply_after"] = view(hi, "ft_total_supply")
    out["ft_total_supply_+10"] = view(hi + 10, "ft_total_supply")
    print(json.dumps(out, indent=1))

if __name__ == "__main__":
    main()
