#!/usr/bin/env python3
"""Read-only mainnet check of wrap.near's solvency at ONE block (no keys, no transactions).

Checks the hypothesis of `WNear.solvent_of_stake_bound`:
    total_supply + 2 * storage_usage * storage_amount_per_byte <= account balance
which implies the solvency part of `Inv` (supply + accounts * minBal + base <= balance),
because every account entry is >= 63 bytes and minBal is 125 bytes.
usage: mainnet_check.py [WASM_PATH]  -> JSON on stdout
"""
import base64, json, sys, time, urllib.request

EPS = ["https://rpc.mainnet.fastnear.com", "https://free.rpc.fastnear.com", "https://rpc.mainnet.near.org"]
ACC = "wrap.near"

def rpc(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
    last = None
    for _ in range(3):
        for url in EPS:
            try:
                r = urllib.request.urlopen(urllib.request.Request(url, body, {"Content-Type": "application/json"}), timeout=30)
                j = json.loads(r.read())
                if "result" in j:
                    return j["result"]
                last = j
            except Exception as e:
                last = str(e)
            time.sleep(1)
    raise RuntimeError(f"{method}: {last}")

def view(h, m, args):
    r = rpc("query", {"request_type": "call_function", "block_id": h, "account_id": ACC,
                      "method_name": m, "args_base64": base64.b64encode(json.dumps(args).encode()).decode()})
    return json.loads(bytes(r["result"]).decode())

def main():
    blk = rpc("block", {"finality": "final"})
    h = blk["header"]["height"]
    acct = rpc("query", {"request_type": "view_account", "block_id": h, "account_id": ACC})
    keys = rpc("query", {"request_type": "view_access_key_list", "block_id": h, "account_id": ACC})
    cfg = rpc("EXPERIMENTAL_protocol_config", {"block_id": h})
    byte = int(cfg["runtime_config"]["storage_amount_per_byte"])
    supply = int(view(h, "ft_total_supply", {}))
    bounds = view(h, "storage_balance_bounds", {})
    own = int(view(h, "ft_balance_of", {"account_id": ACC}))
    amount, usage = int(acct["amount"]), int(acct["storage_usage"])
    code_len = len(open(sys.argv[1], "rb").read()) if len(sys.argv) > 1 else None
    stake = usage * byte
    minbal = int(bounds["min"])
    n_max = (usage - (code_len or 0)) // 63
    out = {
        "block_height": h, "block_hash": blk["header"]["hash"],
        "code_hash": acct["code_hash"], "access_keys": len(keys["keys"]), "locked": acct["locked"],
        "amount_yocto": str(amount), "total_supply_yocto": str(supply),
        "storage_usage_bytes": usage, "storage_amount_per_byte": str(byte),
        "storage_stake_yocto": str(stake), "storage_min_balance_yocto": str(minbal),
        "surplus_yocto": str(amount - supply),
        "hypothesis_supply_plus_2stake_le_amount": supply + 2 * stake <= amount,
        "margin_yocto": str(amount - supply - 2 * stake),
        "registered_accounts_upper_bound": n_max,
        "wnear_held_by_wrap_near_itself_yocto": str(own),
        "minbal_le_2x63_bytes": minbal <= 2 * 63 * byte,
        "minbal_is_125_bytes": minbal == 125 * byte,
    }
    print(json.dumps(out, indent=1))

if __name__ == "__main__":
    main()
