#!/usr/bin/env python3
"""fetch_code.py ACCOUNT OUT.wasm [--sha256 HEX] [--rpc URL]

Downloads the contract code of a NEAR mainnet account with one read-only RPC query (view_code at
the final block) and writes it to OUT.wasm. Signs nothing and sends no transaction. With --sha256
the file is written only if the code has that hash. Prints the sha256 and the NEAR code hash.
The RPC endpoint: --rpc, or the environment variable NEAR_RPC_URL, or a public mainnet endpoint.
Exit status: 0 written, 1 the query failed or the hash differs.
"""
import base64
import json
import os
import sys
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kitlib  # noqa: E402

DEFAULT_RPCS = ["https://rpc.mainnet.fastnear.com", "https://free.rpc.fastnear.com", "https://rpc.mainnet.near.org"]


def view_code(account, rpcs):
    last = "no endpoint"
    body = json.dumps({"jsonrpc": "2.0", "id": "1", "method": "query",
                       "params": {"request_type": "view_code", "finality": "final", "account_id": account}}).encode()
    for url in rpcs:
        try:
            req = urllib.request.Request(url, body, {"Content-Type": "application/json", "User-Agent": "token-monitors"})
            with urllib.request.urlopen(req, timeout=60) as r:
                j = json.load(r)
            if "result" in j and "code_base64" in j["result"]:
                return base64.b64decode(j["result"]["code_base64"])
            last = f"{url}: {json.dumps(j.get('error') or j.get('result'))[:300]}"
        except Exception as e:  # noqa: BLE001 - any transport problem: try the next endpoint
            last = f"{url}: {e!r}"
    raise RuntimeError(last)


def main():
    argv = sys.argv[1:]
    want = rpc = None
    pos = []
    i = 0
    while i < len(argv):
        if argv[i] == "--sha256" and i + 1 < len(argv):
            want = argv[i + 1].lower(); i += 2
        elif argv[i] == "--rpc" and i + 1 < len(argv):
            rpc = argv[i + 1]; i += 2
        else:
            pos.append(argv[i]); i += 1
    if len(pos) != 2:
        print(__doc__); return 1
    account, out = pos
    rpcs = [rpc] if rpc else ([os.environ["NEAR_RPC_URL"]] if os.environ.get("NEAR_RPC_URL") else DEFAULT_RPCS)
    try:
        code = view_code(account, rpcs)
    except RuntimeError as e:
        print(f"view_code of {account} failed: {e}", file=sys.stderr); return 1
    got = kitlib.sha256_bytes(code)
    if want and got != want:
        print(f"{account}: the code has sha256 {got}, expected {want} (the account's code changed, or the hash is wrong)",
              file=sys.stderr)
        return 1
    with open(out, "wb") as f:
        f.write(code)
    print(f"{account}: {len(code)} bytes, sha256 {got}, NEAR code hash {kitlib.near_code_hash(code)} -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
