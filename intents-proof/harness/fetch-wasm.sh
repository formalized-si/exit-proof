#!/bin/bash
# fetch-wasm.sh [account] [out.wasm]
# Read-only: asks a public RPC for the code deployed at an account (query view_code, finality final),
# decodes it and prints its sha256 in hex and base58 (NEAR's code hash). No keys, no transactions.
set -euo pipefail
ACC=${1:-intents.near}
OUT=${2:-$(cd "$(dirname "$0")" && pwd)/wasm/intents.wasm}
EXPECT=${EXPECT:-BtA1BEFNS619KkvXFsgcpQ21Tb5yMm32aaUkn7xNothk}
mkdir -p "$(dirname "$OUT")"
TMP=$(mktemp)
trap 'rm -f "$TMP"' EXIT
ok=0
for RPC in ${RPCS:-https://rpc.mainnet.fastnear.com https://free.rpc.fastnear.com https://rpc.mainnet.near.org}; do
  if curl -sS --max-time 120 -H 'Content-Type: application/json' -A 'wasm-fetch/1.0' "$RPC" \
      -d "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"query\",\"params\":{\"request_type\":\"view_code\",\"finality\":\"final\",\"account_id\":\"$ACC\"}}" > "$TMP" \
     && python3 -I - "$TMP" "$OUT" "$RPC" <<'PY'
import base64, hashlib, json, sys
j = json.load(open(sys.argv[1]))
r = j.get("result")
if not r or "code_base64" not in r:
    print("no code from", sys.argv[3], str(j)[:200], file=sys.stderr); sys.exit(1)
code = base64.b64decode(r["code_base64"])
open(sys.argv[2], "wb").write(code)
AL = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
d = hashlib.sha256(code).digest()
n = int.from_bytes(d, "big"); s = ""
while n: n, m = divmod(n, 58); s = AL[m] + s
s = "1" * (len(d) - len(d.lstrip(b"\0"))) + s
print(json.dumps({"rpc": sys.argv[3], "bytes": len(code), "sha256": d.hex(), "base58": s,
                  "rpc_hash": r.get("hash"), "block_height": r.get("block_height"), "block_hash": r.get("block_hash")}))
PY
  then ok=1; break; fi
done
[ "$ok" = 1 ] || { echo "FAIL: no RPC returned the code"; exit 1; }
GOT=$(python3 -I - "$OUT" <<'PY'
import hashlib, sys
AL = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
d = hashlib.sha256(open(sys.argv[1], "rb").read()).digest()
n = int.from_bytes(d, "big"); s = ""
while n: n, m = divmod(n, 58); s = AL[m] + s
print("1" * (len(d) - len(d.lstrip(b"\0"))) + s)
PY
)
if [ "$GOT" = "$EXPECT" ]; then echo "OK: $OUT has code hash $GOT"; else echo "FAIL: code hash $GOT, expected $EXPECT"; exit 1; fi
