#!/usr/bin/env bash
# Re-derives the wasm inputs from their public sources and verifies them.
#   ./fetch-wasm.sh            download wasm/w_near.wasm from github.com/near/core-contracts at the
#                              pinned commit, check its hash, compare it with the committed copy
#                              (created if missing); check the hash of the committed pre-upgrade code
#   ./fetch-wasm.sh --old      also download the pre-upgrade code of wrap.near from a NEAR archival
#                              RPC node (view_code at the last block before the upgrade) and compare
#   ./fetch-wasm.sh --verify   offline: only check the hashes of the committed copies
# Exit status is non-zero on any mismatch. Needs git and python3.
set -euo pipefail
cd "$(dirname "$0")"
REPO=https://github.com/near/core-contracts
COMMIT=54f8267436058567b66efdaba3e790394f7f1529
SRC=w-near/res/w_near.wasm
DST=wasm/w_near.wasm
SHA256=b72c26d390b23f4517d091a8aab06b0369d465356ec5fb337d5fda076da38ac0
CODE_HASH=DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1   # base58 of the sha256: the on-chain code hash
# the code wrap.near ran before block 35438886 (not in a public git repository: taken from the chain)
OLD_DST=evidence/old_9kQaNisc.wasm
OLD_CODE_HASH=9kQaNiscuPh69vRs1GyzfnkEjpUPGLjJhT6RaJBQyG7p
OLD_LAST_BLOCK=35438885
ARCHIVAL_RPC="${ARCHIVAL_RPC:-https://archival-rpc.mainnet.fastnear.com}"

hashes() {  # prints "<sha256 hex> <base58 of the sha256>"
  python3 -I -c '
import hashlib, sys
d = hashlib.sha256(open(sys.argv[1], "rb").read()).digest()
A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
n, s = int.from_bytes(d, "big"), ""
while n:
    n, r = divmod(n, 58)
    s = A[r] + s
print(d.hex(), "1" * (len(d) - len(d.lstrip(b"\0"))) + s)' "$1"
}
check() {  # check FILE LABEL EXPECTED_CODE_HASH [EXPECTED_SHA256]
  local h; h=$(hashes "$1")
  if [ "${h#* }" != "$3" ] || { [ -n "${4:-}" ] && [ "${h% *}" != "$4" ]; }; then
    echo "FAIL: $2 has hash $h, expected ${4:-} $3"; exit 1
  fi
  echo "ok: $2: sha256 ${h% *} = code hash $3"
}

if [ "${1:-}" = "--verify" ]; then
  check "$DST" "$DST" "$CODE_HASH" "$SHA256"; check "$OLD_DST" "$OLD_DST" "$OLD_CODE_HASH"; exit 0
fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
git -C "$tmp" init -q
git -C "$tmp" fetch -q --depth 1 "$REPO" "$COMMIT"
git -C "$tmp" cat-file blob "FETCH_HEAD:$SRC" > "$tmp/fetched.wasm"
check "$tmp/fetched.wasm" "upstream $SRC" "$CODE_HASH" "$SHA256"
echo "    source: $REPO commit $COMMIT, $SRC"
mkdir -p "$(dirname "$DST")"
if [ -f "$DST" ]; then
  cmp "$tmp/fetched.wasm" "$DST" || { echo "FAIL: $DST differs from the upstream file"; exit 1; }
  echo "ok: $DST is byte-identical to the upstream file"
else
  cp "$tmp/fetched.wasm" "$DST"; echo "created $DST"
fi
check "$OLD_DST" "$OLD_DST" "$OLD_CODE_HASH"
if [ "${1:-}" = "--old" ]; then
  python3 -I - "$ARCHIVAL_RPC" "$OLD_LAST_BLOCK" "$tmp/old.wasm" <<'PY'
import base64, json, sys, urllib.request
url, block, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": "query",
                   "params": {"request_type": "view_code", "block_id": block, "account_id": "wrap.near"}}).encode()
req = urllib.request.Request(url, body, {"Content-Type": "application/json"})
res = json.loads(urllib.request.urlopen(req, timeout=120).read())
if "result" not in res:
    sys.exit(f"FAIL: archival RPC: {json.dumps(res)[:300]}")
open(out, "wb").write(base64.b64decode(res["result"]["code_base64"]))
PY
  check "$tmp/old.wasm" "wrap.near code at block $OLD_LAST_BLOCK (archival RPC)" "$OLD_CODE_HASH"
  cmp "$tmp/old.wasm" "$OLD_DST" || { echo "FAIL: $OLD_DST differs from the on-chain code"; exit 1; }
  echo "ok: $OLD_DST is byte-identical to the on-chain code at block $OLD_LAST_BLOCK"
fi
