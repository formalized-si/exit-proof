#!/usr/bin/env bash
# Re-derives wasm/staking_pool.wasm from its public source and verifies it.
#   ./fetch-wasm.sh            download the file from github.com/near/core-contracts at the pinned
#                              commit, check its hash, and compare it with the committed copy
#                              (the copy is created if it is missing)
#   ./fetch-wasm.sh --verify   offline: only check the hash of the committed copy
# Exit status is non-zero on any mismatch. Needs git and python3.
set -euo pipefail
cd "$(dirname "$0")"
REPO=https://github.com/near/core-contracts
COMMIT=1cacc9dbd57db7af2504c181edd707299869bce7
SRC=staking-pool/res/staking_pool.wasm
DST=wasm/staking_pool.wasm
SHA256=fcbcf3f3721d9ca92be6b3ecd109c91909bfc435a969bf4c7c43215be6c4a6b7
CODE_HASH=J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY   # base58 of the sha256: the on-chain code hash

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
check() {  # check FILE LABEL: the file has the pinned hash
  local h; h=$(hashes "$1")
  if [ "$h" != "$SHA256 $CODE_HASH" ]; then echo "FAIL: $2 has hash $h, expected $SHA256 $CODE_HASH"; exit 1; fi
  echo "ok: $2: sha256 $SHA256 = code hash $CODE_HASH"
}

if [ "${1:-}" = "--verify" ]; then check "$DST" "$DST"; exit 0; fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
git -C "$tmp" init -q
git -C "$tmp" fetch -q --depth 1 "$REPO" "$COMMIT"
git -C "$tmp" cat-file blob "FETCH_HEAD:$SRC" > "$tmp/fetched.wasm"
check "$tmp/fetched.wasm" "upstream $SRC"
echo "    source: $REPO commit $COMMIT, $SRC"
mkdir -p "$(dirname "$DST")"
if [ -f "$DST" ]; then
  cmp "$tmp/fetched.wasm" "$DST" || { echo "FAIL: $DST differs from the upstream file"; exit 1; }
  echo "ok: $DST is byte-identical to the upstream file"
else
  cp "$tmp/fetched.wasm" "$DST"; echo "created $DST"
fi
