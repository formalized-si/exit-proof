#!/bin/bash
# Deploys the stage-1 examples on NEAR testnet: the reference vault of upgrade-window/ (near-plugins v0.5.1
# Upgradable) with a 7-day staging delay, once quiet and once with an upgrade already staged.
#
# usage: PARENT=<funded testnet account whose credentials near-cli has> tools/stage1_demo.sh
# Creates gov.$PARENT (holds the DAO role: the only party that can stage and deploy code),
# quiet-vault.$PARENT and staged-vault.$PARENT (both end up with no access keys). Needs near-cli v4 (and node), and the
# Python package `cryptography`. Key files are written to ~/.near-credentials/testnet/, never printed.
set -euo pipefail
: "${PARENT:?set PARENT to a funded testnet account}"
NET=testnet
DELAY_NS=604800000000000   # 7 days
ROOT=$(cd "$(dirname "$0")/.." && pwd)
W=$ROOT/upgrade-window/contract/out
GOV=gov.$PARENT; QUIET=quiet-vault.$PARENT; STAGED=staged-vault.$PARENT

mkkey() {  # writes a fresh key file for account $1, prints the public key only
python3 - "$1" "$NET" <<'PY'
import json, os, sys
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization as s
A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58(b):
    n = int.from_bytes(b, "big"); out = ""
    while n: n, r = divmod(n, 58); out = A[r] + out
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + out
k = Ed25519PrivateKey.generate()
seed = k.private_bytes(s.Encoding.Raw, s.PrivateFormat.Raw, s.NoEncryption())
pub = k.public_key().public_bytes(s.Encoding.Raw, s.PublicFormat.Raw)
d = os.path.expanduser(f"~/.near-credentials/{sys.argv[2]}"); os.makedirs(d, exist_ok=True)
p = os.path.join(d, sys.argv[1] + ".json")
if os.path.exists(p): sys.exit(f"{p} exists; not overwriting")
fd = os.open(p, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
os.write(fd, json.dumps({"account_id": sys.argv[1], "public_key": "ed25519:" + b58(pub),
                         "private_key": "ed25519:" + b58(seed + pub)}).encode()); os.close(fd)
print("ed25519:" + b58(pub))
PY
}
tx() { grep -E "Transaction Id|rror" | tail -2; }

for pair in "$GOV 0.5" "$QUIET 2.7" "$STAGED 4.9"; do
  set -- $pair
  PK=$(mkkey "$1")
  near create-account "$1" --useAccount "$PARENT" --initialBalance "$2" --publicKey "$PK" --networkId $NET 2>&1 | tx
done
for V in "$QUIET" "$STAGED"; do
  near deploy "$V" "$W/vault_v1.wasm" --initFunction new --initArgs "{\"staging_duration\": $DELAY_NS}" --networkId $NET 2>&1 | tx
  near call "$V" acl_grant_role "{\"role\":\"DAO\",\"account_id\":\"$GOV\"}" --accountId "$V" --networkId $NET 2>&1 | tx
  near call "$V" deposit '{}' --accountId "$GOV" --deposit 0.05 --networkId $NET 2>&1 | tx
  PK=$(python3 -c "import json,os,sys;print(json.load(open(os.path.expanduser('~/.near-credentials/$NET/'+sys.argv[1]+'.json')))['public_key'])" "$V")
  # near-cli asks for confirmation on a terminal; give it one.
  (sleep 2; echo y; sleep 2; echo y; sleep 10) | script -qfc "near delete-key $V $PK --force --networkId $NET" /dev/null | tx
done
# the code is the raw argument of up_stage_code: too long for a command line, so it is sent by a small script
NODE_PATH=$(npm root -g)/near-cli/node_modules node "$ROOT/tools/stage_code.js" "$STAGED" "$GOV" "$W/vault_v2.wasm" $NET 2>&1 | tx
sleep 3
for V in "$QUIET" "$STAGED"; do near list-keys "$V" --networkId $NET | tail -1; done
