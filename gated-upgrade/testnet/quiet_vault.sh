#!/usr/bin/env bash
# A second example on testnet: a gated vault with nothing staged and a staging delay of seven days. A scanner reads
# it as stage 1 with certified upgrades only; the first example was left with uncertified code staged past its
# delay, which is stage 0. TESTNET ONLY.
#   VAULT (default gated-quiet-vault.testnet) is a new top-level account funded by the testnet faucet.
#   It uses the registry, the attestor and the stager of the first example (PARENT, default gated-upgrade.testnet).
# The key file is written to ~/.near-credentials/testnet/ and never printed; the vault's only key is deleted at the
# end. Every transaction is appended to testnet/quiet_vault_tx.jsonl (not to tx.jsonl, which belongs to the first
# example and is what check.sh --testnet compares with the chain).
set -euo pipefail
cd "$(dirname "$0")/.."
export NODE_PATH; NODE_PATH=$(npm root -g)/near-cli/node_modules
P=${PARENT:-gated-upgrade.testnet}; VAULT=${VAULT:-gated-quiet-vault.testnet}
DELAY_NS=${DELAY_NS:-604800000000000}   # 7 days
W=$(mktemp -d); cp testnet/tx.js "$W/"
trap 'cat "$W/tx.jsonl" >> testnet/quiet_vault_tx.jsonl 2> /dev/null || true; rm -rf "$W"' EXIT
tx() { node "$W/tx.js" "$@" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.readline()); print(j["label"], "|", j["tx"], "|", j["result"], j.get("failure", ""))'; }
KEYFILE=$HOME/.near-credentials/testnet/$VAULT.json
if [ -f "$KEYFILE" ]; then K=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["public_key"])' "$KEYFILE")
else K=$(python3 testnet/mkkey.py "$VAULT"); fi
near create-account "$VAULT" --useFaucet --publicKey "$K" --networkId testnet > "$W/faucet.log" 2>&1 \
  || { grep -v -i "private\|secret\|seed" "$W/faucet.log" | tail -3; echo "the faucet did not create $VAULT"; exit 1; }
echo "created $VAULT with the testnet faucet"
tx "quiet vault: deploy the gated vault v1 and call new" deploy-init "$VAULT" contract/out/gated_vault_v1.wasm new \
  "{\"staging_duration\":$DELAY_NS,\"registry\":\"registry.$P\",\"certificate_kind\":\"upgrade-window\",\"attestors\":[\"attestor.$P\"],\"stagers\":[\"gov.$P\"]}"
tx "quiet vault: delete the vault's only access key" delete-key "$VAULT" "$K"
sleep 3
python3 testnet/read.py "$VAULT"
