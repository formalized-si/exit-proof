#!/usr/bin/env bash
# Sets up the testnet example. TESTNET ONLY.
#   PARENT (default gated-upgrade.testnet) must exist and hold about 10 NEAR; it was created with
#     python3 testnet/mkkey.py $PARENT        (writes the key file, prints the public key)
#     near create-account $PARENT --useFaucet --publicKey <that key> --networkId testnet
# Creates registry.$PARENT (the unchanged registry wasm, owner $PARENT, one attestor), attestor.$PARENT,
# gov.$PARENT (the code stager) and vault.$PARENT (gated vault v1: staging duration DELAY_NS, that
# registry, kind upgrade-window, that attestor, that stager), puts a small deposit into the vault,
# and deletes the only access key of the registry and of the vault. Key files are written to
# ~/.near-credentials/testnet/ and never printed. Every transaction is appended to testnet/tx.jsonl.
set -euo pipefail
cd "$(dirname "$0")/.."
export NODE_PATH; NODE_PATH=$(npm root -g)/near-cli/node_modules
P=${PARENT:-gated-upgrade.testnet}
REG=registry.$P; ATT=attestor.$P; GOV=gov.$P; VAULT=vault.$P
DELAY_NS=${DELAY_NS:-180000000000}   # 3 minutes
tx() { node testnet/tx.js "$@" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.readline()); print(j["label"], "|", j["tx"], "|", j["result"], j.get("failure", ""))'; }
pk() { python3 -I -c 'import json,os,sys; print(json.load(open(os.path.expanduser("~/.near-credentials/testnet/" + sys.argv[1] + ".json")))["public_key"])' "$1"; }

for pair in "$REG 2.3" "$ATT 0.4" "$GOV 0.6" "$VAULT 5.6"; do
  set -- $pair
  K=$(python3 testnet/mkkey.py "$1")
  tx "setup: create $1" create "$P" "$1" "$K" "$2"
done
tx "setup: deploy the registry and call new" deploy-init "$REG" contract/out/exitproof_registry.wasm new "{\"owner\":\"$P\"}"
tx "setup: registry owner adds the attestor" call "$P" "$REG" add_attestor "{\"account_id\":\"$ATT\"}" 30
tx "setup: delete the registry's only access key" delete-key "$REG" "$(pk "$REG")"
tx "setup: deploy the gated vault v1 and call new" deploy-init "$VAULT" contract/out/gated_vault_v1.wasm new \
  "{\"staging_duration\":$DELAY_NS,\"registry\":\"$REG\",\"certificate_kind\":\"upgrade-window\",\"attestors\":[\"$ATT\"],\"stagers\":[\"$GOV\"]}"
tx "setup: a deposit of 0.05 NEAR by gov" call "$GOV" "$VAULT" deposit '{}' 30 0.05
tx "setup: delete the vault's only access key" delete-key "$VAULT" "$(pk "$VAULT")"
sleep 3
python3 testnet/read.py "$VAULT"
