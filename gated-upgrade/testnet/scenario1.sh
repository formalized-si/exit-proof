#!/usr/bin/env bash
# Testnet scenario 1: certified code is deployed. TESTNET ONLY.
#   gov stages the v2 build; the attestor attests its hash in the registry during the window; a
#   deploy_certified before the delay is refused; after the delay deploy_certified, called by an
#   account with no role, replaces the code.
set -euo pipefail
cd "$(dirname "$0")/.."
export NODE_PATH; NODE_PATH=$(npm root -g)/near-cli/node_modules
P=${PARENT:-gated-upgrade.testnet}
REG=registry.$P; ATT=attestor.$P; GOV=gov.$P; VAULT=vault.$P
tx() { node testnet/tx.js "$@" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.readline()); print(j["label"], "|", j["tx"], "|", j["result"], j.get("failure", ""))'; }
python3 testnet/read.py "$VAULT" --json > testnet/state_before_scenario1.json
tx "scenario 1: gov stages the v2 build" call "$GOV" "$VAULT" up_stage_code @contract/out/gated_vault_v2.wasm 300
python3 testnet/make_attest.py v2 > testnet/attest_v2.json
python3 scripts/bundle_hash.py --list > testnet/attest_v2.bundle.txt
tx "scenario 1: the attestor attests the hash of v2" call "$ATT" "$REG" attest json@testnet/attest_v2.json 100 0.1
tx "scenario 1: deploy_certified before the delay (must be refused)" call "$P" "$VAULT" deploy_certified '{}' 300 || true
python3 testnet/wait_staging.py "$VAULT"
tx "scenario 1: deploy_certified after the delay, by an account with no role" call "$P" "$VAULT" deploy_certified '{}' 300
sleep 3
python3 testnet/read.py "$VAULT" --json > testnet/state_after_scenario1.json
python3 testnet/read.py "$VAULT"
