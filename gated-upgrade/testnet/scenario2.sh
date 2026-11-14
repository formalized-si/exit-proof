#!/usr/bin/env bash
# Testnet scenario 2: uncertified code is not deployed. TESTNET ONLY.
#   gov stages the v3 build, for which the registry holds no certificate; after the delay
#   deploy_certified is refused in the callback and a direct up_deploy_code by the stager is
#   refused by the plugin; the code hash of the vault does not change.
set -euo pipefail
cd "$(dirname "$0")/.."
export NODE_PATH; NODE_PATH=$(npm root -g)/near-cli/node_modules
P=${PARENT:-gated-upgrade.testnet}
REG=registry.$P; GOV=gov.$P; VAULT=vault.$P
tx() { node testnet/tx.js "$@" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.readline()); print(j["label"], "|", j["tx"], "|", j["result"], j.get("failure", ""))'; }
python3 testnet/read.py "$VAULT" --json > testnet/state_before_scenario2.json
tx "scenario 2: gov stages the v3 build (no certificate)" call "$GOV" "$VAULT" up_stage_code @contract/out/gated_vault_v3.wasm 300
python3 testnet/wait_staging.py "$VAULT"
tx "scenario 2: deploy_certified after the delay (must be refused)" call "$P" "$VAULT" deploy_certified '{}' 300 || true
H3=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["up_staged_code_hash"])' <(python3 testnet/read.py "$VAULT" --json))
tx "scenario 2: up_deploy_code by the stager (must be refused)" call "$GOV" "$VAULT" up_deploy_code "{\"hash\":\"$H3\"}" 300 || true
sleep 3
python3 testnet/read.py "$VAULT" --json > testnet/state_after_scenario2.json
python3 testnet/read.py "$VAULT"
