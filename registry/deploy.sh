#!/bin/bash
# Deploy the registry to a fresh sub-account and make it keyless.
# usage: NETWORK=mainnet OWNER=exitproof.near REGISTRY=registry.exitproof.near BALANCE=2.6 ./deploy.sh
# Needs near-cli (v4) with credentials for $OWNER, and out/exitproof_registry.wasm (cargo near build non-reproducible-wasm --out-dir out).
set -euo pipefail
: "${NETWORK:?}" "${OWNER:?}" "${REGISTRY:?}"
BALANCE=${BALANCE:-2.6}
cd "$(dirname "$0")"
sha256sum out/exitproof_registry.wasm
near create-account "$REGISTRY" --useAccount "$OWNER" --initialBalance "$BALANCE" --networkId "$NETWORK"
near deploy "$REGISTRY" out/exitproof_registry.wasm --initFunction new --initArgs "{\"owner\":\"$OWNER\"}" --networkId "$NETWORK"
PK=$(python3 -c "import json,os;print(json.load(open(os.path.expanduser('~/.near-credentials/$NETWORK/$REGISTRY.json')))['public_key'])")
# near-cli asks for confirmation on a terminal; give it one.
(sleep 2; echo y; sleep 2; echo y; sleep 10) | script -qfc "near delete-key $REGISTRY $PK --force --networkId $NETWORK" /dev/null | tail -3
sleep 3
near list-keys "$REGISTRY" --networkId "$NETWORK" | tail -2
near view "$REGISTRY" owner '{}' --networkId "$NETWORK" | tail -1
