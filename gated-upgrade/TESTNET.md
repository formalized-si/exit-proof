# The gated vault on NEAR testnet

One run of each scenario, on 2026-11-12/13 (UTC). Testnet only; nothing here touches mainnet.
Every transaction below is recorded with its receipts in `testnet/tx.jsonl`; `./check.sh --testnet`
(`testnet/verify.py`) reads all of them and the final state back from the chain and compares.

## Accounts

| Account | What it is | Access keys | Code (sha256) |
|---|---|---|---|
| `gated-upgrade.testnet` | parent; created through the testnet faucet (10 NEAR); owner of the registry; has no role in the vault and is the "anyone" that calls `deploy_certified` | 1 | none |
| `registry.gated-upgrade.testnet` | the certificate registry: the registry source built as it is. Same bytes as the wasm recorded for the mainnet registry `registry.exitproof.near` | **0** | `a8984200f13b774e71ac24cfa260ee69efaaa6123e8da498e4b5cc815ce4ca9b` |
| `attestor.gated-upgrade.testnet` | allow-listed in the registry; the only attestor the vault accepts | 1 | none |
| `gov.gated-upgrade.testnet` | the vault's code stager (role `CodeStager`); depositor of 0.05 NEAR | 1 | none |
| `vault.gated-upgrade.testnet` | the gated vault: staging duration 180 s, that registry, kind `upgrade-window`, that attestor, that stager | **0** | v1 `52a787345f263ca02219a787be84be9e0a2d3dd5e8fd3a84552b8586a0e8c25e` at deployment, v2 `4119617a3df44a476ec8f1aa6ed58b942fc37ce24155403bc307b23e56f13a85` after scenario 1 |

The registry's `new` makes its owner an attestor of the registry too; the vault does not accept it.
Key files were written by `testnet/mkkey.py` (the private key is never printed); the files of the
two accounts without keys were removed after their keys were deleted on chain.

## Setup (`testnet/setup.sh`)

| Step | Transaction | Result |
|---|---|---|
| create `registry.…` | `CBWjCKfiWRLgGkW6gEGRXD5gsUccBpXbJ7ZNqwZnUJxg` | success |
| create `attestor.…` | `Dgxfb25KJuWxJ6jQuJHtxFNK9FcL8ecGKfiVgFkqs9P9` | success |
| create `gov.…` | `JApyjnpe9vtCyN8Jm3T1nYjHgQWWBi4QZWCRkRjb4Ug9` | success |
| create `vault.…` | `FaAzEvHnUe3T4Twx1n9aXBpLSby5p9rGeCBtgdAm5kyS` | success |
| deploy the registry, `new(owner = gated-upgrade.testnet)` | `BxE6wV1HXWyGtCWHzCHoaXUTdRLPepXpdtqA2kgegD2t` | success |
| registry owner: `add_attestor(attestor.…)` | `Nd2ET5GaEGYLGoQAkK8CAZMXJrUz36qAT98oo5akhKF` | success |
| delete the registry's only access key | `AQZBznwvJmzQhBTzs83PuG9bWgnVZkdxDTQykvfqgE5G` | success |
| deploy the gated vault v1, `new(180 s, registry.…, upgrade-window, [attestor.…], [gov.…])` | `4LJZUa5MY7X8Nk9eZZ98dhsaT79PBBwuBTLecZLfkQmK` | success |
| `gov`: `deposit()` with 0.05 NEAR | `5ZRTEMdo8nuAr1jiiMNzzEjm9MHuHF5FHD6uvPGSTg4m` | success |
| delete the vault's only access key | `XV2E2wt8bgtkuc78m9H8JYqnNMmjGqBU9jXSJNpVq4P` | success |

The parent account itself was created by the faucet service
(`near create-account gated-upgrade.testnet --useFaucet --publicKey <key> --networkId testnet`);
that transaction is the faucet's and is not recorded here.

## Scenario 1: certified code is deployed (`testnet/scenario1.sh`)

State before (`testnet/state_before_scenario1.json`): code `52a78734…` (v1), `version()` = 1,
nothing staged, no certificates.

| # | Step | Transaction | Result | What it shows |
|---|---|---|---|---|
| 1 | `gov`: `up_stage_code(v2 build)` | `oZHkyNXrkiD2miRHtzr5DMaNDT6Q9y8iXUGZRgvG8ei` | success | the hash `5P7wwWQ5qA1tFez6mwc3Sh6YdwhGSxrBSA7heq5z3JZ2` is staged; staging timestamp = staging time + 180 s |
| 2 | `attestor`: `attest(hash of v2, certificate)` in the registry | `EDwj8A131hbVnNNEFuGYWFkoijMDst9gTByXEjgj89o1` | success | the certificate arrives during the window (`testnet/attest_v2.json`) |
| 3 | `gated-upgrade.testnet`: `deploy_certified()`, seconds after the staging | `GjzZAVL51qWQYmaT5hYUNFvMWQU2SvxHQ7hA3o8UsKcq` | **failure**: `Gate: deploy too early: staging ends on 1794524885108635419` | a certificate does not shorten the delay; one receipt, the registry is not asked |
| 4 | the same call, once the staging timestamp has passed | `Bk2dvYM2f24dtujK7ji9V8di4jSXKcodptcFesJLZeDL` | **success**, 43.3 Tgas | four receipts: `deploy_certified` on the vault (log `Gate: asking registry.gated-upgrade.testnet for a upgrade-window certificate of 5P7w…`), `get_valid_kind` on the registry (sent by the vault), `on_certificates` on the vault (sent by the vault; log `Gate: certificate of attestor.gated-upgrade.testnet accepted for 5P7w…`), and `[DeployContract, FunctionCall(up_verify_state)]` on the vault (sent by the vault) |

State after (`testnet/state_after_scenario1.json`): **code `4119617a…` (v2), `version()` = 2**;
same gate, same roles, no access keys; the registry holds one valid `upgrade-window` certificate
for the running code, by `attestor.gated-upgrade.testnet`.

## Scenario 2: uncertified code is not deployed (`testnet/scenario2.sh`)

Runs on the upgraded vault, so it also shows that the gate is in force after the upgrade.
State before (`testnet/state_before_scenario2.json`): code `4119617a…` (v2).

| # | Step | Transaction | Result | What it shows |
|---|---|---|---|---|
| 1 | `gov`: `up_stage_code(v3 build)` | `EuwVKGE3qbofEkybamvC8chhY5wyQf5omVH6BiYq9vVH` | success | the hash `6AFnkHg3NKz9xwWeomPYq5BpaowVWe2BHCwKD3CuDTuA` is staged; nobody attests it |
| 2 | `gated-upgrade.testnet`: `deploy_certified()`, once the staging timestamp has passed | `BqssNoHvStwbBXBtAAn3YXZiXqq4t1TzBRqKuDAfGocu` | **failure**: `Gate: no valid upgrade-window certificate from an accepted attestor for 6AFn…` | three receipts: `deploy_certified` succeeds and asks, the registry answers, `on_certificates` panics; **no deploy batch** |
| 3 | `gov` (the stager): `up_deploy_code(hash of v3)` directly | `EtonGXeR47dnfKUUz7FVkGw9wSg1DpAnEZUXDUzCiNas` | **failure**: `Insufficient permissions for method up_deploy_code restricted by access control. Requires one of these roles: ["CodeDeployer"]` | the plugin's own deploy method is closed to the holder of the staging role |

State after (`testnet/state_after_scenario2.json`): **code still `4119617a…` (v2), `version()` = 2**;
the v3 build is staged and stays staged; the registry holds no valid certificate for it.

## Reading it back

No keys are needed for any of this.

```
python3 testnet/read.py vault.gated-upgrade.testnet        # code hash, access keys, version, gate, delay
                                                           # status, staged hash, roles; the registry's code
                                                           # hash, keys, and its valid certificates for the
                                                           # running and for the staged code
python3 testnet/verify.py                                  # the same, compared with tx.jsonl and the pinned hashes
```

With near-cli (`export NEAR_TESTNET_RPC=https://rpc.testnet.fastnear.com`):

```
near state vault.gated-upgrade.testnet --networkId testnet            # code_hash 5P7wwWQ5qA1tFez6mwc3Sh6YdwhGSxrBSA7heq5z3JZ2
near list-keys vault.gated-upgrade.testnet --networkId testnet        # []
near list-keys registry.gated-upgrade.testnet --networkId testnet     # []
near view vault.gated-upgrade.testnet version '{}' --networkId testnet                 # 2
near view vault.gated-upgrade.testnet gate '{}' --networkId testnet
near view vault.gated-upgrade.testnet up_get_delay_status '{}' --networkId testnet
near view vault.gated-upgrade.testnet up_staged_code_hash '{}' --networkId testnet     # 6AFnkHg3NKz9xwWeomPYq5BpaowVWe2BHCwKD3CuDTuA
near view vault.gated-upgrade.testnet acl_get_permissioned_accounts '{}' --networkId testnet
near view registry.gated-upgrade.testnet get_valid_kind '{"code_hash":"5P7wwWQ5qA1tFez6mwc3Sh6YdwhGSxrBSA7heq5z3JZ2","kind":"upgrade-window"}' --networkId testnet   # one certificate
near view registry.gated-upgrade.testnet get_valid_kind '{"code_hash":"6AFnkHg3NKz9xwWeomPYq5BpaowVWe2BHCwKD3CuDTuA","kind":"upgrade-window"}' --networkId testnet   # []
near tx-status Bk2dvYM2f24dtujK7ji9V8di4jSXKcodptcFesJLZeDL --accountId gated-upgrade.testnet --networkId testnet
```

The base58 code hash is the sha256 of the wasm: `5P7w…` = `4119617a…` (`contract/out/gated_vault_v2.wasm`),
`6ZebT4oBmsftwqdjnTcaha1227dARNU9uzXNae2VaNPf` = `52a78734…` (v1), `6AFn…` = `4ca96232…` (v3),
`CM89kMNQzjWRkuNJE7Q2Va2Z4YrbK4MjmiLZnGbUcGkS` = `a8984200…` (the registry).

## What this example is, and is not

- One execution of each scenario on a public test network: it shows that the deployed bytes do
  what the scenarios of the simulator do, in these two cases. It is not a proof and not a test run.
- The certificate attested here (`testnet/attest_v2.json`) is a demonstration certificate by an
  account created for this example. It says so, names the theorems and their assumptions, and
  pins the proof bundle by hash (`artifact_sha256` = `09a3d698…`, `python3 scripts/bundle_hash.py`;
  the listing at the time of the attestation is `testnet/attest_v2.bundle.txt`).
- Non-archival RPC nodes forget transactions after a few days; `verify.py` then reports that it
  cannot find them. The final state stays readable.
- The scanner (`tools/exitproof.py vault.gated-upgrade.testnet --network testnet`) reads the gate of this build
  of the proved vault and prints `EXIT STAGE 0 — KEYHOLDER TRUST: … certified upgrades only, but code is staged
  (6AFnkHg3NKz9…) and its delay has passed`: the uncertified code is deployed the moment one accepted attestor
  certifies it, so no time bound holds.
- Left on testnet: about 1 NEAR on the parent, the three accounts with keys, and the vault and the registry
  (with `gated-quiet-vault.testnet` below, three contracts).

## A second vault, with nothing staged

The vault above was left by scenario 2 with uncertified code staged and its delay passed. That state is one
attestation away from a deploy, with no time bound, and a scanner that reads the gate reports it as stage 0.

`gated-quiet-vault.testnet` is the same vault code (`gated_vault_v1.wasm`, code hash `6ZebT4oB…`) with a staging
delay of seven days, the same registry, attestor and stager, nothing staged and no access keys. It was created by
`testnet/quiet_vault.sh` on 2026-11-13 (a new account funded by the testnet faucet):

| Step | Transaction |
|---|---|
| deploy the gated vault v1 and call `new` | `CvywDaQvEuesD1HneezdYPkt3QyAJ6eFEbB7DvbwP6yU` |
| delete the vault's only access key | `AzFYnzLdgEdoGJFxZehqFcdn7dKb8wd8dbCp7T65v6Ng` |

`python3 ../tools/exitproof.py gated-quiet-vault.testnet --network testnet` prints
`EXIT STAGE 1 — EXIT WINDOW (168 h, certified upgrades only)`. The transactions are in
`testnet/quiet_vault_tx.jsonl`; `check.sh --testnet` reads the first example only.
