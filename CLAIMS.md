# Claims — what is proved, what is tested, what is not claimed

Evidence levels used below: **proved** = a Lean 4.35 theorem, no `sorry`, axioms listed; **tested** = executed and
compared; **read** = taken from chain state or code; **heuristic** = inferred from names or view methods.

## 1. Core staking pool (`near/core-contracts@1cacc9d`, code hash `J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY`)

| Claim | Level | Where |
|---|---|---|
| In the Lean model, from any state reachable from `new()` without outflow from the pool account and with fewer than 10^12 calls, `unstake_all` by a delegator with stake succeeds and leaves it at least `get_account_total_balance` | proved (`StakingPool.unstake_all_ok`, `exit_guarantee`) | `pool-proof/lean/StakingPool/Exit.lean` |
| Then, with no further calls by that delegator, in any state 4+ epochs later in which the protocol has returned the unstaked stake (PUA), `withdraw_all` succeeds and sends at least that amount | proved (`withdraw_all_ok`, `exit_guarantee`); PUA is an assumption about the protocol | same |
| No call by another account, the pool owner included, lowers a delegator's unstaked balance, unlock epoch or shares; the share price never decreases; owner methods only set fee (future rewards), key, pause, vote | proved (`others_call`, `others_preserve`, `owner_methods`, `exec_price`) | `pool-proof/lean/StakingPool/Safety.lean` |
| A successful deposit of `d` raises the depositor's claim by at least `d` | proved (`deposit_claim`) | `pool-proof/lean/StakingPool/Deposit.lean` |
| The model behaves like the deployed bytes | tested: 1149 random traces, 55 955 calls on nearcore 2.14.0 (near-contract-sim), state compared after every step, 20 998/20 998 error texts equal | `pool-proof/out/summary.json` |
| The comparison would notice a wrong model | tested: 8 of 8 one-line changes of it (exit arithmetic, unlock delay, two balance guards) differ from the wasm on 33 to 1149 of the 1149 traces; the unchanged model agrees on all; run by an independent reviewer; a sample, not one change per guard | `pool-mutants/` |
| The deployed code equals `staking-pool/res/staking_pool.wasm` committed at `1cacc9d` | read (sha256 equality); a rebuild from source with the author's compiler was not byte-identical | `docs/REPRO.md` |
| 196 current validators (500.9M NEAR, 86.2% of stake) run this code; none has an access key | read (RPC `validators`, `view_access_key_list`) | `docs/CENSUS.md` |

Assumptions: protocol returns unstaked stake within the window (PUA), no outflow other than `withdraw`, storage staking not
modelled, enough gas, staking-key validity rules unchanged. Not claimed: compilation correctness, gas, multi-shard timing.

## 2. wrap.near (`near/core-contracts@54f8267` w-near, near-contract-standards 3.1.0, code hash `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1`)

| Claim | Level | Where |
|---|---|---|
| In any state satisfying the full invariant `Inv`, `near_withdraw(b)` with 1 yocto by a registered holder `u ≠ wrap.near`, `b` its balance when the call executes, succeeds and the contract sends `u` `b + 1` yocto | proved (`WNear.T_exit`; `exit_always` for states reachable from `new()`) | `wnear-proof/lean/WNear/Theorems.lean` |
| `total_supply` = sum of balances; every step preserves `Inv` | proved (`T_conservation`, `inv_step`) | same |
| `ft_resolve_transfer` has effect only when the contract itself is the caller, for any arguments and promise results | proved (`T_resolve_private`) and tested on the deployed bytes from a user, a contract and a contract callback | same; `wnear-proof/evidence/checks.json` |
| Only `u`'s own calls, or the settlement of a transfer made to `u` (bounded by that transfer), lower `u`'s balance | proved (`T_no_one_else`, `T_who_can_lower`) | same |
| The model behaves like the deployed bytes | tested: 2000 traces, 55 825 receipts, 329 546 balance comparisons, 0 mismatches; 8/8 model mutants caught | `wnear-proof/evidence/conformance.json`, `mutants.txt` |
| Mainnet satisfies the solvency part of `Inv` | read at block 224 128 229 (margin 3 388 NEAR); `supply = Σ balances` over ~2.68M records not checked on mainnet | `wnear-proof/evidence/mainnet_check.json` |
| The account has had two code deployments, the first code from 2021-02-15 and the certified code since 2021-04-22, and none since: no temporary code in between | read (every deployment receipt of `wrap.near`, read on 2026-11-14) | `evidence/wrap-near-deployments.json`, `tools/deploy_history.py` |

## 3. Token standard (`near-contract-standards` 5.29.0, example token code hash `3Ty4ENxJ4EicohgXi9E2txgbqMh3DWSshPrtXxY8pksm`)

| Claim | Level | Where |
|---|---|---|
| P1 conservation, P2 settlement bounds (`f ≤ amount`, `f ≤` receiver balance, conservation or burn), P3 callback only by the token, P4 only the holder (or settlement of a transfer to it) lowers its balance, P5 unregister / storage deposit / storage solvency | proved: 16 theorems in `token-standard/lean/ProvedFT/Theorems.lean`; P3 theorems use only `propext` | `token-standard/PROPERTIES.md`, `properties.json` (statement hashes checked against the Lean sources) |
| A given token wasm behaves as the model | tested per token by `certify-token.sh` (1000 traces, every receipt, event and state compared, plus model-free monitors for P1–P4) | `token-standard/evidence/certificate_example.json` |
| The kit detects deviations | tested: 10 one-line mutants (9 of the library, 1 of the example token), each FAIL with the expected property; unmutated control PASS | `token-standard/evidence/mutants.json` |
| P3 depends on the token: `#[private]` on `ft_resolve_transfer` is the documented responsibility of the token (the legacy macro adds it), so the kit checks P3 on each token's wasm | read (source) | `token-standard/README.md` |

Not covered by a token certificate: the token's custom methods (mint, burn, pause, owner), access keys on the token account,
gas beyond the 5 Tgas callback constant, the JSON parsing layer (tested on harness inputs only).

## 4. Upgrade window (`near-plugins` v0.5.1 `Upgradable`, commit `312e016e`; reference vault code hash `7m2GRykdzJxaH4r8fmjZg5BJnVvvkKFqDm55GcLLfdPv`)

| Claim | Level | Where |
|---|---|---|
| W1: a successful `up_deploy_code` deploys exactly the code of the last `up_stage_code`, no earlier than the staging time plus the duration in force when it was staged | proved (`UpgradeWindow.W1_delay`, `deploy_origin`) | `upgrade-window/lean/UpgradeWindow/Theorems.lean` |
| W2: between staging and deploy `up_staged_code_hash` is constant and is the only hash a deploy accepts | proved (`W2_visibility`) | same |
| W3: no deploy is accepted before `safeUntil = min(now + D, staging timestamp of staged code, effect time of a pending duration change + its value)`; the bound is tight. The naive bound "D after staging" is false: three ways around it (code staged before a delay existed; shrinking the delay first; a build without overflow checks) are each proved with a witness | proved (`W3_no_deploy_before`, `W3_tight`, `W3_prestaged_shortcut`, `W3_shrink_shortcut`, `W3_unchecked_shortcut`) | same; `Unchecked.lean` for builds without overflow checks |
| W4: with no duration set, staging and an accepted deploy can share one block timestamp | proved (`W4_no_window`, `W4_witness`) | same |
| W5: with duration `D` and no alarm (no staged code, no pending shorter duration), no deploy is possible before `now + D`; a code change is preceded by a visible alarm at least `D` earlier | proved (`W5_quiet_reading`, `W5_notice`, `W5_code_change`); that a user's exit fits in the window is a hypothesis about the host contract | same |
| The reference vault wasm behaves as the model | tested: 1000 + 5000 random traces, 0 divergences; 7 scenario runs on the wasm; 12/12 one-line plugin mutants detected | `upgrade-window/evidence/` |
| `token.sweat`, `lst.rhealab.near`, `ctl-intents.near`, `omni.bridge.near` expose the plugin interface and have no staging duration set | read on 2026-11-12 (`up_get_delay_status`); the checker does not compare their wasm with v0.5.1 | `upgrade-window/evidence/mainnet_readings.txt` |

Not covered: code-change paths outside the plugin (keys, custom upgrade methods, global contracts by account id), which the
scanner checks; pausing of exit methods; gas.

## 5. Scanner and stages (any mainnet contract)

| Claim | Level |
|---|---|
| Full-access keys, function-call keys, code hash, global-contract reference | read |
| Upgrade-like / fund-moving / pausing methods and the roles that guard them | heuristic (export names + the contract's own view methods; a contract can misreport) |
| Stage 2 | no code-change path found by these checks AND no access key of any kind on the account (a function-call key pays its gas from the account's balance) AND an `exit` certificate for the exact code hash in the registry from an attestor the scanner accepts (one account so far) AND the account runs its own code, not a global contract, AND its deployment history shows one code deployment (the indexer lists the first and the latest, so one row means one), or the proof records the full list of the account's deployments, read once from every deployment receipt, and the latest listed is still the latest of them (`wrap.near`: 2, `evidence/wrap-near-deployments.json`). The scanner checks neither the proof nor the theorem's precondition on the live state; for wNEAR the headline says "under a stated condition" |
| Stage 1 | no code-change method other than the upgrade plugin's five is found by name, its current window (the `safeUntil` bound on the chain's clock, with the staging timestamp whenever it is set) is non-zero, no pause or fund-moving method or role was found, and every view these readings come from answered; rests on `[name]` and `[view]` readings of the contract, and on one of two bases, which the report names: the code hash has an `upgrade-window` certificate from an accepted attestor (that wasm was run against the plugin model), or it is a build that this repository proved and tested with the plugin unchanged (the gated vault). A plugin recognised by method names only gives stage 0. `deploy_certified` counts as part of the plugin path only for the builds of this repository's gated vault (`tools/proofs.json`). The reference agent stakes at stage 1 only on the first basis |
| Stage 1 exists in practice | shown on three testnet vaults: two running the certified reference vault, one quiet and one with an upgrade staged until 2026-11-19 17:47 UTC (`EVIDENCE.md`), and `gated-quiet-vault.testnet`, a build of the proved gated vault (`gated-upgrade/TESTNET.md`); no mainnet contract read is at stage 1 |
| Stage 0 / U | the path that prevents a higher stage is named; "no code-change path found" is the result of these checks, not a proof |
| Reports show the strength of each guard (DAO, multisig, contract, several keys, single key) and never list key holders | design rule |

## 6. Live state of the proved pools

| Claim | Level | Where |
|---|---|---|
| At block 224 223 218 (hash `HmrMKtdN…`, 2026-11-12) each of the 196 validator pools with code hash `J1arLz48…` satisfies: account balance ≥ `total_staked_balance` + the sum of delegators' unstaked balances (the `solvency` invariant of the exit theorem); the sum of delegators' staked balances ≤ `total_staked_balance`; no access keys. 256 564 delegator accounts, 501 637 444 NEAR staked, 9 087 438 NEAR unstaked by delegators, 510 738 429 NEAR held by the pools | read at one pinned block through the pools' own view methods | `evidence/pools-live.json`, `tools/pools_live.py` |
| The deployment history of each of the 196 pools lists exactly one code deployment, made by the factory `poolv1.near` in the receipt that created the account; so the state of each was made by the proved code alone, which is what the exit theorem starts from | read (an indexer's list, 2026-11-13) | `evidence/pools-origin.json`, `tools/pools_origin.py` |

## 7. On-chain registry (`registry.exitproof.near`, NEAR mainnet)

| Claim | Level |
|---|---|
| Certificates are keyed by code hash and carry a kind (`exit`, `token-standard`, `upgrade-window`), theorem names, assumptions, binding, conformance counts, the bundle hash and the re-check command | read (`get_valid`) |
| The bundle hash of a certificate can be recomputed from a checkout: `python3 tools/bundle_hash.py <directory>` | re-computable |
| The registry account has no access keys | read (`view_access_key_list`) — see `EVIDENCE.md` |
| The registry does not verify proofs on chain; it records who attested what and pins the artifact | design |
| The owner that admits attestors and the one attestor so far are the same account with one access key; a certificate can be revoked only by its attestor, and removing an attestor does not withdraw its certificates | read (source of `registry/`, account state) |

## 8. Token census and token check

| Claim | Level |
|---|---|
| For the 71 run of 86 code hashes — every code hash of the 395 fungible tokens in the ledger of `intents.near` (block 224 273 043) and of 171 of the 217 tokens whitelisted on `v2.ref-finance.near`: the deployed code, run on the nearcore runtime on 1000–2000 random traces per code hash, with monitors of the proved properties P1–P4 (total supply = sum of balances, exact transfers, settlement of `ft_transfer_call`, callback ownership, balance ownership) | tested; a verdict is agreement on those traces, for the code initialised with test arguments, not a proof and not a statement about any token's live state |
| Tokens of the Intents ledger by verdict: 355 behave as the standard (92 plain, 263 with extensions), 14 deviate, 2 under review, 21 not run, 3 have no contract code | tested |
| 201 of the 355 run code with an extension that changes transfers when it is switched on; whether it applies to a given token now is a live reading: `tools/token_check.py` reads the fee and tax views `get_tax`, `get_config`, `tax_state`, `get_fee_state`, `get_accumulated_info`, and answers "unknown" for code that has such an extension and no view that holds a field recognised as its fee (the bridged-token families) | tested with the extension on; live state read from five kinds of view, unknown otherwise |
| The deviating code: a transfer tax; for one build the settlement of `ft_transfer_call` reports a refund that is not made (the case published by the Backed team) | tested |
| The monitors of the census (an earlier, smaller set than the 14 of `token-monitors/` below) notice 6 of 10 one-line changes of the standard library and are silent on the reference token; the 4 they miss concern storage and gas, which they do not watch | tested |
| On 2026-11-13 all 13 exchange-listed tokens of the three tax-capable builds of one issuer answer `get_tax` with a non-zero tax | read (`get_tax`) |
| `tools/token_check.py`: the census verdict for a token's code hash, the transfer tax read from the token now, methods beyond the standard, the methods with which a privileged party freezes or lowers a holder's balance (pause, blacklist, destroy, burn_from…: then `behaves_as_standard_now` is unknown, since P4 does not hold for such code), the exit stage | read + lookup + heuristic (the balance powers by name); a code hash outside the census, not run or under review is reported as `NOT CHECKED` |
| `token-monitors/`: any token wasm, with its own initialiser, run on 1 000 random traces with 14 model-free monitors of the proved properties; the result is a certificate file. `token_check` counts the certificates kept in `evidence/token-certificates/` by code hash; a certificate brought by the caller is checked for consistency and shown as a claim, and counts only after the caller has re-run it (`--accept-certificate`) | tested: four codes taken from mainnet with different initialisers got PASS (`evidence/token-certificates/`); the monitors catch 7 of 10 one-line mutants of the reference token, 3 are outside them (NEAR accounting, gas); a monitor without a check makes the verdict INCONCLUSIVE. A PASS is agreement on those traces for the methods the config exercised, not a proof |

Not in this repository: the census runner and its per-family configurations.

## 9. Token ledger of NEAR Intents (`intents-proof/`)

| Claim | Level | Where |
|---|---|---|
| For the code `BtA1BEFN…` of `intents.near`: T1 backing, T2 settlement, T3 credit on arrival, T4 who can lower a balance — six ways, each with the authorisation the contract tests, and where keys, role holders and pending refunds come from (`T4_authorised` and the statements around it; for wNEAR the earlier, weaker form) — for a token that is the proved model of near-contract-standards 5.29.0; W1–W4 and N2–N4 for wNEAR; under "any receipt may fail" | proved (Lean 4.35, 136 statements, axioms propext, Quot.sound, Classical.choice); re-checked by `leanchecker --fresh` and nanoda | `intents-proof/lean/`, `NOTES.md` |
| The deployed bytes are the build of `near/intents@16d04f6e` | rebuilt byte for byte | `intents-proof/evidence/rebuild_run.log` |
| The deployed wasm behaves as the model on its token paths | tested: 311 697 receipts replayed receipt by receipt — 308 469 agree, 0 disagree, the outcome of 3 228 not compared (failures forced by the harness, receipts out of gas, signature checks); token and contract replayed together through the step function of the two-contract world for the standard token (209 557 receipts agree, 0 disagree; the wNEAR world is not replayed this way). 23 106 calls of the 24 role-guarded methods by accounts without the permission, none ran. Sensitivity: 121 one-line changes of the model, at least one per guard — 114 noticed, 7 that no receipt can show and with which the Lean build fails (four at a theorem, three only at a lemma that restates the changed definition) (11 of ours, 23 by an independent reviewer, 38 added since, 49 for the strict world; the replay first noticed 10 of the reviewer's 23). Not compared: gas, the signature check itself, the strict step of a whole signed payload; not generated: `token_diff` intents and their fees, `auth_call`, key changes during a trace | `intents-proof/evidence/`, `intents-proof/MUTANTS-REVIEW.md` |
| The same ledger stated in TLA+ has no violation over 78 961 324 states, and violates backing with a fee-keeping token and with a contract variant that refunds a failed `ft_transfer_call` | model-checked for a small scope | `intents-proof/tla/` |
| The plain-language statements match the theorems | re-derived blind once; two sentences were wrong and are corrected | `intents-proof/README.md` |
| `intents.near` has had 19 code hashes: created on 2024-11-01 without code, its code changed 18 times between 2024-11-05 and 2026-10-07 (18 deployment receipts; the indexer lists the first and the latest deployment, which is the `deployments: 2` of `evidence/contracts-census.json`); the proved code `BtA1BEFN…` is in force since block 218 982 375 | read (archival state: the code hash at sampled heights and the exact block of each change; a code version shorter than the sampling interval could be missed) | `intents-proof/evidence/intents-code-history.json` |
| `near/intents@fce0936b`, not deployed: behaves as the model on 625 traces (40 279 receipts replayed, 0 disagree), same exports, no ledger write site added; three modelled source files changed, so the gate's verdict is NEEDS REVIEW | tested (run) + read (source comparison) | `intents-proof/evidence/upgrade_4PMYYWqio2Q3.json` |

The theorems are about states reachable from an empty ledger under this code with a standard token. The live
ledger was also written by the 17 earlier codes of the account. The live contract also holds tokens that do not
behave as the standard; for those the ledger can exceed the holdings, and `tools/intents_backing.py` reads that for
every token at one block (`evidence/intents-live-backing.json`).

Not covered: multi-token and NFT paths (the 2026 loss on this contract was on the multi-token deposit path), that
an intent or internal transfer was authorised by the account's signature, gas, the intent engine (the balancing of a `token_diff` between signers and its fees are moves that balance by assumption, `NOTES.md` §4, item 7), the three powers of the role `DAO`
(a call from the contract's account, a full-access key, a code upgrade), a proof about the bytes.

## 10. Verified upgrades (`gated-upgrade/`)

| Claim | Level | Where |
|---|---|---|
| For the gated vault: every code change installs code whose hash had a valid certificate of the accepted kind from an accepted attestor when the registry was asked, that was staged before, no earlier than `safeUntil`; code whose hash never gets such a certificate is never installed | proved (Lean 4.35; axioms propext, Quot.sound, Classical.choice) under the hypotheses listed there: no receipt from the contract's own account (no access keys), the registry answers with certificates it holds, the model describes the wasm | `gated-upgrade/lean/GatedUpgrade/Theorems.lean`, `README.md` |
| The wasm behaves as the model | tested: 10 scenarios (82 checks), 2 000 random traces with a monitor, 0 violations; mutants with `--mutants` | `gated-upgrade/check.sh` |
| On NEAR testnet the vault deployed certified code after its window and did not deploy uncertified code | read back from the chain | `gated-upgrade/TESTNET.md`, `./check.sh --testnet` |
| The scanner reports the gate | read (`gate()` view of the contract, the gate's registry); self-reported by the contract unless its code hash is certified. A gated vault is stage 1 only while nothing is staged or the staged code is inside its delay; with staged code past its delay it is stage 0 (one attestation away from a deploy), which is the state of the first testnet example; the second one, `gated-quiet-vault.testnet` (nothing staged, a delay of seven days, no access keys), reads as stage 1 | `tools/exitproof.py`, `gated-upgrade/testnet/quiet_vault_tx.jsonl` |

Limits: a certificate revoked after the registry call does not stop a deployment already under way; the guarantee
is as strong as the accepted attestors (the testnet example accepts one); the example's gate accepts the existing
kind `upgrade-window`, no certificate kind states that new code keeps the proved properties of the old; a stager can
restart the delay, so liveness of an upgrade is not guaranteed; after an upgrade the new code has to be a gated
contract again.

Independent adversarial review of sections 1–2 (non-vacuity examples, `leanchecker --fresh`, the nanoda kernel): `docs/REVIEW.md`.
