# Design decisions

| # | Decision | Reason |
|---|---|---|
| 1 | The product question is "can I get my money back, and who could stop me", not "is the contract locked". | `token.sweat`, `wrap.near`, USDT and `intents.near` have no full-access keys, yet three of the four can change their code through a contract method. |
| 2 | Static reachability of wasm imports is not used for verdicts. | In near-sdk one Promise dispatcher serves transfer and deploy actions alike, so any method that creates a promise statically "reaches" deploy; resolving indirect calls through vtables does not help. `tools/reach.py` is kept as the negative result. |
| 3 | Reports show the kind and number of holders of a power and the weakest link, never account names of key holders. | A depositor needs the strength of the guard; a list of privileged keys is a list of targets. |
| 4 | Depth first on the artifact with the largest coverage: the `poolv1` staking pool code. | The validator census shows 86.2% of NEAR stake on this one code hash; the accounts are keyless and the source has no code-change action. |
| 5 | Second and third proofs on the NEP-141 flow (wrap.near; the current near-contract-standards). | The 2026 losses on NEAR were in the two-step `transfer_call` → `resolve` flow, and the library is a shared dependency. |
| 6 | A theorem is tied to deployed code by hash equality with a committed artifact plus execution of the exact bytes on nearcore against the model. | Proofs are about a model; the binding has to be explicit and re-checkable. A byte-identical rebuild of the 2020 pool from source was attempted and is documented in `REPRO.md`. |
| 7 | One-line claims were narrowed after an independent adversarial review. | For example: the protocol returning unstaked stake is an assumption, not a theorem; for mainnet the wNEAR headline is `T_exit` under the invariant. |
| 8 | An RPC failure never becomes a verdict. | A census run once mistook rate limiting for "account not found"; `tools/rpc.py` now raises instead. |
| 9 | Certificates live in a keyless registry contract on NEAR, keyed by code hash, append-only, with a `kind`. | Agents and wallets need one place to look; the registry passes its own "code cannot change" check; a revocation never erases the record. |
| 10 | The registry does not verify proofs on chain; it pins the proof bundle by hash and names the re-check command. | A Lean kernel run for theorems of this size does not fit NEAR's gas limit; it is more honest to record who attests what and how to re-check it. |
| 11 | The reference agent applies a rule over evidence (minimum exit stage) and is dry-run only. | A guarantee, not a spending guard; nothing needs to be signed to demonstrate the decision. |
| 12 | Exit Stages: every contract gets a stage, each stage defined by re-checkable evidence. | Unconditional exit theorems only apply to immutable code; most live contracts are upgradable, and for them the meaningful guarantee is a proven exit window. |
| 13 | For staking-farm pools the upgrade path is shown as "owner AND code supplied by the factory". | The source requires the owner as caller and takes the new code from the factory. |
