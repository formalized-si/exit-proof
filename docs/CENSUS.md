# Census: which code holds the NEAR stake (snapshot of 2026-11-11, ~22:17 UTC)

Source: the RPC method `validators` (current epoch) → `view_account` and `view_access_key_list` for every pool.
Raw data: `../evidence/validators-census.json` (script `../tools/census_validators.py`; requests that failed on
RPC limits were queried again). 340 validators, 581 205 250 NEAR staked.

| Pool code (code hash) | Pools | Stake, NEAR | Share | With a full-access key | Where the code comes from |
|---|---:|---:|---:|---:|---|
| `J1arLz48fgXc…` | 196 (`*.poolv1.near`) | 500 880 513 | 86.2% | 0 | `near/core-contracts@1cacc9d` `staking-pool/res/staking_pool.wasm` (byte for byte) |
| `AjD4YJaXgpiR…` | 140 (`*.pool.near`) | 64 636 959 | 11.1% | 0 | staking-farm; has the methods `upgrade`/`migrate` |
| `GGfKUF9TuAFN…` | 2 (`*.pool.near`) | 10 402 166 | 1.8% | 0 | not established |
| `DqKkcbjBiPJj…` | 1 | 4 774 244 | 0.8% | 1 | not established |
| `5vf2Jkqpk11H…` | 1 | 511 369 | 0.1% | 0 | not established |

The conclusion for the product: a proof of withdrawal for one artefact (`J1arLz…`) covers 86.2% of the whole
stake of the network. These 196 accounts have no keys, and the source at `1cacc9d` has no action that changes the
code, deletes the account or adds a key; the rights of a pool's owner are the staking key, the fee, the staking
pause and the vote. Which of these can get in the way of a withdrawal is answered by the theorem
(`../pool-proof/REPORT.md`), not by this file. The theorem is about a model, tied to the deployed bytes by hash
equality and execution.

A re-run by an independent reviewer at a later epoch (from block 224 394 737, 2026-11-13 23:58 UTC) found 354
validators and 589.4M NEAR, with the proved code in 206 pools and 86.3% of the stake: the same picture. The
numbers of this page stay those of the snapshot, which the live-state and origin readings are about.

Limits: a snapshot of one epoch; the shares are by validator stake, not by the number of delegators; the link
between the code and the source is the equality of the hash with the committed artefact; a rebuild from source
with the author's compiler did not match byte for byte (`REPRO.md`).

## NEAR stake by exit stage (same snapshot; `evidence/stake-by-stage.json`)

One pool per code hash was scanned with `tools/exitproof.py`; pools sharing a code hash share its stage unless they
hold a full-access key of their own.

| Exit stage | Share of stake | Pools | Why |
|---|---:|---:|---|
| **2 — proven exit** | **86.2%** | 196 | no code-change path; exit theorem registered on chain for the code hash |
| 1 — exit window | 0% | 0 | — |
| **0 — keyholder trust** | **13.8%** | 144 | 143 pools whose code has an `upgrade` method with no delay; 1 pool with a full-access key |

Live state of the stage-2 pools at block 224 223 218 (2026-11-12): 196 of 196 satisfy the theorem's solvency
precondition, have consistent share books and no access keys; 256 564 delegator accounts (`evidence/pools-live.json`).

## Valuable contracts (snapshot of 2026-11-12, `../tools/census_contracts.py`, raw data `../evidence/contracts-census.json`, 28 addresses picked by hand: bridges, tokens, DeFi, Intents, wNEAR, pools)

Aggregates only; the output for a named contract is produced on request (`../tools/exitproof.py <account>`).
The field `deployments` of each record is the number of rows the indexer lists, which are the first and the latest
code deployment: `1` means one deployment, `2` means at least two. For `intents.near` the chain shows 18 code
changes (`../intents-proof/evidence/intents-code-history.json`).

| | Contracts |
|---|---:|
| Scanned | 28 |
| **Stage 2** — no code-change path and an exit theorem (wNEAR, the poolv1 pool) | 2 |
| **Stage 1** — code can change only after a visible delay | 0 |
| **Stage U** — no code-change path found, no exit theorem | 4 |
| **Stage 0** — the code can change with no delay | 22 |
| … the weak link is one key | 9 |
| … the weak link is several keys of one account | 6 |
| … a DAO vote | 1 |
| … the guard is not identified (the methods exist, the roles cannot be read through views) | 6 |

A DAO is counted as "a DAO vote" only if its own code cannot be replaced behind the vote. A Sputnik DAO with
`auto_update` on accepts new code from its factory with no proposal (the `update` method of the DAO contract), so
it is counted by the keys of the factory account; 5 of the 22 contracts have such a DAO among the holders of the
power to change their code.

How the 22 can change: 7 have full-access keys on the contract account or an `add_full_access_key` method (some of
them an upgrade method as well), 4 use the standard upgrade plugin with no staging delay set, 11 have an upgrade
method of their own.

The conclusion for a user: "no full-access keys" does not mean "the code does not change" — the code of 22 of the
28 large contracts can be changed with no notice, for 9 of them by a single key.
