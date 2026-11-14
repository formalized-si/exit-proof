# Intents Proof: for standard tokens, the ledger of NEAR Intents never credits more than it holds

A machine-checked proof about the fungible-token ledger of the NEAR Intents contract (`intents.near`), tied to the
exact code deployed on mainnet in three steps: the deployed bytes are rebuilt from the public source, the Lean
model is replayed against those bytes receipt by receipt, and one-line changes of the model are shown to be noticed.

## The problem

Calls between NEAR contracts are asynchronous receipts with no automatic rollback, so every contract writes its own
compensation logic by hand, and a ledger can end up crediting an amount that a callback *reported* rather than an
amount that *arrived*. NEAR Intents keeps such a ledger for every token it accepts. Its own post-mortem of
2026-10-16 ends with "Please follow the advancements of formal verification", and NEAR named "applying it to the
NEAR protocol and core smart contracts" as its next step (2026-10-19).

What this proof covers and what it does not, stated first. It covers the **fungible-token** paths of the contract
and treats every receipt as able to fail. The 2026 incident of the contract itself was on the **multi-token**
deposit path, where a refund failed on a log-length limit (near/intents PR #362); that path has no theorem here
yet. And the headline holds for a token that behaves as the standard one: for a token that keeps part of a
transfer the statement is false, in the model (`T5`) and on the live contract (section "The live ledger").

## What is proved

Subject: `intents.near`, code hash `BtA1BEFNS619KkvXFsgcpQ21Tb5yMm32aaUkn7xNothk` (sha256 `a1afab98…2b547`,
1 297 551 bytes), version 0.4.5, source `near/intents@16d04f6e`; the deposit and withdrawal paths of NEP-141 tokens
(`contracts/defuse/src/contract/tokens/nep141/`).

The model is a two-contract world: the proved model of the token standard (`near-contract-standards` 5.29.0, from
`../token-standard/`) and the Intents ledger. Any account calls anything at any time; any receipt may fail before it
runs; any pending callback lands or is dropped. Lean 4.35, no `sorry`, axioms `propext`, `Quot.sound`,
`Classical.choice` (`lean/Axioms.lean` prints them for each of the 136 statements it lists: the theorems of the tables below and the lemmas they are quoted with).

| Theorem | In plain words |
|---|---|
| `T1_backing`, `T1_ledger_covered` | in every reachable state the sum of the ledger balances is at most the tokens the contract holds — with anything in flight, in any order, with any failures |
| `T1_supply` | the ledger's total supply equals the sum of its balances |
| `T1_can_pay` | the contract's token balance covers any withdrawal it has debited and queued for the token; that all of them are covered together is part of `T1_backing` |
| `T1_exact`, `T1_equality` | without four named events that leave tokens held but assigned to nobody, the ledger equals the holdings exactly whenever nothing is in flight |
| `T2_debit`, `T2_settles`, `T2_no_callback` | a withdrawal debits exactly its amount; after its callback the owner is down by exactly what left the contract, except when a withdrawal with `msg` fails before any token moves (below) |
| `T3_credit_only_on_arrival`, `T3_arrival`, `T3_covered` | a credit happens only in `ft_on_transfer` called by the token, after the tokens have arrived |
| `T4_authorised` and the statements around it | one step lowers a balance in six ways only, each with the checks the contract makes before it; where keys, role holders and pending refunds come from (section "Who can lower a balance") |
| `T5_fee_token_breaks_backing` | the assumption is needed: with a token that keeps a fee and reports the full amount, a deposit of 100 ends with ledger 100 and holdings 99 |
| `tok_reach` | inside the two-contract world the token stays a reachable state of its own model, so its proved properties hold there |

The exception in T2: a withdrawal with `msg` that fails before any token moves — the token's `ft_transfer_call`
receipt failed as a whole, or, for a withdrawal that also pays a storage deposit, the contract's own preparatory
receipt failed and no token receipt was sent. In both cases the contract keeps the full debit and refunds nothing;
the tokens stay in the contract assigned to nobody. Backing is not affected.
Every theorem has a concrete example that satisfies its hypotheses (`lean/Intents/Examples.lean`,
`lean/Intents/StrictExamples.lean`). What is modelled, with references into the source: `lean/NOTES.md`.

## Who can lower a balance

`T4_authorised`: if one step lowers the ledger balance of an account, the step is one of six.

| # | Step | What the contract has tested |
|---|---|---|
| 1 | the account's own `ft_withdraw` | the method is not paused, authentication by predecessor is enabled for the account, the account is not locked |
| 2 | one signed payload whose signer is the account | the signature verifies under a key registered for the account, the verifying contract is this contract, the deadline has not passed, the nonce is unused, the account is not locked. The balance falls by at most what the intents of the payload name, and the nonce stays used (`T4_nonce_kept`): the payload runs once |
| 3 | `ft_force_withdraw` | the caller holds `DAO` or `UnrestrictedWithdrawer` |
| 4 | the account's own `mt_transfer*` | as in 1, with the pause key `mt_transfer` |
| 5 | `mt_resolve_transfer`: the refund of a transfer call made to the account | the refund is at most the amount of that transfer and is taken once: a pending refund is created only by the transfer call it belongs to and is removed when it runs or fails (`T4_calls`) |
| 6 | `mt_force_transfer*` | the caller holds `DAO` or `UnrestrictedWithdrawer` |

Where the things these six rest on come from:

- **Keys** (`T4_key_power`). A key becomes a key of an account only by the account's own `add_public_key` or by a
  payload signed with a key the account already has.
- **Roles** (`T4_role_change`, `T4_roles_from_initial`, `T4_force_from_initial`). A holder of a role is made only by
  `acl_grant_role` called by a super-admin or by an admin of that role. If at the start there is no super-admin and
  no admin of a role, its holders never grow. **A super-admin can make itself a holder of any role with one call**
  (`T4_super_admin_can_take_any_role`), so while a super-admin exists ways 3 and 6 are open to it.
- **Switches** (`T4_switches`, `T4_pause_power`, `T4_lock_power`, `T4_auth_flag_power`). Pausing and locking change
  no balance. The authentication flag of an account is switched only by the account itself, while it is not locked,
  or by a holder of the roles named in the statement.
- **Signatures** (`T4_signed_by_holder`). Under one named assumption — a signature that verifies under a key was
  made by the holder of that key (`Unforgeable`) — a payload that lowers a balance was signed by the holder of a key
  registered for the account.

These statements are about the strict world (`lean/Intents/Strict.lean`, `Auth.lean`): a refund belongs to a transfer
call, an operation of an owner carries its authorisation, and the role table changes by the rules of near-plugins
only. A step of the strict world is zero or more steps of the world of T1–T3 (`strict_refines`), so T1–T3 hold in
it (`strict_reach`). The earlier statement `T4_who_can_lower`, about the world where a refund, a signature and the
role table are arbitrary, is unchanged.

Limits. Signature verification and the decoding of a payload are one abstract function, and salted nonces are not
modelled, so the model admits more payloads than the contract. For a `TokenDiff` intent the statement bounds the
amount, not the destination. Keys and refunds are proved per step, not along a whole run. For wNEAR the statement
is still the earlier one (`W4_who_can_lower`): an unbounded refund step, assumed authorisation, an unrestricted
role table.

## wNEAR and the path to native NEAR

wNEAR (`wrap.near`) is not the plain standard token: it has `near_withdraw`, which the Intents contract calls to
unwrap wNEAR into NEAR. `lean/IntentsW/` is a second two-contract world, with the proved model of the wNEAR contract
(`../wnear-proof/`, copied unchanged as `lean/WNear/`) in place of the standard token; the contract model
(`lean/Intents/Ledger.lean`) is the same file.

| Theorem | In plain words |
|---|---|
| `W1_ledger_covered`, `W1_backing`, `W1_kept` | the ledger of `nep141:wrap.near` is at most the wNEAR the contract holds, in every reachable state, with any receipt failing |
| `W2_debit`, `W2_settles` | a wNEAR withdrawal settles exactly, with the same exception as T2 |
| `W3_credit_only_on_arrival`, `W3_arrival` | a credit happens only when wNEAR has arrived |
| `W4_who_can_lower` | the seven ways a balance can be lowered, each with its condition |
| `N2_burn`, `N2_unwrap_succeeds` | unwrapping burns exactly the amount debited from the ledger, and by the state alone `near_withdraw` cannot fail |
| `N3_forward`, `N3_near_le` | the callback forwards exactly that amount of NEAR; NEAR sent ≤ wNEAR burnt ≤ NEAR received |
| `N4_*` | which receipt failed → what happens to the ledger, to the wNEAR and to the NEAR (`lean/NOTES.md`, section 12): when the unwrap or its callback fails, the ledger debit is kept |
| `tok_inv`, `tok_step` | the token side of this world stays a state of the wNEAR model |

Replay on the deployed wasm (the 4 000-trace run): 41 796 receipts that touch wNEAR, 41 217 compared, 0 disagree. Not proved for
wNEAR: exact equality at rest, the NEAR balance of the contract as a whole, the refund of NEAR after a failed
forward. Of the four one-line changes of the new functions three are noticed by the replay. The fourth, an unwrap
that ignores the account lock, no receipt can show: the contract tests the lock of the signer once per payload,
before any intent runs, and the model does the same (`MUTANTS-REVIEW.md`, section 5).

## How the proof is tied to the deployed code

| Step | Result |
|---|---|
| Source ↔ deployed bytes | **byte-identical**: the commit the contract names in its own `contract_source_metadata`, built with `cargo near build reproducible-wasm` in the image it names, gives sha256 `a1afab98…2b547`, the hash of the code at `intents.near` (`scripts/rebuild.sh`, `evidence/rebuild_run.log`) |
| Model ↔ deployed bytes | 4 000 random traces of the deployed wasm on the nearcore runtime, standard token. Receipt by receipt through the ledger functions: 260 321 receipts on the contract, 257 605 agree, **0 disagree**; the outcome of 2 716 was not compared — 1 615 failures the harness forced and 966 receipts that ran out of the attached gas (the model has no gas; that they changed nothing is compared), 135 payloads whose signature does not verify (the model has no ed25519). Token and contract together through `Intents.stdStep`, the step function of the two-contract world the theorems are about: 84 636 receipts on the token and 126 755 on the contract, 209 557 agree, **0 disagree**, 1 834 failed for gas with nothing changed; compared after each are the ledger of the token's id, the token balance of the contract and every watched token balance (the wNEAR world, `IntentsW.step`, is not replayed this way). Fee-keeping mock token: 25 688 receipts, 0 disagree. Mock token with malformed replies: 25 688 receipts, 0 disagree (`evidence/conformance.json`) |
| Are the proofs themselves sound? | re-checked outside the elaborator: `leanchecker --fresh` replays every declaration in the Lean kernel, and `nanoda`, an independent kernel written in Rust, checked 62 496 declarations with no errors (`lean/kernel-check.sh`, `evidence/kernel_check.txt`) |
| Is the replay sensitive? | 121 one-line changes of the model: our own 11 (a credit one unit too large, a debit that ignores a lock, a callback that refunds everything, …), 23 written by an independent reviewer (permission checks, pause switches, the length limit of a token's reply, extreme amounts), 38 added so that every guard of the model and the step function of the world have at least one, and 49 for the strict world (the refund of a transfer call, the admission of a signed payload, public keys, the rules of the role table). **114 are noticed**: 55 by both replays, 40 by the receipt replay only, 19 by the world-level replay only. The other 7 no receipt can show: `ft_withdraw` debiting another owner (the method has no owner argument: the wasm debits the predecessor); a storage deposit on `ft_withdraw` / `ft_force_withdraw` (they have no such argument); an amount or a balance above the `u128` range; and two lock tests inside intents, which a locked signer never reaches because its payload is refused before any intent runs. With each of the seven the Lean build fails: with four at a theorem (`T4_who_can_lower` three times, `T4_auth_flag_power`), with three only at a lemma that restates the changed definition, which is a weaker rejection — and for the two range guards among these it is proved that the invariant implies the guard in every reachable state (`startWithdraw_amount_guard_redundant`, `moveBal_destination_guard_redundant`). The unchanged model passes (`evidence/model_mutants.json`). The replay had first noticed 10 of the reviewer's 23: the traces did not exercise permission checks, the pause of intents, the edges of a token's reply and extreme amounts, and the replay decided some guards with a copy of its own. What was changed, and the score per guard: `MUTANTS-REVIEW.md`, section 5. What the replay still cannot see: gas, the signature check itself, the strict step of a whole signed payload (its intents are applied one by one), keys of implicit accounts, and the eleven guarded methods outside the ledger |
| Properties on the traces themselves | 463 687 receipts: "ledger ≤ holdings" checked 1 854 748 times, 0 violations; exact equality at rest 445 620 times, 0 violations; 13 647 calls of private callbacks by other accounts, all failed and changed nothing; 23 106 calls of the 24 role-guarded methods and of the role-table methods by accounts without the permission (the holder of any other role, an admin that is no grantee, the super-admin, no role), none ran — and on a local build with the role check of two forced transfers removed the same monitor fired 56 times in 200 traces (`evidence/source_mutants.json`, variant S7); on the fee-keeping mock the backing monitor fired on 400 of 400 traces (`harness/README.md`) |

The replay compares the contract's functions receipt by receipt; the token side of each trace is taken from the
trace. It is evidence from execution, not a proof about the wasm.

## The statements were re-derived blind

A second pass wrote its own Lean statements from the plain-language claims and the model's definitions alone,
froze them (a file kept outside this repository, sha256 `4a274ce4…`, 2026-11-12 22:19 UTC), and only then compared them with the theorems. Outcome for
seven claims: three are the same statement or follow from the theorems; two were proved in a stronger form (the
joint cover of all queued withdrawals; exact settlement without the bookkeeping field the first proof used); and
**two plain-language claims were wrong as worded** although the theorems were true — the exception of T2 was
stated too narrowly, and the list of who can lower a balance in T4 omitted two paths. Both are corrected in the
table above. One hypothesis of `T3_arrival` ("the entry was not in the list") does not hold for two identical
transfers in flight; the stronger form covers that case.

## The proof does not die with the next upgrade

`scripts/verify_upgrade.sh <commit | wasm | --tree dir>` is a gate for a candidate version of the contract. It has two
parts, because a run of random traces cannot see everything:

- **static** — the source files the model mirrors are unchanged since the certified commit; no place in the contract
  writes the ledger that did not write it before; the exported methods of the wasm are the same;
- **dynamic** — the candidate, built with the reproducible flow, runs on the nearcore runtime with the monitors
  silent, and every receipt agrees with the proved model.

`CARRIES OVER` needs both. If the run agrees but the static part finds a change, the verdict is `NEEDS REVIEW`, with
the changes listed; if the run disagrees, `DIVERGES`. About two minutes.

| Candidate | Result |
|---|---|
| `near/intents@fce0936b` (2026-11-10), the newest commit, 17 commits after the deployed one; not deployed | **`NEEDS REVIEW`**: the run agrees (625 traces, 40 279 receipts replayed and 25 652 more through the world's step function, 0 disagree, no monitor fired), the exports are the same and no ledger write site was added or removed (53), but three modelled files changed — the cached balance arithmetic of the intent engine and the handling of a new account type (`evidence/upgrade_4PMYYWqio2Q3.json`) |
| the deployed source with one line changed, 8 variants (`scripts/source_mutants.py`, `evidence/source_mutants.json`) | **8 of 8 rejected**, the unchanged source gets `CARRIES OVER`. 6 are seen by the run (`DIVERGES`): five changes of the ledger arithmetic and of the refund rules, and the role check removed from the forced internal transfers (`unauthorized_ran` fired 56 times, 71 receipts disagree with the model). 2 are invisible to the run and caught by the static part only (`NEEDS REVIEW`): a new entry point that credits the ledger, and a change that acts on one particular amount. (Removing the role attribute from `mt_force_transfer` alone changes no behaviour — the method delegates to `mt_force_batch_transfer`, which tests the role itself — so the variant removes it from both.) |

The last three were proposed by an independent reviewer of this kit, against a first version of the gate that had
only the dynamic part and passed all three. Since the traces call every guarded method from accounts without the
role, the run now sees one of the three itself — the removed role check; the other two stay invisible to any run of
random traces. A gate of this kind narrows what has to be re-read after an upgrade to the
listed files; it does not replace reading them.

One of the changes of the first kind is the "friendlier" variant of the documented exception in T2: built from the
real source, it makes the backing monitor fire on the traces — the same conclusion TLC reaches below.
`../tools/watch.py` reports the moment the code hash of a watched contract changes.

## A second formalization, model-checked

`tla/IntentsLedger.tla` states the same ledger in TLA+, written from the Rust source and from NEP-141 rather than
from the Lean model, and TLC explores every interleaving of receipts and every failure for a small scope
(`tla/run.sh`).

| Configuration | Result |
|---|---|
| 2 users, 2 tokens each, amounts up to 2, 4 operations | 1 029 218 distinct states, depth 16: no violation of `Backing`, `TokenConserved`, `ExactWhenQuiet`, `CanPay` |
| 2 users, 3 tokens each, amounts up to 2, 5 operations | 78 961 324 distinct states (599 938 047 generated), depth 20: no violation (`tla/out/Large.log`) |
| the token keeps a fee and reports the full amount | `Backing` violated, shortest counterexample of 3 states |
| a variant of the contract that refunds a withdrawal whose `ft_transfer_call` receipt failed | `Backing` violated, shortest counterexample of 8 states |

The last row explains the exception in T2. The deployed code keeps the debit when the token's `ft_transfer_call`
receipt fails; TLC shows that the friendlier alternative is unsafe: if the transfer went through and only the
token's settlement callback was dropped, a refund would credit tokens that have left the contract. Keeping the
debit is what backing costs under "any receipt may fail".

`ExactWhenQuiet` is the model-checked form of `T1_equality`: with nothing in flight, the ledger plus the tokens
that the code assigns to nobody equals the holdings exactly.

## Assumptions

| Assumption | About | Status |
|---|---|---|
| The token behaves as the standard one | the token | needed (`T5`). Measured for the 395 fungible tokens the ledger holds: 371 have a verdict from runs of their deployed code — 355 behave as the standard, 14 deviate, 2 are under review; 201 of the 355 have an extension that changes transfers when switched on (`../evidence/token-census.json`, `../tools/token_check.py`) |
| A callback reads the outcome of the receipt it is chained to; a receipt is atomic | NEAR | taken; consistent with every replayed receipt |
| No arbitrary receipt leaves the contract's own account | the contract | taken. Three powers of the role `DAO` are outside it — a call from the contract's account (`admin_call`), a full-access key, a code upgrade. **A holder of these powers can break every theorem above**; by the exit stages of this repository the contract is at stage 0. `acl_init_super_admin` is private to the contract's account and falls under the same assumption |
| A valid signature under a key was made by the holder of that key (`Unforgeable`) | the caller | taken, as the hypothesis of `T4_signed_by_holder` and of nothing else. `T4_authorised` says "the signature verifies under a key registered for the signer" and does not use it |
| Signature verification, the hash and the decoding of a payload are one abstract function (`SCfg.valid`); salted nonces are not modelled; a `TokenDiff` is a move of the signed amount to a destination the signer did not choose | the contract | taken. The model admits more payloads than the contract does, and the statement about a `TokenDiff` is about its amount only. Internal operations are moves that keep the total |
| The public keys, the used nonces and the role table (super-admins, admins, holders) at the start are arbitrary | the contract | taken. The statements about roles are relative to the initial table; the live table is not read here |
| A direct call by an account is a receipt whose predecessor is that account; the block time is an input of a step | NEAR | taken |
| Authorisation, refunds and the role table in the wNEAR world are as before: assumed, unbounded, unrestricted | the caller, the contract | not removed for wNEAR (`W4_who_can_lower`) |
| The model has the ledger of one token id | the contract | taken: the balances of other ledger ids are not modelled, and the statements are about one id at a time. The replay compares the receipts that concern the id of the trace's token; the receipts of other ids are counted and left out (`lean/NOTES.md`, section 4, item 10, and section 15) |
| Gas, log length and storage staking are not modelled | NEAR | any receipt may fail, but nothing is proved about a callback getting enough gas |

## The live ledger

The theorems speak about the deployed code with a token that behaves as the standard. This is the reading of the
live contract next to them: for every fungible token id in the ledger of `intents.near`, at one block, what the
ledger says its accounts hold (`mt_supply`) against what the contract holds at the token (`ft_balance_of`), grouped
by the verdict of the token's deployed code (`../tools/intents_backing.py`, `../evidence/intents-live-backing.json`;
block 224 299 938, 2026-11-13).

| Verdict of the token's code | ledger = held | held > ledger | ledger > held | not readable |
|---|---|---|---|---|
| STANDARD | 77 | 15 | 0 | 0 |
| STANDARD + EXTENSIONS | 235 | 27 | 0 | 0 |
| DEVIATES | 12 | 1 | 1 | 0 |
| UNDER REVIEW | 1 | 1 | 0 | 0 |
| NOT RUN | 15 | 3 | 0 | 2 |
| NOT CHECKED | 0 | 0 | 0 | 1 |
| CODE FOLLOWS ANOTHER ACCOUNT | 1 | 0 | 1 | 0 |
| NO CODE | 0 | 0 | 0 | 3 |
| all 396 | 341 | 47 | 2 | 6 |

- **For the 354 tokens whose code has a standard verdict the ledger never exceeds the holdings**: equal for 312,
  tokens assigned to nobody for 42 (the four events of `T1_exact`, and plain transfers to the contract).
- **The ledger exceeds the holdings for two tokens, both outside the assumption.** `ninu-4.nearlytrade.near`
  (verdict DEVIATES): its code keeps a tax on a transfer and the tax is switched on, which is the case of `T5`; the
  ledger shows 188 951.48, the contract holds 187 758.77. `nvdastest.optimal-bone.near`: its code is a global
  contract referenced by account id, so another account can replace it and no verdict is given; ledger 119 083 907,
  held 109 083 907 base units.
- Six ids are not readable as tokens (three accounts without a contract, three whose `ft_balance_of` did not answer).
- The census of 2026-11-12 counts 395 tokens and 355 standard verdicts; this reading counts 396 and 354. One id was
  added to the ledger since, and the census gave a verdict to the code that another account had published for
  `bean-be9966.random-test-launcher.near` on that day, while this reading gives none to a token whose code another
  account can replace.
- This is a reading, not a proof: it says where the live state stands at one block, and it is the reason the
  headline carries the words "for standard tokens".

## Not covered

Multi-token (NEP-245) and NFT paths: no theorem, their ledger arithmetic is only replayed. Gas. The signature
standards themselves and the binding of a signature to the fields of its payload; salted nonces; the matching of
`TokenDiff` intents and their fees (moves that balance by assumption, `lean/NOTES.md` §4, item 7; the generator of
the replay makes no `token_diff` intent and no `auth_call`, so this path is not replayed either); the pause of
`intents` for the internal transfers of a payload. Who can lower a balance in the
wNEAR world beyond the earlier statement. A statement along a whole run for keys and for refunds (they are proved
per step: `T4_key_power`, `T4_calls`). Liveness. A proof about the bytes. The theorems are about one deployed code
hash and last until the next upgrade of the contract. They speak about states reachable from an empty ledger under
that code; the live ledger also went through earlier versions of the contract, which is why the live reading is
shown next to them. The account has had 19 code hashes: it was created without code on 2024-11-01, and its code
changed 18 times between 2024-11-05 and 2026-10-07, the last time to the code proved here
(`evidence/intents-code-history.json`, read from archival state; each row can be checked with one `view_account` at
its block).

## Re-check

`./check.sh --mutants --tla` took 38 minutes on a fresh copy with nothing built, on a shared 32-core machine under
load (`evidence/clean_check_run.txt`); with the harness already built it took 26 minutes on another machine of the same kind
(the run of `evidence/check_run.txt`). `evidence/PROVENANCE.json` records which sources each evidence file was made from
(`scripts/source_hash.py --check`). It needs Linux x86-64, `elan`,
`rustup`, a C/C++ compiler, cmake, libclang, python3, and java for `--tla`. Plain `./check.sh`: pinned wasm files,
Lean build and axioms, harness build,
monitors on 1 000 traces, replay through the model. `./check.sh --mutants` adds the model mutants,
`./check.sh --rebuild` the rebuild from source (docker, cargo-near 0.22), `./check.sh --tla` the TLC runs (java). Exit status 0 only if everything holds.
`TRACES=4000 MOCK_TRACES=400 ./check.sh` repeats the numbers above.

## Layout

| Path | Contents |
|---|---|
| `lean/` | model (`Intents/Ledger.lean`, `World.lean`), theorems (`Backing.lean`, `Theorems.lean`, `Exact.lean`, `FeeToken.lean`), the strict world and the statements about who can lower a balance (`Auth.lean`, `Strict.lean`, `StrictTheorems.lean`, `StrictKeys.lean`), the wNEAR world (`IntentsW/`, `WNear/`), examples, the replay executable (`Main.lean`), `NOTES.md` |
| `harness/` | trace generator on near-contract-sim (nearcore 2.14.0), monitors, two mock tokens, the wasm files with pinned hashes |
| `FORMAT.md` | the trace format |
| `tla/` | the TLA+ specification, four configurations, `run.sh`, TLC logs |
| `scripts/` | replay of traces through the model, model mutants, rebuild from source, the upgrade gate (`verify_upgrade.sh`) and its source mutants |
| `MUTANTS-REVIEW.md` | why 13 of an independent reviewer's 23 changes of the model went unnoticed, what was changed, and the score of every guard of the model |
| `evidence/` | results of the runs quoted above |
