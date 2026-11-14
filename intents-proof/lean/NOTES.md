# Notes on the model of the Intents token ledger

Source: `near/intents` at commit `16d04f6ec4401263f8914638710260da50bb46b0` (version 0.4.5, the
commit named by `contract_source_metadata` of `intents.near`), read from a local clone in `src/intents/` (not part
of this repository; `../scripts/rebuild.sh` clones the same commit).
Paths below are relative to `src/intents/contracts/defuse/` unless they start with `crates/`.
The deployed build uses `--features=contract` (`Cargo.toml:93-100`): no `imt`, no `far`.

Scope: the ledger entries of **one NEP-141 token `T`** (ledger token id `nep141:T`), its deposit
path, its withdrawal paths, and everything else that can write those entries, composed with the
proved model of the token (`ProvedFT`, near-contract-standards 5.29.0 — the version this
repository pins, `Cargo.toml:140` of the workspace).

## 1. State

| Contract state | Where | In the model |
|---|---|---|
| `accounts[a].token_balances[nep141:T]` | `src/contract/accounts/state.rs:10` | `Ledger.bals` (association list, 0 when absent) |
| `state.total_supplies[nep141:T]` | `src/contract/state/mod.rs:17` | `Ledger.supply` |
| `Lock<Account>.locked` | `core/src/lock.rs:15-24` | `Ctl.locked` |
| account flag "auth by predecessor id" | `src/contract/accounts/mod.rs:79-130` | `Ctl.authOff` |
| near-plugins `Pausable` keys | `src/contract/mod.rs:74-78` | `Ctl.paused` (`"ALL"` pauses everything) |
| near-plugins `AccessControllable` grants | `src/contract/mod.rs:51-73` | `Ctl.roles` |
| public keys, nonces, salts, fees, relayer keys | — | not modelled (they authorise, they hold no tokens) |
| balances of every other token id | — | not modelled; the model is per token id and the ids do not interact (section 4, item 10) |

Whether an account entry exists is not modelled: for these paths existence only decides which
error a failing call reports (`AccountNotFound` or `BalanceOverflow`).

## 2. Methods that write the ledger of `nep141:T`

Every write of `token_balances` / `total_supplies` in the contract (`grep` over `src/`):
`tokens/mod.rs:49,62` (`deposit`), `:108,114` (`withdraw`), `:202,209`
(`resolve_deposit_internal`), `tokens/nep245/core.rs:188,195` (`internal_mt_batch_transfer`),
`tokens/nep245/resolver.rs:82,90` (`mt_resolve_transfer`), `intents/state.rs:163,189`
(`internal_add_balance`, `internal_sub_balance`).

| Method | Source | Guard | Effect on `nep141:T` | Promises | Model |
|---|---|---|---|---|---|
| `ft_on_transfer(sender_id, amount, msg)` | `src/contract/tokens/nep141/deposit.rs:18-75` | not paused (`#[pause]`, key `ft_on_transfer`); `amount > 0`; `msg` parses; token id is `nep141:<predecessor>` | `deposit`: balance of the account named by `msg` (sender if empty) and total `+amount` | none; returns the value `"0"`. With `execute_intents` in `msg`: runs them in the same receipt (`refund_if_fails`) or sends them to itself detached | `Step.onTransfer`, `credit` |
| `ft_withdraw(token, receiver_id, amount, memo, msg)` | `…/nep141/withdraw.rs:25-50` | not paused (key `ft_withdraw`); exactly 1 yoctoNEAR; auth by predecessor enabled for the caller; then `withdraw`: caller not locked, `amount > 0`, balance and total sufficient | `withdraw`: caller's balance and total `-amount` | `T.ft_transfer` (or `ft_transfer_call` when `msg` is given) with 1 yocto, then `ft_resolve_withdraw(token, owner, amount, is_call)` with 15 Tgas | `Step.ftWithdraw (.method p)`, `startWithdraw` |
| `FtWithdraw` intent | `core/src/intents/tokens.rs:206-231`, `src/contract/intents/state.rs:197-200` | intents not paused (key `intents`); valid signature of a key of the signer (not modelled); then as above without the yocto and predecessor checks | as above for the signer; with `storage_deposit` also debits the signer's `nep141:<wNEAR>` | as above; with `storage_deposit`: `wNEAR.near_withdraw` → `do_ft_withdraw` → one receipt `T.storage_deposit(receiver)` + `T.ft_transfer[_call]` → `ft_resolve_withdraw` | `Step.ftWithdraw .intent`, `Step.doFtWithdraw` |
| `ft_force_withdraw(owner_id, …)` | `…/nep141/withdraw.rs:199-225` | caller holds `DAO` or `UnrestrictedWithdrawer`; 1 yocto; **no pause check, lock ignored** (`force = true`) | `withdraw` from `owner_id` | as `ft_withdraw` | `Step.ftWithdraw (.force c)` |
| `do_ft_withdraw(withdraw)` | `…/nep141/withdraw.rs:117-151` | `#[private]`; with a storage deposit: the `near_withdraw` result must be a success with an empty value | none | the token receipt | `xferBatch`, `Step.doFtWithdraw`, `Step.tokXfer` |
| `ft_resolve_withdraw(token, sender_id, amount, is_call)` | `…/nep141/withdraw.rs:156-194` | `#[private]` | `used` from promise result 0 (below); `refund = amount - used`; if positive, `deposit(sender_id, refund)` | none; returns `used` | `Step.resolveWd`, `Rs.used`, `resolveWithdraw` |
| `ft_resolve_deposit(receiver_id, contract_id, amount)` | `…/nep141/deposit.rs:80-93`, `tokens/mod.rs:152-220` | `#[private]` | burns from `receiver_id` what promise result 0 asks, capped | none | **not a step**: nothing in the contract schedules it (the notify action is commented out, `deposit.rs:46-61`); it can only lower balances |
| `mt_transfer`, `mt_batch_transfer`, `mt_transfer_call`, `mt_batch_transfer_call` | `…/nep245/core.rs:15-104`, `:164-216` | key `mt_transfer` not paused; 1 yocto; auth by predecessor; sender not locked; sender ≠ receiver; amount > 0 | moves balance sender → receiver; total untouched | `*_call`: `receiver.mt_on_transfer` then `mt_resolve_transfer` | `Step.move .owner`, `moveBal` |
| `Transfer`, `TokenDiff` intents (and fees) | `core/src/intents/tokens.rs:84-133`, `core/src/intents/token_diff.rs`, `core/src/engine/state/deltas.rs:136-164,267-283` | valid signatures; signer not locked; at the end of `execute_intents` the recorded deltas of every token must cancel (`finalize`), otherwise the receipt fails | balances move between accounts; total untouched | optional notification | `Step.move .owner` (one move per pair; see section 4) |
| `mt_resolve_transfer` | `…/nep245/resolver.rs:16-122` | `#[private]` | refund receiver → previous owner, capped by amount and by the receiver's balance; total untouched | none | `Step.move .refund` |
| `mt_force_transfer*` | `…/nep245/force.rs:16-110` | `DAO` or `UnrestrictedWithdrawer`; lock ignored | as `mt_transfer*` from any owner | as above | `Step.move (.force c)` |
| `NativeWithdraw`, `StorageDeposit`, `AuthCall` intents, `storage_deposit` of withdrawals | `src/contract/intents/state.rs:212-339` | — | `withdraw` of the signer's `nep141:<wNEAR>` only | to wNEAR, then to a third contract | not modelled in this world (they write another token id; for that id see section 9); `Step.meStorageDeposit` covers the call `T.storage_deposit` they can cause |

How `ft_resolve_withdraw` reads the promise result (`withdraw.rs:164-181`,
`crates/near/utils/src/promise.rs:39-72,82-88`):

| `is_call` | promise result | `used` |
|---|---|---|
| false | success with an empty value | `amount` |
| false | failed, or success with a non-empty value | `0` (full refund) |
| true | success, ≤ 44 bytes, a JSON `U128` `u` | `min(u, amount)` |
| true | success, ≤ 44 bytes, not a JSON `U128` | `0` (full refund) |
| true | failed, or longer than 44 bytes | `amount` (**no refund**; comment at `withdraw.rs:169-171`, doc comment at `core/src/intents/tokens.rs:147-149`) |

## 3. The two-contract world (`Intents/World.lean`)

State: the token's contract state and settlement callbacks in flight (exactly `ProvedFT.Sys`),
the ledger, and three queues of the contract's own receipts in flight.

| Step | The receipt it stands for |
|---|---|
| `tokCall p d m rs` | any receipt on the token from any account `p ≠ contract`: any method, deposit, promise results |
| `tokResolve i res` | the token's `ft_resolve_transfer` for its `i`-th callback in flight; `res` is the receiver's answer, except for a transfer to the contract, where it is the contract's own answer |
| `tokResolveFails i` | that callback fails before it runs (gas) |
| `tokNearIn x` | NEAR arrives at the token |
| `onTransfer i recv ok` | the contract's `ft_on_transfer` for the transfer behind callback `i`; `ok = false` is a failure for a reason outside the model |
| `ftWithdraw via w` | `ft_withdraw` / `FtWithdraw` intent / `ft_force_withdraw` |
| `doFtWithdraw j ok` | `do_ft_withdraw` after wNEAR `near_withdraw` (storage-deposit path) |
| `tokXfer j` / `tokXferFails j` | the token receipt of withdrawal `j` executes / fails before any effect |
| `meStorageDeposit acc d` | `T.storage_deposit(acc)` sent by the contract |
| `resolveWd k` / `resolveWdFails k` | `ft_resolve_withdraw` runs / fails before it runs |
| `move auth src dst amt` | an internal operation moving `amt` |
| `admin a` | pause, unpause, lock, unlock, auth flag, role change |

Reachable states: from an initial token state (`ProvedFT.InitOK`) and an empty ledger, any
sequence of steps. A step whose guard fails changes nothing, so "any account calls anything at
any time" includes all failing calls.

## 4. Hypotheses and simplifications

Each is labelled: **NEAR** (how the protocol runs receipts), **token**, **caller**, or
**contract** (the contract's own code outside these paths).

1. **token — the token is the standard one.** `T` behaves as `ProvedFT.exec`
   (near-contract-standards 5.29.0 `FungibleToken`, example-token wiring) and exports no other
   method. In particular `ft_transfer` returns an empty value, `ft_transfer_call` returns the
   `U128` of `ft_resolve_transfer`, and the amount notified to `ft_on_transfer` is the amount
   credited. `T5` shows the statement fails without the last part. Consequence used in the
   world: every other call the contract can send to `T` fails on a standard token
   (`near_withdraw`, `on_auth`, `mt_on_transfer`, `nft_transfer*`, `mt_batch_transfer*` are not
   methods of it). wNEAR is not such a token (it has `near_withdraw`), so `T = wNEAR` is outside
   the statements of sections 1–8; sections 9–14 are about wNEAR.
2. **NEAR — a callback reads the outcome of the receipt it is chained to, after it.** The
   token's settlement callback for a transfer to the contract reads the result of the contract's
   `ft_on_transfer` (`"0"` or a failure) and cannot run before it. `ft_resolve_withdraw` reads
   the result of the token receipt: of `ft_transfer`, or the value `ft_resolve_transfer`
   returned for `ft_transfer_call`, or a failure. A failed receipt changes no state.
3. **NEAR — a receipt is atomic and one batch is one receipt.** `storage_deposit` +
   `ft_transfer` of `do_ft_withdraw` either both apply or neither (`xferBatch`).
4. **NEAR — the encoding of a `U128` return value.** Not an assumption: `Intents/Json.lean`
   proves that the reader (`serde_json::from_slice::<U128>` as modelled in `ProvedFT`) returns
   what near-sdk's writer wrote (`parse_enc`).
5. **contract — no arbitrary receipt from the contract's own account.** A receipt on the token
   with the contract as predecessor exists only as `tokXfer` or `meStorageDeposit`. This rules
   out, by assumption: `admin_call` (`src/contract/admin_call.rs:10-31`, role `DAO`: any function
   call or transfer from the contract's account, including `T.ft_transfer` and the contract's own
   `#[private]` callbacks), a full-access key on the account (`add_full_access_key`,
   `src/contract/admin.rs:9-14`, role `DAO`), and a code upgrade (`upgrade`,
   `src/contract/upgrade.rs:11-25`, roles `DAO`, `Upgrader`). **These three powers are outside
   every theorem; a holder of them can break all of T1–T4.** Relayer keys
   (`src/contract/intents/relayer.rs`) are function-call keys limited to the contract's own
   `execute_intents` and send nothing to the token.
6. **caller — signatures and the intent engine are not modelled.** An `FtWithdraw` intent is
   the step `ftWithdraw .intent` (the model does not check who signed), an internal operation
   is `move .owner`. The statement "authorised by the owner" for these two is the engine's
   signature check (`core/src/engine/mod.rs:42-83`), taken as given.
7. **contract — internal operations are single moves.** `mt_transfer*`, `Transfer`,
   `TokenDiff`, fees and `mt_resolve_transfer` are modelled as moves `src → dst` that keep the
   total. This is what the code does for the total: `internal_add_balance` /
   `internal_sub_balance` do not write `total_supplies`, a transfer subtracts and adds the same
   amount, and `TokenDiff` deltas must cancel per token in `Deltas::finalize`. A multi-party
   `TokenDiff` is one atomic receipt; the model reaches its end state through intermediate
   states that do not exist on chain, which can only add reachable states.
8. **contract — pause checks of internal operations are dropped** (`move` ignores
   `mt_transfer` / `intents` pauses): more behaviours, same theorems.
9. **NEAR — gas, logs, storage staking are not modelled.** Every receipt may fail before it
   runs (`ok = false`, `tokXferFails`, `tokResolveFails`, `resolveWdFails`,
   `doFtWithdraw _ false`). Not covered: a claim that a callback *does* get enough gas
   (15 Tgas for `ft_resolve_withdraw`, `min_gas` for the token call), log-length failures of
   `check_refund`, and NEAR balance for storage.
10. **one token.** The model has the ledger of one token id. Other ids are independent: every
    write is keyed by the token id, `ft_on_transfer` derives it from the predecessor
    (`deposit.rs:27`), withdrawals from the `token` argument.
11. **amounts are natural numbers**; each `checked_*` of the code is a guard, and `amount` of a
    withdrawal is at most `u128::MAX` (its type).

## 5. Statements, and where they differ from the first wording

`Intents/Theorems.lean`, `Intents/Exact.lean`, `Intents/FeeToken.lean`; `Axioms.lean` prints
the axioms (`propext`, `Quot.sound`, `Classical.choice` only; no `sorry`, no `native_decide`).

* **T1** `T1_backing`: ledger total + withdrawals in flight (full amounts) + transfers to the
  contract not yet credited ≤ tokens held + what those withdrawals already moved out.
  `T1_ledger_covered`: ledger total ≤ tokens held in **every** reachable state, not only quiet
  ones. `T1_supply`: `total_supplies` = sum of balances. `T1_can_pay`: the contract's balance
  covers every withdrawal not yet sent. Added to the first wording: the term for incoming
  transfers (needed for induction).
  **Equality** does not follow from "nobody sent tokens outside `ft_transfer_call`" alone.
  Tokens end up held but assigned to nobody in exactly these events: a plain `ft_transfer` to the
  contract; a failed deposit whose token-side refund callback is dropped; a withdrawal with
  `msg` whose `ft_transfer_call` receipt fails (debit kept); a dropped `ft_resolve_withdraw`
  while a refund was due. `Intents/Exact.lean` proves the exact version: `T1_exact` (starting
  from an empty token balance, without those four events — the predicate `Lossless` — ledger
  total + owed in flight = tokens held, in every state) and `T1_equality` (in a quiet state the
  ledger total equals the tokens held). Extra hypothesis there: `Env.Sane` for the token
  deployment (label **token**: storage parameters, as in the token model).
* **T2** `T2_debit`, `T2_settles`, `T2_no_callback`. Adjusted: "minus exactly what left" holds
  with one exception that the source documents — the `ft_transfer_call` receipt failed, nothing
  left, nothing refunded. `Rs.left` is bookkeeping set in three places of `World.step` from the
  token's balances before and after the token receipt; no guard or effect reads it.
* **T3** `T3_credit_only_on_arrival`, `T3_arrival`, `T3_covered`.
* **T4** `ledger_step`, `T4_who_can_lower`, `T4_switches`, `T4_pause_power`, `T4_lock_power`;
  the powers of hypothesis 5 are outside.
* **T5** `Examples.T5_fee_token_breaks_backing`: with a token that keeps a fee of 1 and reports
  the full amount, one deposit of 100 ends with ledger 100, held 99, nothing in flight.
* `tok_reach`: the token part of every reachable world is a reachable state of `ProvedFT`, so
  the token properties P1–P5 hold inside the two-contract world.
* `parse_enc`: the JSON reader returns the `U128` the writer wrote.

Non-vacuity: `Intents/Examples.lean` (concrete runs for every theorem, evaluated by `decide`).

## 6. Not proved

* The NEP-245 paths (`tokens/nep245/deposit.rs`, `withdraw.rs`): no theorem. There is no proved
  model of an NEP-245 token to compose with. Their ledger arithmetic is in the executable only
  (same `credit` / `debit`) and is compared with the wasm (section 7).
* `T = wNEAR` (`near_withdraw` burns the contract's wNEAR after a ledger debit): no theorem
  in the world of section 3; proved in a second world, sections 9–14 (what is left open there:
  section 13).
* Anything about gas: that a callback gets enough gas, or that a third party cannot force a
  failure by gas.
* The signature check, nonces, deadlines, the intent engine, `TokenDiff` matching: taken as
  the abstraction of hypotheses 6 and 7.
* That the deployed wasm equals the model. Section 7 is a test on recorded receipts, not a
  proof.
* Liveness (that a withdrawal eventually settles).

## 7. Comparison with the deployed wasm

`intentsmodel` (`Main.lean`, description in `OBSERVABLE.md`) replays the harness traces
(`../FORMAT.md`) receipt by receipt. Runs of 2026-11-12, files `../harness/runs/t40.jsonl`
(standard token) and `m40.jsonl` (fee-keeping mock token), 40 traces each:

| run | receipts on the contract | agree | disagree | env (gas faults) | auth (signature-level rejections) | skipped |
|---|---|---|---|---|---|---|
| `t40.jsonl` | 3090 | 3029 | 0 | 44 | 17 | 0 |
| `m40.jsonl` | 1904 | 1879 | 0 | 25 | 0 | 0 |

"agree" compares success/failure, the ledger of every token id, the supplies, pauses, locks and
the return value. This checks the contract functions of `Intents/Ledger.lean` and the decode
layer on these receipts; it does not check the two-contract step relation (the token side is
taken from the trace).

## 8. Checking

```
./check.sh    # lake build, axioms of every theorem, forbidden tokens, replay
```

## 9. The world with wNEAR as the token (`IntentsW/`)

Sections 1–8 are about a token that is exactly the 5.29.0 standard. This part is about the
ledger id `nep141:<wNEAR>` (`nep141:wrap.near` on mainnet): wNEAR is the token, and the
contract also calls `near_withdraw` on it and sends the unwrapped NEAR on.

### 9.1 One more world, not a generalised one

There are now two worlds: `Intents/World.lean` (unchanged) and `IntentsW/World.lean`. The new
statements rest on these definitions and no others:

| Definitions | Status |
|---|---|
| `WNear/Model.lean` — the wNEAR contract (near/core-contracts `54f8267` `w-near/`, near-contract-standards 3.1.0) | copied unchanged from the wNEAR proof (`WNear/` is byte-identical to its source; that proof's conformance run: 2000 traces of the wNEAR wasm, 0 divergences) |
| `Intents/Ledger.lean` — `credit`, `debit`, `startWithdraw`, `Rs.used`, `resolveWithdraw`, `moveBal`, `adminStep` | unchanged; the same functions the standard-token theorems and the replay use |
| `Ann`, `Pend`, `annThird`, `annWd`, `depRes`, `depW`, `wdDone` of `Intents/World.lean` | unchanged |
| `IntentsW/World.lean` — the composition: `Fwd`, `Job`, `Ready`, `World`, `prW`, `depResW`, `retPRW`, `resOfW`, `xferBatchW`, `startWithdrawW`, `startUnwrap`, `Step`, `step`, `Init`, `Reach` | new (about 430 lines with comments; the step function is about 150 of them) |

Why not one world over an interface of token facts:

* The two token models have different types — the 5.29.0 model reads promise results as bytes
  and has `memo` / `msg` arguments, the wNEAR model reads a parsed value and has
  `near_deposit` / `near_withdraw` — and each was compared with its own wasm in its own form.
  An interface would be a new layer of definitions between them and the world, and every
  statement of sections 1–8, already kernel-checked and replayed, would have to be restated
  through it.
* wNEAR needs steps that do not exist for a standard token (the contract calls
  `near_withdraw` on the token; an `FtWithdraw` with `storage_deposit` debits the same ledger
  twice). A generic world would carry a switch for them, i.e. two worlds inside one definition.
* With a second world nothing that was proved before is touched (`Intents/` and `ProvedFT/` are
  byte-identical to the original), and the trusted base of the new statements is the table
  above. The price: the shape of the step function exists twice (14 steps there, 17 here).

### 9.2 State added

| Contract / protocol state | In the model |
|---|---|
| an unwrap whose `near_withdraw` receipt is in flight | `World.jobs : List Job` (`owner`, `amount`, what follows: `Fwd`) |
| a `do_*` callback ready to run, with the promise result it will read | `World.ready : List Ready` (`ok`: success with an empty value) |
| — (bookkeeping, read by no guard) | `uDebited`, `uBurned`, `uKept`, `nGot`, `nFwd` |

`Fwd` names what the callback does with the NEAR:

| `Fwd` | Intent | Callback | Source |
|---|---|---|---|
| `native r` | `NativeWithdraw` | `do_native_withdraw`: NEAR transfer to `r` | `src/contract/intents/state.rs:212-240`, `tokens/nep141/native.rs:11-19` |
| `storage c a` | `StorageDeposit` | `do_storage_deposit`: `c.storage_deposit(a)` | `state.rs:267-299`, `tokens/nep141/storage_deposit.rs:13-26` |
| `auth c` | `AuthCall` with `attached_deposit` | `do_auth_call`: `c.on_auth(..)` | `state.rs:305-339`, `intents/auth_call.rs:17-38` |
| `other t r` | `FtWithdraw` of another token, `NftWithdraw`, `MtWithdraw`, with `storage_deposit` | `do_ft_withdraw` / `do_nft_withdraw` / `do_mt_withdraw`: `t.storage_deposit(r)` + the transfer, one receipt | `tokens/nep141/withdraw.rs:54-106`, `nep171/withdraw.rs:58-110`, `nep245/withdraw.rs:62-131` |
| `ftw w` | `FtWithdraw` of wNEAR itself with `storage_deposit` | `do_ft_withdraw`: wNEAR `storage_deposit(w.receiver)` + `ft_transfer[_call]`, then `ft_resolve_withdraw` | `tokens/nep141/withdraw.rs:54-106,117-151` |

All five debit with `Contract::withdraw(.., force = false)` (`tokens/mod.rs:76-128`) and call
`ext_wnear::near_withdraw(amount)` with 1 yoctoNEAR and `NEAR_WITHDRAW_GAS` = 10 Tgas
(`crates/near/wnear/src/lib.rs:7`); each callback begins with
`require!(promise_result_checked_void(0).is_ok(), "near_withdraw failed")`.

### 9.3 Steps

As in section 3, with the token receipts executed by `WNear.exec`, and:

| Step | The receipt it stands for |
|---|---|
| `tokCall p d m rs` | any receipt on wNEAR from any account other than the contract and wNEAR itself |
| `ftWithdraw via w` | as before; with `w.sd = some d` (an intent) the debit is `w.amount` and then `d` from the same ledger (`startWithdrawW`), and a job `ftw w` starts |
| `unwrap owner x f` | an intent that unwraps (`f` is not `ftw`): `startUnwrap` = intents not paused, `debit .. false`; a job starts |
| `nearWithdraw j` | the `near_withdraw` receipt of job `j` executes on wNEAR (`WNear.exec`); the callback becomes ready with its outcome |
| `nearWithdrawFails j` | that receipt fails before any effect (out of gas) |
| `doJob k ok` | the `do_*` callback of the `k`-th ready job; `ok = false`: it fails before it runs. On a successful unwrap it sends the NEAR on (`nFwd`), and for `ftw w` puts `w` into the outbox; otherwise, for `ftw w`, `ft_resolve_withdraw` becomes ready with a failure |
| `tokXfer j` | the token receipt of a withdrawal of wNEAR, with the `storage_deposit` action before the transfer when `w.sd` is set |
| `meStorageDeposit acc d` | `wNEAR.storage_deposit(acc)` sent by the contract (`StorageDeposit` with `contract_id` = wNEAR) |

Reachable states start from `Init`: wNEAR in any state that satisfies the invariant of its
model (`WNear.Inv`), any settlement callbacks in flight that do not involve the contract, an
empty ledger, nothing of the contract in flight; the contract may already hold wNEAR.

## 10. Hypotheses added for wNEAR

Hypotheses 5–11 of section 4 carry over unchanged (in particular 5: `admin_call`, a full-access
key and `upgrade` are outside every theorem). Hypothesis 1 is replaced by W1–W3.

* **W1. token — wNEAR is the proved model.** wNEAR behaves as `WNear.exec` and exports no other
  method; at the start it satisfies `WNear.Inv` (no repeated keys, `total_supply` = sum of
  balances, NEAR covering supply and storage). For mainnet the wNEAR report checked the solvency
  part directly; conservation there rests on a test of the code wrap.near ran before its 2021
  upgrade (that report, finding 1).
* **W2. token — wNEAR does not call itself.** A receipt on wNEAR whose predecessor is wNEAR is
  only its own settlement callback (no access keys; assumption A4 of the wNEAR report).
  `Step.tokCall` therefore excludes `p = wNEAR`.
* **W3. token — the reply formats of wNEAR (near-sdk 3.1.0).** `ft_transfer` returns the empty
  value; the result of `ft_transfer_call` is the `U128` returned by `ft_resolve_transfer`,
  written as the same JSON string near-sdk 5 writes (`retPRW`, `encU128`); wNEAR's reader of the
  contract's answer `"0"` yields 0 (`prW`, by the parser of the 5.29.0 model, used on this one
  input: `unused_credited`). Not proved from the 3.1.0 sources; seen on the traces of section 14.
* **W4. NEAR — what the callback after `near_withdraw` reads.** `near_withdraw` returns the
  promise of its NEAR transfer to the caller, so the callback reads the outcome of that
  transfer; a transfer to an existing account cannot fail and the contract's account exists. So
  the callback reads a success with an empty value exactly when `near_withdraw` succeeded, and
  the NEAR has arrived by then (`Ready.ok`).
* **W5. NEAR — what comes back is not modelled.** NEAR is counted when it is sent: `nGot` when
  wNEAR creates the transfer to the contract, `nFwd` when a callback sends or attaches it. Not
  modelled: the refund of the attached yocto when `near_withdraw` fails, the refund of the
  deposit when the receipt a callback sent fails, the excess a `storage_deposit` of a third
  contract returns. Each of these only adds NEAR to the contract's account.
* **W6. contract — unwraps exist only as intents.** The methods `ft_withdraw`,
  `ft_force_withdraw`, `mt_withdraw`, `mt_force_withdraw`, `nft_withdraw`, `nft_force_withdraw`
  pass `storage_deposit: None` (`nep141/withdraw.rs:44,219`, `nep245/withdraw.rs:52,290`,
  `nep171/withdraw.rs:48,219`), and `NativeWithdraw`, `StorageDeposit`, `AuthCall` are intents.
  So every unwrap debit is guarded by the pause key `intents` (`intents/mod.rs:26`; the inline
  execution of a deposit message calls the same method, `nep141/deposit.rs:65`) and is never
  forced.
* **W7. contract — the receipts the contract sends to wNEAR.** `near_withdraw` (only as a job,
  after the debit), `ft_transfer` / `ft_transfer_call` with or without `storage_deposit` before
  it (a withdrawal of wNEAR), `storage_deposit(acc)`, a NEAR transfer (`Step.tokNearIn`). Every
  other call the contract can address to wNEAR (`on_auth`, `mt_on_transfer`, `nft_transfer*`,
  `mt_batch_transfer*`, alone or after `storage_deposit` in one receipt) is not a method of
  wNEAR and fails as a whole.
* **W8. caller — who signed is not modelled** (as hypothesis 6): `unwrap owner x f` is the
  intent of `owner`.
* **W9. contract — one `execute_intents` is several steps.** A receipt that runs several
  intents (or a deposit with inline intents) is modelled as their steps one after another; the
  model reaches the same end state through intermediate states that do not exist on chain.
* **W10. one token id.** This world has the ledger of `nep141:<wNEAR>` only. A withdrawal of
  another token with `storage_deposit` appears here as `unwrap .. (.other ..)` and in the world
  of section 3 as `doFtWithdraw`; the two worlds are not composed.
* **W11. NEAR — gas is not modelled** (as hypothesis 9): that 10 Tgas suffice for
  `near_withdraw`, 12 Tgas for `do_native_withdraw`, and so on, is not claimed. A receipt that
  runs out of gas is a `…Fails` step or `ok = false`.
* **Parameters.** `N2_unwrap_succeeds` and `N2_burn_is_debit` also assume `WNear.Env.Sane` for
  the wNEAR deployment (label **token**) and `S.c.near < cap`: wNEAR's NEAR balance is below the
  bound on any NEAR balance (label **NEAR**).

## 11. Statements for wNEAR

`IntentsW/Theorems.lean`, `IntentsW/Native.lean`, `IntentsW/TokenSide.lean`; axioms in
`Axioms.lean` (`propext`, `Quot.sound`, `Classical.choice` only). Non-vacuity:
`IntentsW/Examples.lean`.

* **W1 backing.** `W1_ledger_covered`: in every reachable state the sum of the ledger balances
  of `nep141:<wNEAR>` is at most the contract's wNEAR balance. `W1_backing`: the same with
  everything in flight, and with the wNEAR of failed unwraps (`uKept`) on the left side.
  `W1_kept`: ledger total + `uKept` ≤ wNEAR held. `W1_supply`, `W1_quiet`, `W1_can_pay`,
  `W1_can_unwrap` (the balance covers every `near_withdraw` in flight).
* **W2 settlement.** `W2_debit` (a withdrawal of wNEAR debits `amount`, plus the storage deposit
  when the intent has one), `W2_settles` (as `T2_settles`, with the same single exception),
  `W2_no_callback`.
* **W3 credit only on arrival.** `W3_credit_only_on_arrival`, `W3_arrival`, `W3_covered`.
* **W4 who can lower a balance.** `ledger_step` (every change of the ledger is one of six),
  `W4_who_can_lower` (seven cases: the six of `T4_who_can_lower` and an unwrap intent of the
  account itself — intents not paused, account not locked), `W4_switches`. Who may pause and
  lock: `T4_pause_power`, `T4_lock_power` (statements about `adminStep`, valid as they are).
* **The token side.** `tok_inv`: the token keeps `WNear.Inv` in every reachable state.
  `tok_step`, `tok_run`, `tok_reach` (with `me ≠ wNEAR`): every step of the world is zero, one
  or two steps of `WNear.sysStep`, so what the wNEAR proof shows along its own steps holds
  inside this world.
* **The native path.**
  * `N1_debit`, `N1_start`: an unwrap debits exactly `x`, from the owner only, and puts one
    `near_withdraw(x)` in flight.
  * `N2_burn`: when that receipt succeeds, the contract's wNEAR balance and wNEAR's supply drop
    by exactly `x`, nobody else's balance changes, and wNEAR sends the contract exactly one
    transfer of `x + 1`. `N2_unwrap_succeeds`: in a reachable state the receipt cannot fail for
    a reason of state. `N2_burn_is_debit`: both together.
  * `N3_forward`: the callback sends on exactly `x` and only after a successful unwrap; it
    touches neither the ledger nor wNEAR. `N3_books`, `N3_near_le`: in every reachable state
    `uDebited = uBurned + uKept + (in flight)` and `nFwd ≤ uBurned ≤ nGot`: the NEAR that left
    is at most the wNEAR burned, which is at most what was debited and at most the NEAR the
    unwrapping returned.
  * `N4_unwrap_fails`, `N4_callback_fails`, `N4_no_refund`, `N4_withdrawal_refund`: section 12.

Where the wording differs from the first one: the unwrap statements are about the NEAR *sent*
by the contract's callbacks and *sent* to the contract by wNEAR (W5); they are not statements
about the contract's NEAR balance. "Backing" for wNEAR was proved in the stronger form with
`uKept`. No statement was weakened to make it provable.

The observation from the harness, "when `near_withdraw` on wNEAR fails, the ledger debit of
wNEAR stays": confirmed for the model (`N4_unwrap_fails`, `N4_callback_fails`, `N4_no_refund`,
`W3_credit_only_on_arrival`: no step gives the amount back), and narrowed: the wNEAR is not
lost to another account, it stays in the contract's balance on top of the ledger (`W1_kept`);
and the receipt does not fail for a reason of state (`N2_unwrap_succeeds`) — on the traces of
section 14 all 5 failed `near_withdraw` receipts of 139 were gas faults forced by the harness.
The source documents it: "the `wNEAR` will not be refunded in case of fail"
(`core/src/intents/tokens.rs:155,434-435,470`, `core/src/intents/auth.rs:26-31`).

## 12. Which receipt failed → what happens

`x`: the unwrapped amount. "Kept": the amount is counted in `uKept` — it stays in the
contract's wNEAR balance on top of the ledger, assigned to nobody (`W1_kept`). "Unassigned": it
stays in the balance and no ledger entry stands for it, by `W1_ledger_covered` alone. The NEAR
column is about NEAR sent (W5); what NEAR returns to the contract by its own refund rule is
marked "not modelled".

An unwrap (`NativeWithdraw`, `StorageDeposit`, `AuthCall`, the storage deposit of a withdrawal
of another token id):

| Receipt that fails | Ledger `nep141:<wNEAR>` | wNEAR held by the contract | NEAR | Theorem / example |
|---|---|---|---|---|
| none | owner − x | − x, burned (supply − x) | wNEAR sends x + 1, the callback sends x on | `N1_debit`, `N2_burn`, `N3_forward`; example `native` |
| the intent's own receipt | unchanged | unchanged | none | `step` is the identity when `startUnwrap` fails; example |
| `near_withdraw` on wNEAR | − x stays | unchanged: x kept | none arrives, none sent on (refund of the yocto: not modelled) | `N4_unwrap_fails`, `N4_callback_fails`, `N4_no_refund`, `W1_kept`; example |
| the `do_*` callback, after a successful unwrap | − x stays | − x, burned | x + 1 arrived, nothing sent on: it stays on the contract's account | `N2_burn`, `N3_forward`, `N4_callback_fails`; example |
| the receipt the callback sent (transfer to a missing account, a failing `storage_deposit` / `on_auth`) | − x stays | − x, burned | x was sent; its return to the contract is not modelled | `N3_forward` (the job is gone), `N4_no_refund`, `W3_credit_only_on_arrival` |
| none, but the target `storage_deposit` returns the deposit (account already registered; target = wNEAR) | − x stays | − x, burned | wNEAR sends the deposit back to the contract (`paid`) | example |

A withdrawal of `a` wNEAR with a storage deposit `d` (`ftw`):

| Receipt that fails | Ledger | wNEAR held | NEAR | Theorem / example |
|---|---|---|---|---|
| none | owner − (a + d) | − d burned, − a sent to the receiver | d + 1 in, d sent with the token receipt | `W2_debit`, `N2_burn`, `W2_settles`; example `withdrawSd` |
| `near_withdraw` | plain `ft_transfer`: `a` refunded, `d` stays; with `msg`: `a + d` stay (the exception of `W2_settles`) | unchanged: `d` kept; with `msg` also `a` unassigned | none | `N4_unwrap_fails`, `N4_withdrawal_refund`, `W2_settles`; example (plain) |
| `do_ft_withdraw`, after a successful unwrap | as the row above | − d burned; with `msg` also `a` unassigned | d + 1 arrived, nothing sent on | `N3_forward`, `N4_withdrawal_refund`; example (plain) |
| the token receipt (`storage_deposit` + transfer) | as above | − d burned; with `msg` also `a` unassigned | d sent with the receipt; its return is not modelled | `W2_settles`; example (plain) |
| wNEAR's settlement of `ft_transfer_call` | no refund; `a` left to the receiver | − a − d | — | `W2_settles` (`left = amount`); example |
| `ft_resolve_withdraw` | `a` stays debited, also if nothing left | as before it; what did not leave is unassigned | — | `W2_no_callback`; example |

A deposit of wNEAR:

| Receipt that fails | Ledger | wNEAR held | Theorem / example |
|---|---|---|---|
| the contract's `ft_on_transfer` | no credit | wNEAR's settlement returns the amount to the sender | `W3_credit_only_on_arrival`; example |
| the same, and wNEAR's settlement callback | no credit | the amount stays, unassigned | `W1_ledger_covered`; example |

## 13. Not proved for wNEAR

* The exact books (`T1_exact`, `T1_equality` of section 5) for wNEAR: not proved. Only the
  inequality, with the kept wNEAR of failed unwraps named (`W1_kept`).
* Anything about the contract's NEAR balance as a whole (storage stake, attached deposits, the
  yocto attached to `ft_transfer` by an intent withdrawal), and anything about NEAR after it is
  sent: that it reaches the receiver, that a refund returns (W5).
* That `near_withdraw` and the callbacks get enough gas (W11); that a third party cannot make
  them fail by gas.
* Both ledgers at once: the world of section 3 and this one are separate (W10).
* The reply formats of W3 from the near-sdk 3.1.0 sources, and W4 from the protocol
  specification: hypotheses, supported by the traces of section 14 only.
* That mainnet wNEAR satisfies `WNear.Inv` (W1) and that the ledger of `nep141:wrap.near` on
  mainnet was reached from an empty ledger by this code version (hypothesis 5: upgrades).
* The wNEAR receipts of the harness traces are not replayed through `WNear.exec` here (the
  wNEAR proof did that on its own traces); the replay of section 14 covers the contract's
  receipts.
* Liveness.

## 14. Comparison with the deployed wasm, wNEAR

`intentsmodel` now computes the debits of the wNEAR ledger with the functions of this world:
`IntentsW.startWithdrawW` for an `FtWithdraw` intent of wNEAR, `IntentsW.startUnwrap` for
`native_withdraw`, `storage_deposit` and the `storage_deposit` of withdrawals of other ids; and
it counts the receipts that involve wNEAR (`involvesWNear` in `Main.lean`: the receipt reads or
writes `nep141:<wNEAR>` or is a callback of an unwrap; decided from the receipt's inputs).

Run of 2026-11-13, freshly generated: `intents-gen traces intents.wasm ft.wasm w_near.wasm
20261112 0 200`, kept as `../runs/w200.jsonl.gz`.

| run | receipts on the contract | agree | disagree | env | auth | skipped | involve wNEAR | of them agree / disagree | callbacks after `near_withdraw` |
|---|---|---|---|---|---|---|---|---|---|
| `w200.jsonl` | 11 000 | 10 781 | 0 | 154 | 65 | 0 | 2 729 | 2 663 / 0 (66 env or auth) | 139 |
| `t40.jsonl` (the run of section 7, again) | 3 090 | 3 029 | 0 | 44 | 17 | 0 | 775 | 758 / 0 | 29 |

`../scripts/wnear_glue.py` checks on the same traces what hypotheses W3 and W4 say (a test on
recorded receipts, not a proof). On `w200.jsonl`, 0 checks failed:

| What | Count |
|---|---|
| `near_withdraw` receipts sent by the contract, each with 1 yocto | 139 |
| … succeeded: wNEAR balance of the contract and supply − amount, one transfer of amount + 1 to the contract | 134 |
| … failed: all by a gas fault the harness forced; nothing moved | 5 |
| callbacks that read a success: the value is empty and comes from the transfer to the contract; the callback sends exactly the amount; ledger untouched | 134 |
| callbacks that read a failure: it comes from `near_withdraw`; the callback fails, sends nothing, ledger untouched | 5 |
| wNEAR settlements of a transfer to the contract that read `"0"` (from a successful `ft_on_transfer`) and move nothing | 798 |
| … that read a failure (from a failed `ft_on_transfer`) | 71 |
| `ft_resolve_withdraw` of wNEAR, plain: reads the empty value | 191 |
| … with `msg`: reads the `U128` string wNEAR's `ft_resolve_transfer` returned | 128 |
| … reads a failure | 110 |
| per trace: NEAR sent on ≤ wNEAR burned ≤ NEAR received | 200 of 200 |

Is the replay sensitive to the two new ledger functions? `../scripts/replay_mutants.sh` changes
one line of `IntentsW/World.lean` at a time and replays `w200.jsonl`:

| Change | Disagreements |
|---|---|
| none | 0 |
| `startUnwrap` debits one unit more | 101 |
| `startWithdrawW` does not debit the storage deposit of a withdrawal of wNEAR | 47 |
| `startUnwrap` ignores the pause of `intents` | 0 — not noticed |
| `startUnwrap` ignores the account lock | 0 — not noticed |

The last two are not noticed because the replay's own dispatch rejects such a receipt before it
reaches the function (`mExecuteIntents` checks the pause for every `execute_intents`,
`applyPayloads` the signer's lock). So the replay tests the arithmetic of the two functions; their
two guards are in the model from reading the source (W6) and are tested only at that outer level.

(State of that run. Since section 15 the replay leaves both guards to the two functions, and both
changes are noticed.)

Checking: `./check.sh` (build, axioms of every theorem of both worlds, forbidden tokens, replay of
the runs present) and `./kernel-check.sh` (leanchecker and nanoda
on `Intents` and `IntentsW`; run of 2026-11-13: both `leanchecker --fresh` passes are silent,
nanoda checked 61 999 declarations with no errors; the run on the present sources checked 62 496,
`../evidence/kernel_check.txt`).

## 15. Guards in the replay, and a replay of the world (2026-11-13, after an independent review)

An independent reviewer applied 23 one-line changes to `Intents/Ledger.lean`; the replay noticed
10. Of the 13 it missed, eight were never exercised by the traces, four were exercised but decided
by a copy of the guard in `Main.lean`, and one cannot be exercised by any call
(`../MUTANTS-REVIEW.md`). The reviewer also pointed out that the replay never ran `Intents.step`.
What was changed for it: the trace generator, and `Main.lean`. No definition and no theorem of
`Intents/` or `IntentsW/` changed; `Axioms.lean` prints the same 80 statements (136 since section 16).

* **Permissions come from the model.** `stepAllowed` asks `adminStep` whether a caller may pause,
  unpause, lock, unlock or switch the auth flag: `adminStep` returns the state unchanged for a
  caller it refuses, so the step is run on a state where its effect shows (for an unpause, an
  unlock or an enabling the entry is put in first) and the answer is whether the state changed.
  `mPause` and `mLock` had their own lists of roles before. Forced operations were already
  decided by `Via.ok` / `MoveAuth.ok`.
* **Per-call guards of the contract that the model has per function.** `execute_intents` is paused
  as a whole and needs the signer unlocked for every payload. The model has the pause in
  `Via.ok .intent` and `IntentsW.startUnwrap`, and the lock in `debit`, `moveBal .owner` and
  `adminStep`. `Main.lean` now tests the pause only for a call none of whose intents is guarded in
  the model (`pausedHere`), and the lock only for a payload without intents. A call that succeeds
  in the model has run each of its intents, hence each of these guards, so the unchanged model
  still rejects exactly the calls the contract rejects.
* **Entry points added to the replay:** the four `mt_force_*` transfers (`moveBal (.force caller)`;
  `MoveAuth.force` was in the model and in `T4_who_can_lower`, but no replayed receipt used it),
  `nft_force_withdraw`, the auth-by-predecessor switch in its three forms (`Admin.authOffSelf`,
  `.authForce`, `.authIntent`), and the near-plugins `acl_*` methods. The model leaves open who
  changes the role table (`Admin.acl`), so the near-plugins rules are decode-layer code (`mAcl`),
  compared with the wasm and covered by no theorem. So is `mOutside`: the eleven guarded methods
  that do not touch the ledger, with what decides their success for a holder of the role.
* **Signed payloads.** `admitPayload` decides the verifying contract, the deadline (against the
  block time the trace now records), the registered key and the reuse of a nonce. Only a
  signature that does not verify is left as not compared.
* **A receipt that failed for gas** is still not predicted, but that it changed nothing is now
  compared instead of assumed.
* **The world.** `intentsmodel --world` replays the receipts of the token and of the contract
  together through `Intents.stdStep` on one `Intents.World` (`OBSERVABLE.md`, last section). The
  token is `ProvedFT.exec`; `ft_resolve_withdraw` reads the result the token model produced, and
  the replay checks that the receipt read the same bytes. The in-flight lists of the world
  (`pend`, `unwrap`, `outbox`, `resolves`) are followed by receipt id. This is the first time the
  step relation of sections 1–8 is executed against the wasm; before, the theorems were about
  `step` and the comparison was about the ledger functions `step` calls.

Run of 2026-11-13, `../check.sh` (`../evidence/conformance_1000.json`): 1 000 traces of the
standard token and 200 of each mock, generated by the extended harness.

| receipt replay | receipts on the contract | agree | disagree | not compared: forced failure | out of the attached gas | signature | a runtime error of an action | skipped |
|---|---|---|---|---|---|---|---|---|
| standard token | 64 325 | 63 774 | 0 | 275 | 245 | 31 | 0 | 0 |
| fee-keeping mock | 12 847 | 12 743 | 0 | 50 | 45 | 9 | 0 | 0 |
| reply mock | 12 858 | 12 754 | 0 | 50 | 45 | 9 | 0 | 0 |

| world-level replay | receipts on the token | receipts on the contract in this world | agree | disagree | failed for gas, nothing changed | receipts on the contract about other ledger ids |
|---|---|---|---|---|---|---|
| standard token, 1 000 traces | 20 934 | 31 136 | 51 649 | 0 | 421 | 33 189 |
| standard token, 4 000 traces (`../evidence/conformance.json`, the run on the present sources) | 84 636 | 126 755 | 209 557 | 0 | 1 834 | 133 566 |

Sensitivity at that point (`../scripts/model_mutants.py`, 240 traces; today 121 changes, 114 noticed, 7 that no
receipt can show: `../evidence/model_mutants.json`, section 16.7): 72
one-line changes — the kit's 11, the independent reviewer's 23 and 38 more, among them the four
of section 14 and eight of `Intents/World.lean`. 67 are noticed, 8 of them by the world-level
replay only (the changes of `World.lean`). 5 cannot be noticed by a replay because no receipt
reaches the guard with inputs on which it matters: `ft_withdraw` debiting another owner (the
method has no owner argument), a storage deposit on the two withdrawal methods, an amount or a
destination balance above the `u128` range. With each of the five the theorems stop compiling;
for `ft_withdraw` debiting another owner it is `T4_who_can_lower`. The two changes of section 14
that were missed are noticed now. The score per guard: `../MUTANTS-REVIEW.md`, section 5.

What the replays cannot see by construction: gas; signatures; any rule that lives in `Main.lean`
rather than in the model (`outsideGuards` and `mOutside`, `mAcl`, `admitPayload`) — those are
compared with the wasm on every receipt, but a wrong line there that agrees with the wasm on the
traces would not be caught by changing the model. And the wNEAR world: `IntentsW.step` is still
not executed against the wasm. A world-level replay for it needs the same construction with the
`WNear` model as the token, the unwrap jobs and `do_*` callbacks followed by receipt id, and the
NEAR balance of wNEAR, which the traces do not record.

## 16. The strict world: refunds bound to their transfer, authorisation, the role table (2026-11-13)

`T4_who_can_lower` (section 5) had three limits, stated next to it: the refund step of the world
could take any amount from any account, "the account's own" operation was a label, and the role
table could be anything. This section removes the three, in a second layer on top of the world of
section 3.

### 16.1 What was added, and what was not touched

| File | Contents |
|---|---|
| `Intents/Auth.lean` | functions: the refund of a transfer call (`Xc`, `Xc.refund`, `resolveTransfer`), the entry guard of `mt_transfer*` (`directOk`), keys, nonces and signed payloads (`AuthSt`, `hasKey`, `addKey`, `removeKey`, `Op`, `Payload`, `admit`, `commitNonce`), the role table (`Acl`, `Acl.isAdmin`, `AclCall`, `aclStep`) |
| `Intents/Strict.lean` | the strict world: `SWorld`, `SCfg`, `Step.free`, `SStep`, `runOp`, `runOps`, `sstep`, `SInit`, `SReach` |
| `Intents/StrictTheorems.lean`, `Intents/StrictKeys.lean` | the statements of 16.5 |
| `Intents/StrictExamples.lean` | a concrete run for every statement |

`Intents/Ledger.lean`, `World.lean`, `Backing.lean`, `Theorems.lean`, `Exact.lean`, `Examples.lean`
and all of `IntentsW/` are byte-identical to what they were. No existing statement changed.

Why a layer and not a change of `step`. The world of section 3 lets the refund, the owner's
operations and the role table be anything; T1–T3 are proved there, for more behaviours than the
contract has, and that is the stronger form of T1–T3. The strict world only removes behaviours:
`strict_refines` proves that every strict step is zero or more steps of `step` on the part the two
worlds share (the token, the ledger, everything in flight between them), and `strict_reach` that
every state reachable in the strict world is reachable in the world of section 3. So every
statement of section 5 holds in the strict world as it stands (`strict_T1_backing`,
`strict_T1_ledger_covered` spell out two), and nothing had to be proved again in another form.
`T4_who_can_lower` itself is still there and still true; the new `T4_authorised` is proved from
it for the steps the two worlds share.

### 16.2 State added

| Contract / protocol state | Where | In the model |
|---|---|---|
| an `mt_resolve_transfer` callback in flight | scheduled by `notify_and_resolve_transfer`, `src/contract/tokens/nep245/core.rs:247-270` | `SWorld.calls : List Xc` (previous owner, receiver, amount of one row of this token id) |
| `Account.public_keys` | `src/contract/accounts/account/mod.rs:64-90` | `AuthSt.keys` |
| the flag "implicit public key removed" | same lines | `AuthSt.noImplicit` |
| committed nonces | `src/contract/intents/state.rs:124-130` | `AuthSt.nonces` |
| near-plugins super-admins, admins of a role | near-plugins-derive 0.5.3 `access_controllable.rs:150-420` | `SWorld.supers`, `SWorld.admins`; the grantees stay in `Ctl.roles` |

At the start (`SInit`) the keys, the nonces and the whole role table are whatever they are; no
transfer call is in flight.

### 16.3 Steps

| Step | The receipt it stands for | Guard, from the source |
|---|---|---|
| `base st` | a step of section 3 that `Step.free` lets through: the token's receipts, deposits, the withdrawal callbacks, `ft_withdraw` by the owner (`Via.method`: the caller is the owner and its authentication by predecessor is enabled), `ft_force_withdraw`, pauses, locks, the forced and the self-made switch of the authentication flag | unchanged. Not free: `ftWithdraw .intent`, every `move`, `admin (.authIntent ..)`, `admin (.acl ..)` — in the strict world these happen only inside the steps below |
| `transfer src dst amt call` | `mt_transfer`, `mt_batch_transfer` (`call = false`), `mt_transfer_call`, `mt_batch_transfer_call` (`call = true`) called by `src`, one row | `directOk`: the pause key `mt_transfer` (`core.rs:34,58,79`) and `ensure_auth_predecessor_id` (`core.rs:48,94`, `accounts/mod.rs:79-85`); then `moveBal .owner`. With `call` an entry is added to `calls` |
| `forceTransfer who src dst amt call` | `mt_force_transfer*` (`nep245/force.rs:16-110`) | `moveBal (.force who)`; with `call` an entry is added |
| `resolveTransfer k req` | `mt_resolve_transfer` (`nep245/resolver.rs:16-122`, `#[private]`) for the `k`-th entry; `req` is what the receiver's answer asks back (the whole amount when the answer is unusable, `resolver.rs:32-36`) | refund = `min(req, amount)` (`:51`), then `min` with the receiver's balance (`:72-74`); zero: nothing (`:75-78`); otherwise it moves from the receiver to the previous owner, locks not tested (`:55-67`, `:81-92`). The entry is removed whether the receipt succeeds or panics |
| `resolveTransferFails k` | that callback fails before it runs (gas) | the entry is removed |
| `payload now p sig` | `execute_signed_intent` (`core/src/engine/mod.rs:42-83`) for one signed payload at block time `now` | `valid p.key p sig` (the signature verifies and `p.key` is the key `verify` returns, `:44`); `admit`: verifying contract (`:59-61`), deadline (`:66-68`), `has_public_key` (`:71-73`, `intents/state.rs:42-50`), nonce not used and signer not locked (`:76-77`, `commit_nonce`, `intents/state.rs:124-130`). Then the nonce is committed and the intents run in order (`runOps`); if one fails, the step changes nothing |
| `addKey a k`, `removeKey a k` | `add_public_key`, `remove_public_key` called by `a` (`accounts/mod.rs:40-54`) | authentication by predecessor enabled for `a`; `addKey` / `removeKey`: not locked, the key absent / present (`intents/state.rs:102-121`, `accounts/account/mod.rs:64-84`) |
| `acl c` | the nine `acl_*` methods that change the table (`access_controllable.rs:598-660`) | `aclStep`: grant, revoke of a role and add, revoke of an admin need a super-admin or an admin of the role (`:270-400`); add, revoke, transfer of a super-admin need a super-admin (`:169-250`); renouncing is the caller's own entry |

The intents of a payload (`Op`), as far as they concern this token and the signer's keys:
`withdraw w` (`FtWithdraw`; the owner must be the signer; guards of `startWithdraw .intent`),
`move dst amt call` (`Transfer`, `core/src/intents/tokens.rs:84-133`, with `call` when it has a
notification, after which `mt_resolve_transfer` follows, `intents/state.rs:243-262`; or the
signer's negative side of a `TokenDiff`, `core/src/intents/token_diff.rs:59-67`), `addKey k`,
`removeKey k`, `setAuth enable`.

### 16.4 Assumptions added, removed, changed

Removed for the strict world:

* **Hypothesis 6 (caller — signatures and the intent engine are not modelled)** is replaced by
  S1–S5 below. An operation of the owner is now a direct call with the flag tested, or a payload
  with the tests of `admit` and a signature that verifies under a registered key.
* **"Who holds a role is not restricted"** (`Admin.acl`): the table changes by `aclStep` only.
* **Hypothesis 8 (contract — pause checks of internal operations are dropped)**: removed for
  `mt_transfer*` called directly (`directOk` tests the key `mt_transfer`). It stays for the moves
  of a signed payload: the pause key `intents` is tested for a withdrawal intent only.
* **The refund step**: `move .refund` with any source, destination and amount is not a step of the
  strict world.

Added:

* **S1. caller — a valid signature under a key was made by the holder of that key**
  (`Unforgeable`). The only assumption about the signature scheme. It is a hypothesis of
  `T4_signed_by_holder` and of nothing else: `T4_authorised` says "the signature verifies under
  a key registered for the signer" and needs no assumption.
* **S2. contract — `MultiPayload::verify`, the hash and the decoding of a payload are one
  function `valid`.** The model does not compute a signature of any of the supported standards,
  and it does not derive the fields of `Payload` from signed bytes: that the signer, the verifying
  contract, the deadline, the nonce and the intents a step carries are the ones the signature
  covers is part of what `valid k p sig` means.
* **S3. contract — the intents of a payload are `Op`s on one token id.** A `Transfer` is a move to
  the receiver it names. For a `TokenDiff` the signer's balance of the token changes by the delta
  the payload names; the model writes it as a move to some `dst`, which the signer did not
  choose, so for a `TokenDiff` the statement is about the amount (`Payload.takes`), not about the
  destination. That the deltas of all payloads of one call cancel is not modelled (hypothesis 7
  stays).
* **S4. contract — one `execute_intents` with several payloads is several steps** (as W9): the
  payloads of one call fail together on chain and one by one in the model, which only adds
  reachable states.
* **S5. contract — salted nonces are not modelled.** `verify_intent_nonce`
  (`core/src/engine/mod.rs:86-111`) also rejects a versioned nonce with an invalid salt or an
  expired nonce deadline. The model has only "not used yet", so it admits payloads the contract
  refuses: more behaviours, same statements.
* **S6. NEAR — the block time is an input of the step** (`now`); it is not required to grow.
* **S7. NEAR — a direct call by `a` is a receipt whose predecessor is `a`.** That the account
  holder sent it is NEAR's access-key rule, outside the model, as before.
* **S8. contract — the initial tables are arbitrary.** Keys, nonces, super-admins, admins and
  grantees at the start are not restricted; the statements about roles are relative to them.
* **S9. token — implicit accounts.** `implicit` (`PublicKey::to_implicit_account_id`) is an
  arbitrary function of the configuration; nothing is assumed about it.

Unchanged: hypotheses 1–5, 7, 9–11. In particular 5: `admin_call`, a full-access key and an
upgrade are outside every statement, and so is `acl_init_super_admin`, which is `#[private]`
(`access_controllable.rs:599-600`): only a receipt from the contract's own account can call it.

### 16.5 Statements (`Intents/StrictTheorems.lean`)

* **Refinement.** `strict_refines`, `strict_reach`, `sreach_run`; `strict_T1_backing`,
  `strict_T1_ledger_covered`.
* **`T4_authorised`.** If one step of the strict world lowers `u`'s balance, it is one of six:
  1. `ft_withdraw` called by `u`: not paused, authentication by predecessor enabled, not locked;
  2. one signed payload with signer `u`: the signature verifies under `p.key`, the key is
     registered for `u`, the verifying contract is this contract, the deadline has not passed,
     the nonce is unused, `u` is not locked; the balance falls by at most `p.takes`, the sum of
     the amounts its withdrawals and transfers name; the nonce is used after the step;
  3. `ft_force_withdraw` by a holder of `DAO` or `UnrestrictedWithdrawer`;
  4. `mt_transfer*` called by `u`: `mt_transfer` not paused, authentication by predecessor
     enabled, not locked;
  5. `mt_resolve_transfer` for an entry in flight whose receiver is `u`: the balance falls by at
     most the amount of that transfer, and the entry is gone after the step;
  6. `mt_force_transfer*` by a holder of `DAO` or `UnrestrictedWithdrawer`.
* **`T4_calls`.** The entries in flight change in three ways only: one is removed by its
  `mt_resolve_transfer` (run or failed); one entry `⟨src, dst, amt⟩` is added by a transfer call
  that moved exactly `amt` from `src` to `dst` in the same step; a signed payload adds one entry
  per transfer with a notification among its intents, each with the signer as the previous
  owner. With way 5 this is "a refund is taken only from the receiver of a transfer that was
  made, by at most its amount, and once".
* **`T4_nonce_kept`.** A used nonce stays used, so with way 2 a payload is executed at most once.
* **`T4_key_power`** (`Intents/StrictKeys.lean`). If `k` is not a key of `u` before a step and is
  one after it, the step is `add_public_key(k')` called by `u` itself with authentication by
  predecessor enabled, or one signed payload with signer `u`, whose signature verifies under a
  key already registered for `u`, with `AddPublicKey(k')` among its intents; `k'` is `k` or a key
  with the same implicit account (adding back the implicit key of an account restores every key
  that maps to it; nothing is assumed about `implicit`). No step makes a key of `u` for anyone
  else. Removing a key makes no key (`removeKey_has`).
* **`T4_signed_by_holder`.** Under S1: if a payload lowers `u`'s balance, the holder of a key
  registered for `u` signed that payload.
* **The role table.** `T4_role_power`, `T4_admin_power`, `T4_super_power` (statements about
  `aclStep`): a holder of a role is made only by `acl_grant_role` of a super-admin or an admin
  of that role; an admin only by `acl_add_admin` of the same; a super-admin only by
  `acl_add_super_admin` or `acl_transfer_super_admin` of a super-admin. `T4_role_change`: in the
  strict world no other step makes a holder. `T4_roles_from_initial`: along any run, if the
  start has no super-admin and no admin of `r`, there is none later and every holder of `r`
  held it at the start; `T4_force_from_initial`: then whoever can force a withdrawal or a
  transfer held `DAO` or `UnrestrictedWithdrawer` at the start.
  **The power this leaves, named:** `T4_super_admin_can_take_any_role` — a super-admin (or an
  admin of the role) makes itself or anyone a holder of the role with one call, so with a
  super-admin present ways 3 and 6 are open to it at any time.
* **`T4_auth_flag_power`** (a statement about `adminStep`): the authentication flag of an account
  changes only by its own `disable_auth_by_predecessor_id` (flag on, not locked), its
  `SetAuthByPredecessorId` intent (not locked), or the forced switch of a role holder.
* **Two guards that the invariant implies.** `startWithdraw_amount_guard_redundant`: in every
  reachable state `startWithdraw` equals the same function without the guard
  `w.amount ≤ U128_MAX`. `moveBal_destination_guard_redundant`: in every reachable state the
  guard `bal dst + amt ≤ U128_MAX` of `moveBal` follows from its other guards. See
  `../MUTANTS-REVIEW.md`, section 3.

No statement was weakened and no hypothesis was added to an existing statement.

### 16.6 Not proved, not done

* **Keys along a run.** `T4_key_power` is about one step. No statement follows the keys of an
  account from the start of a run (the initial keys are arbitrary, S8).
* **No theorem counts refunds along a run.** "Once per transfer" is the pair way 5 (the entry is
  removed) and `T4_calls` (an entry is added only by a transfer call).
* **In the strict world the authentication flag is switched by an intent only inside a signed
  payload** (`Step.free`), but `T4_auth_flag_power` is stated for `adminStep`, not for `sstep`.
* **The wNEAR world (`IntentsW/`) is as it was**: its refund step is free, its owner operations
  are labels, its role table is unrestricted (`W4_who_can_lower`).
* **S2**: nothing about the signature standards or about the binding of a signature to the
  payload fields. **S5**: salts. **Hypothesis 5**: the three powers of `DAO`.
* The pause key `intents` for the moves of a payload.
* Liveness: that an `mt_resolve_transfer` runs (gas), that a refund which is due arrives.

### 16.7 Comparison with the deployed wasm

`Main.lean` takes every guard of this section from the functions above and has no copy of its
own (`OBSERVABLE.md`): `mt_resolve_transfer` is `resolveTransfer`; `mt_transfer*` asks
`directOk`; a signed payload is admitted by `admit` and its nonce committed by `commitNonce`;
`add_public_key` / `remove_public_key` are `addKey` / `removeKey`; the `acl_*` methods are
`aclStep`. The world-level replay runs the internal transfers of the token's ledger id and the
`acl_*` calls through `sstep`, follows every entry of `calls` by the receipt id of its
`mt_resolve_transfer`, and compares the role table the model computed with the trace after every
receipt. The generator has two more probes for this (`../FORMAT.md`): `keys` (keys added and
removed, payloads signed with each, with the flag off, locked) and `edges` (a refund asked above
the amount, an `mt_resolve_transfer` out of gas, admin entries revoked and renounced, the
super-admin role handed over).

Not run by any replay: the `payload` step as a whole (a signed call is replayed intent by intent:
`runOp … (.move ..)` for a transfer, the steps of section 3 for a withdrawal), a `Transfer`
intent with a notification (no trace has one), `Step.free`, `directOk` at its use inside the
strict `transfer` step (the world-level replay does not decide whether a transfer succeeds; the
receipt replay does, with the same function), the implicit-key half of `hasKey` (the traces
register keys for named accounts), and the signature itself. Numbers of the run and the one-line
changes of every new guard: `../MUTANTS-REVIEW.md`, section 5.
