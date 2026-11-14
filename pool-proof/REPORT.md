# Exit Proof: formal core for the staking pool (`poolv1.near`)

## Summary

The question: if I put money into the pool, can I take it back, and who can stop me?

- **Proved in Lean 4.35, no `sorry`.** This is a theorem about a model, tied to the deployed
  bytes by hash equality and execution. In the model: from any pool state reachable from
  `new()` with no outflow from the pool account, a delegator `u` who has stake calls
  `unstake_all`; the call succeeds and leaves `u` an unstaked balance of at least
  `get_account_total_balance(u)`. Then, if `u` calls nothing in between, in any state at
  least 4 epochs later in which the protocol has returned the stake (assumption PUA),
  `withdraw_all` succeeds and transfers `u` at least that amount. Nothing is lost to
  rounding. Other accounts and the protocol may do anything in the meantime. The theorem is
  `exit_guarantee`; it holds while the pool has received fewer than `10^12` calls
  (`ncalls < 10^12`). That a PUA state arrives is an assumption about the protocol, not a
  theorem.
  Proved separately (`deposit_claim`): a successful deposit of `d` raises that balance by at
  least `d`. So what was put in can be taken out.
- **No one else can reduce `u`'s share.** Neither the owner nor other accounts change
  `u`'s unstaked balance, unlock epoch or number of shares. The share price never falls.
  The owner can change only the fee on future rewards, the pause, the staking key and the
  vote (`others_call`, `others_preserve`, `owner_methods`, `exec_price`).
- **The model agrees with the deployed wasm.** The deployed wasm (hash `J1arLz48…GYTY`,
  checked on the bytes) was run on `near-contract-sim` (nearcore 2.14.0 runtime) on 1149
  random traces: 55 955 calls, 65 538 steps. All 1149 traces agree with the model with no
  divergence (EXACT), and the texts of all 20 998 errors agree too.
- **Axioms:** only the standard `propext`, `Classical.choice`, `Quot.sound`;
  `liquid_covers` does without `Classical.choice`.
- **Assumptions about the environment** (section 4). The main one is PUA: the protocol
  returns a reduced stake within 3 epochs, and the pool's stake receipt executes no later
  than the next epoch. On the simulator PUA was checked before each of 54 342 calls, with
  0 violations. Storage staking is not modelled; if the storage cost exceeded the pool's
  remaining balance the last withdrawal would wait for a top-up.
- **No counterexample to T_exit in the model.** Conformance found one inaccuracy of the
  model: near-sdk 1.0.0 rejects a deposit attached to a non-`#[payable]` method. It was
  fixed. The caveats for the real world are listed in section 6.

Independent re-run on 2026-11-12: `check.sh` — Lean build, 14 theorems with the standard
axioms, 1149/1149 EXACT, 0 error-text mismatches (69 s). Validator census
(`../docs/CENSUS.md`): 196 pools run this code, with 500.9 million NEAR = 86.2% of the
network's total stake.

## 1. Object

| | |
|---|---|
| Contract | `near/core-contracts`, `staking-pool` v0.4.0, commit `1cacc9d` (2020-07-29), `src/lib.rs` + `src/internal.rs` |
| Deployed code | hash `J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY` = `staking-pool/res/staking_pool.wasm` @ 1cacc9d, 262 183 bytes (copy in `wasm/staking_pool.wasm`) |
| Where it was checked | `near-contract-sim` on nearcore 2.14.0 (protocol 88): one shard, one validator, flat rewards per epoch |

## 2. Model (`lean/StakingPool/*.lean`)

| File | Contents |
|---|---|
| `Model.lean` | the executable model: state, the rounding helpers, all internal and public methods, `new`, the view methods |
| `Basic.lean`, `Spec.lean` | lemmas about the error monad and checked arithmetic, sums over the account map, a characterisation of the successful outcome of every internal method |
| `Facts.lean`, `Methods.lean` | the relation `RelC` (what every internal step preserves) and `exec_facts` (the outcome of one successful call, all 16 methods) |
| `World.lean` | the pool together with its environment (`World`), the steps `Step`, reachability `Reach`, the assumption `PUA`, the global invariant `WInv` |
| `Exit.lean`, `Safety.lean`, `Deposit.lean` | the theorems |
| `Main.lean` | `poolmodel`: the executable model on JSON traces. It uses the same definitions of `World`, `exec` and `PUA` |

**Semantics of a call.** A method is a function `Contract → Env → Except String (Contract × Eff)`.

- `error` means a panic. The runtime rolls the call back: the state does not change and the
  deposit is returned.
- Integers are `Nat` with explicit u128 and u64 checks: the crate is built with
  `overflow-checks = true`, so an overflow is a panic. The intermediate U256 values do not
  overflow; only `as_u128` is checked.
- The roundings `rounded_down` and `rounded_up` repeat the source character for character.
- The asserts carry the same messages as the source.
- A transfer larger than the liquid balance fails inside the call
  (`HostError::BalanceExceeded`).
- A stake action with a key that the protocol does not accept for staking fails the call
  (`UnsuitableStakingKey`).
- Methods without `#[payable]` fail when the deposit is > 0 (`Method doesn't accept deposit`).

**What a call reads from the environment** (`Env`): `epoch_height`, `account_balance`
(already including the attached deposit), `account_locked_balance`, `attached_deposit`,
`predecessor`.

**The environment (`World`, `Step`).** A world is the contract plus `epoch`, `liquid` and
`locked` of the pool account. Two more ghost variables are not read by the contract: `hist`
(the window of stake requests over the last 4 epochs, with the rewards credited after the
request) and `ncalls` (the number of calls). The steps:

- `call` — any predecessor, any method, any arguments and deposit (successful calls only;
  an unsuccessful call changes nothing).
- `advance` — an epoch boundary.
- `income` — rewards and any incoming transfers, to liquid and/or locked.
- `rebalance` — the protocol moves anything between liquid and locked, keeping the sum
  (stake actions, unlocking, kick-out).

Funds can leave only through the contract's `withdraw`. This is assumption E1.

`Reach` is the set of all worlds reachable from `new` on an account with a balance of
`> 10^12` yocto and zero locked (the factory requires 30 NEAR) by any sequence of steps.

## 3. Theorems

All names are in the namespace `StakingPool`. The list of axioms is in `out/axioms.txt`.

### T_exit — the exit guarantee

**`exit_guarantee`.** Let `w0` be reachable and `u` any account (the owner included). Let
the pool balance be ≤ u128::MAX, the epoch `< 2^64 − 4`, and the number of calls made to
the pool so far less than `10^12` (`ncalls < 10^12`). Then there is a `w1` such that:

- either `w1 = w0` (there is no stake),
- or `unstake_all` by `u` in `w0` **succeeds** and `w1` is its result.

In both cases the unstaked balance of `u` in `w1` is ≥ `claim(w0,u)`, where
`claim = unstaked + ⌊staked_balance · shares / total_shares⌋`. This is exactly
`get_account_total_balance`.

Next, let `w2` be any continuation of `w1` by steps in which `u` calls nothing (other
accounts, the owner, the protocol), such that:

- `w2.epoch ≥ w0.epoch + 4`;
- PUA holds in `w2`;
- `ncalls ≤ 10^12`;
- the balance is ≤ u128::MAX;
- `claim(w0,u) > 0`.

Then `withdraw_all` by `u` in `w2` **succeeds** and transfers `u` at least `claim(w0,u)`.
The rounding bound is 0: `unstake` rounds up, in the delegator's favour, at the expense of
a fund of 10^12 yocto.

What it is assembled from:

- **`unstake_all_ok`.** In any world with `WInv` and a positive staked balance,
  `unstake_all` succeeds, the unstaked balance becomes ≥ `claim`, and the unlock comes at
  `epoch + 4`.
- **`withdraw_all_ok`.** With `WInv`, PUA and an expired delay, `withdraw_all` succeeds and
  transfers the whole unstaked balance.
- **`liquid_covers` — liquidity.** With `WInv` and PUA the pool's liquid balance covers the
  unstaked balance of any account whose delay has expired.
- **`solvency`.** In any reachable world `liquid + locked ≥`
  `total_staked_balance + Σ unstaked` over all accounts.

### Money in

**`deposit_claim`.** A successful `deposit` or `deposit_and_stake` with deposit `d` raises
the caller's `claim` by at least `d`. Together with T_exit this means: what was put in can
be taken out in full, plus the rewards.

### The global invariant

**`Reach.inv`.** Every reachable world satisfies `WInv`:

| Field | Statement |
|---|---|
| `CInv` | the account map is well-formed; there are shares that belong to no one ("orphan" shares): `Σ shares < total_shares`; the share price is ≥ 1: `total_shares ≤ total_staked`; the fee is valid |
| `key` | if the pool is not paused, its staking key is valid |
| `fund` | `total_staked + Σ unstaked + 10^12 ≤ last_total_balance + ncalls`: every call spends at most 1 yocto of the fund |
| `cons` | `last_total_balance ≤ liquid + locked` |
| `avail` | `unstaked_available_epoch_height ≤ epoch + 4` |
| `win` | for every epoch `j` of the last four: `hist j ≤ total_staked + Σ{unstaked v : v still in its delay after j+3}` |

`win` is the key to liquidity: what the protocol still holds locked is covered by the
current stake of the books plus the balances that are still in their delay.

### T_safety — what others and the owner can do

- **`others_call`.** Any successful call by a predecessor `p ≠ u` (the owner included):
  - does not change the unstaked balance of `u` or its unlock epoch;
  - does not reduce the shares of `u`; if `u` is not the owner, does not change them at all;
  - does not reduce the share price;
  - does not reduce `claim(u)`.
- **`others_preserve`.** The same for any chain of steps without calls by `u`, including
  the protocol's steps.
- **`owner_methods`.** A successful owner-only method (`pause_staking`, `resume_staking`,
  `update_reward_fee_fraction`, `update_staking_key`, `vote`):
  - was called by the owner;
  - transfers nothing;
  - does not change `owner_id`;
  - does not reduce the share price;
  - changes no one's unstaked balance or unlock epoch, and changes shares only for the
    owner (the fee shares from ping).
- **Shape of the owner methods.** `updateFee_shape`, `updateStakingKey_shape`,
  `pauseStaking_shape`, `resumeStaking_shape`, `vote_shape`: every such method is an
  `internal_ping` with the previous parameters, followed by setting one field (`fee`, `key`
  or `paused`); `vote` changes nothing. Important: in `update_reward_fee_fraction` the ping
  runs **before** the fee changes. The rewards accumulated up to this call are distributed
  under the old fee; the new one applies only to future rewards.

**What the owner can do:**

- set the fee up to 100% on future rewards, at once, with no timelock;
- pause the pool (stake 0, no rewards);
- change the key;
- vote on behalf of the pool;
- take part as an ordinary delegator.

**What the owner cannot do:** touch anyone else's principal, transfer other people's funds
to itself, or upgrade the code (the code has no deploy, delete-account or add-key; the pool
has no access keys).

### Share price and rounding

- **`exec_price`, `step_price`.** The price `total_staked / total_shares` does not decrease
  on any successful call or on any step. This is the property
  `verify_stake_price_increase_guarantee` from the tests of the source.
- **`exec_rounding`.** Every call spends at most 1 yocto of the price-guarantee fund.

A refinement of the statement "rounding is never in the delegator's favour". Taken
literally it is **false**: `stake` charges the delegator the rounded-down amount and adds
the rounded-up amount to the pool; `unstake` gives out the rounded-up amount and subtracts
the rounded-down amount from the pool. Rounding favours the caller by ≤ 1 yocto per call.
`STAKE_SHARE_PRICE_GUARANTEE_FUND = 10^12` yocto pays for it, not the other delegators: the
price of their shares does not fall. After `10^12` calls the fund could be exhausted. This
is the condition `ncalls ≤ 10^12` in T_exit; unreachable in practice.

### Axioms

`#print axioms` for all the theorems above (output in `out/axioms.txt`):
`[propext, Classical.choice, Quot.sound]`; for `liquid_covers` it is `[propext, Quot.sound]`.
`Classical.choice` comes from `omega` and `simp` on goals with ∧, ∃ and `if`.

## 4. Assumptions (TCB)

**Correctness.**

- The Lean 4.35.0 kernel.
- The model was transcribed from the source at 1cacc9d by hand; its agreement with the
  deployed code is checked by conformance (section 5) but not proved.
- wasm ↔ source: the hash of the deployed code equals the hash of the wasm committed at
  1cacc9d; conformance was run on this wasm. The compilation of the source to wasm is not
  verified.

**Environment.**

| | Assumption |
|---|---|
| E1 | No outflow. The balance of the pool account (`liquid + locked`) decreases only by the transfer in `withdraw`. The pool has no access keys, the code has no deploy, delete-account or add-key, and NEAR has no slashing. If an outflow happens anyway, `internal_ping` fails on the assert "The new total balance should not be less than the old total balance", and **all** calls that ping in a new epoch are blocked. This was confirmed by fault injection (section 5). |
| E2 | **PUA** (`World.PUA`, checked at the moment of `withdraw_all`): `locked ≤ max(hist[k-3..k]) + (liquid + locked − last_total_balance)`, where `hist j` is the largest `total_staked_balance` of the books in epoch `j` plus the rewards distributed afterwards. In words: the protocol holds locked no more than the largest stake the pool requested over the last 4 epochs (with the rewards on it), plus the income not yet distributed. It follows from the NEAR rule "a reduced stake is returned at the start of the third epoch after the one in which the proposal was accounted for", provided the pool's stake receipt executes no later than the next epoch boundary. Hence `NUM_EPOCHS_TO_UNLOCK = 4 > 3`. |
| E3 | Bounds: pool balance ≤ u128::MAX (the whole NEAR supply is ≈ 2^110); epoch `< 2^64 − 4`; fewer than `10^12` calls to the pool over its whole history. |
| E4 | The validity rules of the staking key (`vk`) are fixed. If the protocol starts rejecting the current key, calls that restake, `unstake_all` included, will fail until the owner changes the key or pauses the pool. |
| E5 | The caller attaches enough gas (300 Tgas in the tests). Gas is not modelled: running out of gas is a rolled-back call. |
| E6 | Storage staking is not modelled. The protocol additionally requires `liquid + locked ≥ storage_usage · 10^19` after every receipt. See section 6, item 4. |
| E7 | Atomicity of one call. Arbitrary interleaving of whole calls of different accounts is covered. The receipts the pool creates itself (stake, `on_stake_action`, `stake(0)`) are abstracted by the `rebalance` step. |

## 5. Conformance: the model against the deployed wasm

The harness, `harness/src/main.rs`:

- the deployed wasm is taken by its bytes and the hash is checked;
- `new` is called by `factory.near`;
- 6 actors: `alice`, `bob`, `carol`, `dave`, `owner` (also a delegator) and the outsider `eve`;
- random calls of all 16 methods, including ones that are sure to fail: owner methods by
  someone else, an invalid fee, a secp256k1 key, an invalid `voting_account_id`, a repeated
  `new`, an external `on_stake_action`, a deposit on a non-payable method, boundary amounts
  ±1 around the balances;
- epoch steps;
- rewards in two ways: `epoch_reward` in 680 of the 1000 traces and 552 direct injections
  of locked growth;
- `minimum_stake` in 76 traces (a failed stake action and the `on_stake_action` path).

After **every** step the following are compared:

- the raw contract state (the borsh `STATE` and all `UnorderedMap` entries: `unstaked`,
  `stake_shares`, `unstaked_available_epoch_height`);
- the view methods `get_account` for all actors, `get_total_staked_balance`,
  `get_number_of_accounts`;
- success or failure of the call and the error text.

| Family | Traces | Steps | Calls | EXACT | MISMATCH | Error texts (match / differ) |
|---|---|---|---|---|---|---|
| normal | 1000 | 57 020 | 48 687 | 1000 | 0 | 17 669 / 0 |
| faults | 100 | 5 602 | 4 804 | 100 | 0 | 2 248 / 0 |
| overflow | 49 | 2 916 | 2 464 | 49 | 0 | 1 081 / 0 |
| **total** | **1149** | **65 538** | **55 955** | **1149** | **0** | **20 998 / 0** |

The share price in the traces reaches 3.63. Both successful and failing calls of all 16
methods were exercised; the ok/fail histogram per method is in `out/summary.json`.

**Environment checks** on the simulator's data, outside the fault steps:

- **Balance conservation.** On every call `Δ(amount + locked) = deposit − transfer` if the
  call succeeds, and 0 if it does not. 0 violations.
- **PUA** from Lean (`poolmodel` evaluates `World.PUA` on the simulator's balances before
  every call): 54 342 checks, 0 violations. **`cons`** (`last_total_balance ≤ liquid +
  locked`): 0 violations.
- **Why PUA needs the rewards in the window.** With a window over the observed states only,
  without the added rewards, there are 1610 violations. Rewards credited to locked are
  distributed by the ping inside the same call as the `unstake`, so that value appears in
  no stored state. Hence the definition of `callHist`.
- No call crossed an epoch boundary. No call failed in the simulator while succeeding in
  the model.

**The fault and overflow families** go beyond the environment model and exercise the
failure branches of the model:

- **`hold` / `drain`.** The pool's liquid balance was forced down before a `withdraw`
  (imitating a protocol that has not returned the stake).
  - 66 times `Exceeded the account balance.` in both the simulator and the model.
  - 26 times `drain` lowered the total balance and the ping failed on the assert "new total
    balance should not be less than the old" in both.
- **`overflow`.** Balances around 2^127: 11 or more matching panics
  `attempt to add with overflow`. 1 trace of the 50 aborted inside nearcore itself
  (`UnexpectedIntegerOverflow` in `update_validator_accounts` on an artificial balance near
  u128::MAX). This is an artefact of the injection, not behaviour of the contract; the
  trace is not in the sample.

**A divergence found by conformance.** The first version of the model did not reject a
deposit on non-`#[payable]` methods: 435 traces MISMATCH. near-sdk 1.0.0 generates the
check `Method doesn't accept deposit` before the method body; the string is in the wasm.
After `Method.payable` was added — 0. Here conformance caught an error of the model, not of
the contract.

## 6. Findings

1. **No counterexample to T_exit in the model.** The theorem is proved for all reachable
   states, under any behaviour of other accounts and of the owner (pause, 100% fee, key
   change) and under any behaviour of the protocol compatible with E1 and PUA.
2. **Rounding in the caller's favour** (≤ 1 yocto per call) is paid by the fund of 10^12
   yocto, not by other delegators. Details in section 3.
3. **Powers of the owner.** A fee of up to 100% can be set instantly, but it applies only
   to rewards after the call. The pause switches rewards off but does not prevent the exit:
   under a pause there is no restake, and T_exit does not depend on the pause.
4. **Storage is not accounted for** (E6). Storage staking is not modelled; if the storage
   cost exceeded the pool's remaining balance the last withdrawal would wait for a top-up
   (it would fail with `LackBalanceForState` until someone tops up the pool). This is a
   limit of the statement "can always withdraw", not a loss of funds. This regime was not
   tested in the simulator.
5. **Dependence on PUA.** If the pool's stake receipt is delayed by more than one epoch
   boundary (only under extreme congestion), the protocol may not yet have returned the
   stake by epoch `e+4`. Then `withdraw_all` temporarily fails with
   `Exceeded the account balance.` (this branch of the model was exercised by the fault
   family) and succeeds later. No funds are lost.
6. **Fragility to outflow (E1).** Any decrease of `liquid + locked` outside `withdraw`
   blocks the pinging calls in a new epoch (fault family `drain`). In today's NEAR there is
   no outflow: no keys and no slashing.
7. **Validity of the key (E4).** The invariant "not paused ⇒ the key is valid" holds as
   long as the protocol rules do not change. Only the owner can change the key.

## 7. What is NOT covered

- The compilation of the source to wasm. There is only the hash equality and conformance;
  the manual transcription of the source into Lean is not formally linked.
- The NEAR protocol. It is reflected only by the `Step` abstraction; PUA is an assumption.
  Its check in the simulator uses near-contract-sim's simplified epoch model: one
  validator, flat rewards, no kick-out and no seat price.
- The receipts the pool creates itself: the stake action, `on_stake_action`, `stake(0)` on
  failure, `vote` to another contract. Their effect on the balance is covered only by the
  `rebalance` step.
- Gas, storage staking (E5, E6), multi-shard receipt delays.
- Pagination of `get_accounts`, the `vote` promises themselves.
- The concrete state of the mainnet pools (key, pause, fee, number of delegators,
  `storage_usage`): not queried.

## 8. How to reproduce

Everything needed is in this directory. One command:

    ./check.sh            # [N_NORMAL=1000] [N_FAULTS=100] [N_OVERFLOW=50] [SEED=20261112]

The script:

1. builds the Lean model, the proofs and the non-vacuity example, checks that there is no
   `sorry`, writes the axioms to `out/axioms.txt` and checks that they are among
   `propext`, `Classical.choice`, `Quot.sound`;
2. builds the harness against the public `near/near-contract-sim` at commit `8e4b69b`
   (which pins nearcore 2.14.0); both are git dependencies, locked in `harness/Cargo.lock`;
3. runs the traces on the simulator, checking the hash of `wasm/staking_pool.wasm`;
4. runs `poolmodel`;
5. compares (`out/results.json`) and writes the summary `out/summary.json`.

The exit status is 0 only when the verdict is EXACT: every trace agrees with the model at
every step, every error text agrees and no environment check is violated.

Requirements: Linux x86-64, `elan` (Lean 4.35.0 is installed from `lean/lean-toolchain`),
`rustup` (Rust 1.95.0 from `harness/rust-toolchain.toml`), a C/C++ compiler, `cmake` and
libclang (for nearcore's RocksDB bindings), `python3`, `git`. Without root, libclang can be
taken from the Python package: `python3 -m pip install libclang`, then set `LIBCLANG_PATH`
to its `site-packages/clang/native` directory and add there a link named after the
library's soname (`ln -s libclang.so libclang.so.18.1`). Paths can be changed with the
environment variables `POOL_WASM`, `OUT_DIR`, `CARGO_TARGET_DIR`, `THREADS`, `JOBS`
(see the header of `check.sh`).

**Time.** With the toolchains installed and the harness built, the whole check takes about
70 s on a 32-core machine: the simulator ≈ 55 s on 8 threads (0.25–0.4 s per trace), the
model ≈ 8 s. On a clean machine (32 cores, shared with other jobs; no Rust or Lean toolchain,
empty cargo and elan directories, a fresh copy of this directory; 2026-11-12) `./check.sh`
took 10 min 17 s — 7 min 37 s of it to download and compile the harness with nearcore
(8 jobs), 99 s for the simulator, 16 s for the model — and ended with the same EXACT result
and the same counts.

**The wasm input.** `wasm/staking_pool.wasm` is the upstream artefact
`staking-pool/res/staking_pool.wasm` of `near/core-contracts` at commit `1cacc9d`
(see `NOTICE`). `./fetch-wasm.sh` downloads it again from that commit, checks the hash
(`J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY`) and compares it with the committed copy.

**The non-vacuity example.** `lean/Review/PoolVacuity.lean`, from the independent review
(`../docs/REVIEW.md`), builds a concrete reachable world by real steps and applies
`exit_guarantee` to it. It is compiled by `lake build` (so by `check.sh`) and can be
checked alone with `cd lean && lake env lean Review/PoolVacuity.lean`.

**Re-checking the proofs in the kernel and in an independent kernel.** The checks of the
independent review, run in `lean/` after `lake build` (the three tools ship with the Lean
4.35.0 toolchain); `lean/kernel-check.sh` runs them in this order:

    lake env leanchecker --fresh StakingPool              # replays every declaration in the Lean kernel; silent on success
    lake env leanexport StakingPool > .lake/pool.ndjson   # exports all declarations (about 360 MB)
    touch .lake/pool.pp.txt                               # nanoda prints the two headline statements here; the file must exist
    lake env nanoda_bin nanoda.json                       # nanoda_bin 0.4.19: an independent kernel written in Rust

The expected last line is `Checked 60236 declarations with no errors`; `sorryAx` is named
there only as an exported axiom that is not permitted, i.e. it is not used.

Files:

- `lean/` — the model, the proofs, `Main.lean` (`poolmodel`), `scripts/Axioms.lean`,
  `Review/PoolVacuity.lean`, `nanoda.json`, `kernel-check.sh`;
- `harness/` — the Rust harness on near-contract-sim (`env.sh` is the build environment);
- `wasm/staking_pool.wasm`, `fetch-wasm.sh`, `NOTICE`;
- `scripts/compare.py`, `scripts/summary.py`, `check.sh`;
- `out/summary.json` — the numbers, `out/results.json` — the full comparison report,
  `out/axioms.txt`, `out/gen.log`, `out/traces.jsonl.errors` — the aborted overflow trace.
