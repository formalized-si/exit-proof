# wrap.near: can you always take your NEAR back — a proof (Exit Proof, core 2)

The code `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1` (wNEAR, ~36.7 million NEAR on the account) is the
artefact `w-near/res/w_near.wasm` of near/core-contracts at `54f8267`, near-sdk 3.1.0 +
near-contract-standards 3.1.0 (copy in `wasm/w_near.wasm`).

The theorems below are theorems about a model, tied to the deployed bytes by hash equality and execution.

## Summary

| | Result |
|---|---|
| Theorems | 14 theorems in Lean 4.35, no `sorry`; the only axioms are `propext`, `Quot.sound`, `Classical.choice` |
| Exit | In any state that satisfies the full invariant `Inv`, a registered holder `u ≠ wrap.near` whose balance at the moment of execution is `b` calls `near_withdraw(b)` (with 1 yocto): the call **always** succeeds and the contract sends `u` `b + 1` yocto (`T_exit`); a second call returns the storage deposit as well. No one can prevent it. For states reachable from `new()` of this code `Inv` is proved, and the statement is `exit_always`; for mainnet see the Mainnet row |
| Conservation | `total_supply = Σ balances` in every reachable state, whatever the receivers do and in whatever order receipts arrive |
| Callback | `ft_resolve_transfer` is executed only by the contract itself; the refund is ≤ the amount transferred and ≤ what the receiver holds now |
| Calls by others | The balance of `u` is lowered only by `u` itself (4 methods) or by the refund of a transfer made **to** `u`, by no more than the amount of that transfer |
| Conformance | 2000 random traces on the deployed wasm bytes (nearcore 2.14.0): 55 825 receipts, 58 022 blocks, 329 546 balance comparisons — **EXACT, 0 divergences**; 8 of 8 mutants of the model are caught |
| Mainnet | The solvency part of the invariant holds now with a margin of **3 388 NEAR** (block 224 128 229) and held at the moment of the 2021 upgrade (margin 66.6 NEAR). The other part of `Inv`, `supply = Σ balances`, was not checked on mainnet, so for mainnet the exit statement is conditional on it |
| Findings | None critical. The main one for the wording: wrap.near did **not** start with this code — up to height 35 438 886 it ran different code, `9kQaNisc…`, which was then replaced without a migration; the key was deleted at 40 858 545. 107.55 wNEAR sit on wrap.near itself and can never be withdrawn |

One-line check: `./check.sh` (~20 s once everything is built) or `./check.sh --all` (~1 min: + the mutants,
the old code, mainnet). Independent re-run on 2026-11-12: build, axioms, hash, rejection of a foreign
callback and 2000 traces EXACT — all matched (17 s).

---

## 1. The theorems in plain words

File `lean/WNear/Theorems.lean`. `E : Env` are the deployment parameters, `S : Sys` is the state of the system
(the contract + the callbacks in flight + every NEAR transfer the contract has sent), `sysStep E S st` is one step.

| Property | Lean | What it says |
|---|---|---|
| **T_conservation** | `inv_step`, `T_conservation` | Every step preserves the invariant `Inv`; in every reachable state `total_supply` = the sum of the balances |
| | `T_force_unregister_burns` | `storage_unregister(force=true)` removes the account, **burns** its balance `b` (`total_supply − b`); the NEAR that backed `b` stays in the contract; the user receives only `minBal + 1` yocto |
| **T_resolve** | `T_resolve_private` | A call of `ft_resolve_transfer` with any predecessor other than the contract itself fails — for any arguments, any deposit and **any promise results** (i.e. also as the `promise_then` callback of another contract — the scheme of the SWEAT attack) |
| | `T_resolve_private_sys` | Such a call changes nothing in the system |
| | `T_resolve` | The refund `f` to the sender: `f ≤ amount`, `f ≤` the receiver's current balance (if the receiver has already moved the tokens away or unregistered — less, or 0), `f ≤ unused`; the receiver loses exactly `f`; the other accounts do not change; sender registered → it receives exactly `f` (the sum sender + receiver is preserved), `amount − f` is returned; sender removed → `f` is burned, `amount` is returned |
| | `T_resolve_never_fails` | In a reachable state the callback cannot fail for any promise result (there are no overflows); only gas can stop it — that is a separate step, `resolveFails` |
| **T_exit** | `exit_always` (headline) | From **any** state reachable from `new()` of this code, a registered `u ≠ wrap.near` with balance `b` calls `near_withdraw(b)` with 1 yocto — the call succeeds: the balance becomes 0, the contract sends `u` a transfer of `b + 1` yocto. No one's participation is needed, and no one's earlier actions get in the way |
| | `T_exit` | The same from any state with the full invariant `Inv`, for any amount `x ≤ b`, with the exact new state (balance `b − x`, supply `− x`, the contract's NEAR `− x`) |
| | `exit_full` | Two calls of one's own — `near_withdraw(b)` and `storage_unregister()` — leave `u` unregistered and with transfers of `b + 1` and `minBal + 1`: all the wNEAR and the storage deposit back |
| **T_no_one_else** | `T_no_one_else` | A step that is not a call by `u` does not lower the balance of `u`, except the callback `ft_resolve_transfer` of an `ft_transfer_call` made **to** `u`; it takes back no more than the amount of that transfer |
| | `T_who_can_lower` | The exact list: the balance of `u` is lowered only by `near_withdraw`, `ft_transfer`, `ft_transfer_call`, `storage_unregister(force=true)` called by `u` itself, and by the callback of a transfer to `u` |
| | `calls_origin` | A callback in flight `(sn, rc, amt)` is created only by a successful `ft_transfer_call` from `sn` that credited `rc` exactly `amt` (and `sn ≠ rc`) |
| bridge to mainnet | `solvent_of_stake_bound` | If `total_supply + 2 × storage_usage × 1e19 ≤ balance`, then the "solvency" part of the invariant holds (every account entry is ≥ 63 bytes, and `minBal` = 125 bytes) |

A correction to the statement of T_no_one_else: the exception is the refund of a transfer that *someone else*
made *to* `u` (at most what was received is taken from `u`), not a transfer initiated by `u` itself (there the
balance of `u` only grows). Force-unregister is `u`'s own call; it is in the list of `T_who_can_lower`.

`b` in `T_exit` and `exit_always` is the balance at the moment the call executes. A callback still in flight
for a transfer made *to* `u` can lower `u`'s balance first; a `near_withdraw` signed for the larger balance
seen earlier then fails. The theorems speak about the balance at execution time
(`lean/Review/WNearVacuity.lean` has this case as an example).

### The invariant (the exact form of solvency)

```lean
structure Inv (E : Env) (S : Sys) : Prop where
  pre : Pre S.c        -- no duplicate keys, total_supply = Σ balances, supply ≤ u128::MAX
  solvent : S.c.supply + S.c.accts.length * E.minBal + E.base ≤ S.c.near
  cap : S.c.near ≤ E.cap
```

The contract's NEAR covers: all the wNEAR + one storage deposit (`minBal` = 1.25e21) for every registered
account + the base storage stake (the code, `STATE`, the account record). The form "balance ≥ supply + the
actual storage stake" is **not** inductive: unregistering a short id (an entry of 61+len < 125 bytes) returns
125 bytes, more than it frees. So the invariant carries the obligation `N × minBal`, and the actual stake
(`LackBalanceForState`) follows from it (`stor_le`).

`T_exit` needs all of `Inv`, not only `solvent`. On mainnet only the solvency part was checked (section 4);
`supply = Σ balances` was not checked there.

### The headline theorem

```lean
theorem exit_always (E : Env) (hE : E.Sane) (S : Sys) (hR : Reach E S) (u : Acct)
    (hu : u ≠ E.self) (hcap : S.c.near < E.cap) (b : Nat) (hb : get S.c.accts u = some b) :
    let S' := sysStep E S (.call u 1 (.near_withdraw b) [])
    bal S'.c.accts u = 0 ∧ S'.c.supply = S.c.supply - b ∧ S'.paid = S.paid ++ [(u, b + 1)]
```

`#print axioms` (all 14): `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`
(`Classical.choice` comes from `omega`/`simp`); `T_resolve_private*` — only `[propext]`. File `evidence/axioms.txt`.

## 2. The model

`lean/WNear/Model.lean` follows the 3.1.0 sources line by line (`core_impl.rs`, `storage_impl.rs`, `macros.rs`,
`w_near.rs`, the code generator of near-sdk-core 3.1.0), with exact u128 arithmetic (`overflow-checks = true` ⇒
an overflow is a failure).

- **State**: `accounts` (an association list = `LookupMap`), `total_supply`, the contract's NEAR balance.
- **Methods**: `near_deposit` (registration with `minBal` deducted), `near_withdraw` (exactly 1 yocto, a transfer of
  `amount+1`), `ft_transfer`, `ft_transfer_call` (step 1 + a callback in flight), `ft_resolve_transfer` (`#[private]`,
  not payable, `promise_result(0)`: `Failed`/garbage → the whole `amount`, otherwise `min(amount, unused)`; the
  receiver is debited, then the sender is read), `storage_deposit` (for oneself or another, refunds go to the
  predecessor), `storage_withdraw`, `storage_unregister` (with/without force), the view methods as transactions
  (the deposit stays with the contract), `new` (always fails: the state exists).
- **Runtime** (`exec`): the deposit is credited, transfer amounts are debited (`BalanceExceeded`), the storage stake
  is checked (`LackBalanceForState`); a failed receipt changes nothing.
- **System** (`Sys`, `Step`): arbitrary interleaving of calls by anyone (including callbacks of other contracts with
  any promise results), the callback of any transfer in flight with **any** result (any number, garbage, a panic, a
  failure), loss of a callback to gas, NEAR arriving (a transfer, the refund of a failed transfer). Everything a
  receiver's `ft_on_transfer` can do — call the contract in any order and return anything — is covered.

## 3. Conformance with the deployed wasm

The harness, `harness/src/main.rs`: near-contract-sim (nearcore 2.14.0, protocol 88), deploying **the same
bytes** (their sha256 → base58 is `DL2f5…`, and so is the account's code hash in the simulator). Accounts with ids of different
lengths, two stub receivers whose `ft_on_transfer` reply is set per transaction, `ghost.near` (registered, the
account does not exist), `evil.near` — a WAT contract that makes `ft_resolve_transfer` the callback of its own
failing promise (the SWEAT-class attack). Every trace: a random funding, 8–32 random operations with 0–3 blocks
between them (overlaps), callback delays `Hold(1..4)`, a forced failure of `ft_on_transfer`, then settling. The
model (`lake exe wnearmodel`) replays the receipts in execution order; `scripts/compare.py` compares, after
**every block**, the whole `accounts` (from storage), `total_supply`, the NEAR balance and `storage_usage`, and
for every receipt — success/failure, the callback's return value and the NEAR transfers.

| Measure | Value |
|---|---|
| Traces / receipts / blocks | 2000 / 55 825 / 58 022 |
| Balance comparisons / NEAR transfers compared | 329 546 / 7 499 |
| Verdict | **EXACT**, 0 MISMATCH |
| Callback branches | full refund 2507 · partial 89 · receiver empty 187 · unused=0 301 · sender removed → burn 38 |
| Receiver behaviour | a number 3534 · garbage 1329 · panic 894 · moved the tokens away with `ft_transfer` 1322 · `storage_unregister` 614 · `near_withdraw` 988 · callback held 1781 · forced failure 392 |
| Overlaps | 2672 of the 3122 callbacks ran with other transactions' receipts between the steps (6809 in total) |
| Actions sent by wrap.near | only `FunctionCall` 6244 and `Transfer` 7499 |

**A foreign call of `ft_resolve_transfer` on the deployed code** (`evidence/checks.json`): from a user, from a
contract and as the `promise_then` callback of `evil.near` — everywhere
`Panic("Method ft_resolve_transfer is private")`, the victim's balance did not change.
A repeated `new()` — `Panic("The contract has already been initialized")`.

**Mutants** (`scripts/mutants.sh`, `evidence/mutants.txt`): one rule of the model is changed, the traces are the same.

| Mutant | Conformance | Proofs |
|---|---|---|
| M1 refund ignores the receiver's balance | MISMATCH 131 | break |
| M2 garbage = "everything used" | MISMATCH 1321 | compile |
| M3 force-unregister without the burn | MISMATCH 2449 | break |
| M4 `near_withdraw` without returning the 1 yocto | MISMATCH 6533 | break |
| M5 deposit without deducting `minBal` | MISMATCH 23457 | break |
| M6 without `#[private]` | MISMATCH 2915 (the evil.near attack goes through in the model, not in the wasm) | break (`T_resolve_private`) |
| M7 the `storage_deposit` refund goes to the wrong account | MISMATCH 51 | compile |
| M8 unregister without force with a balance > 0 | MISMATCH 10156 | break |

Gas: the callback gets a fixed 5 Tgas and burns ≤ 1.79 Tgas (a margin of ≥ 3.2 Tgas on a small trie);
a whole `near_withdraw` ≈ 2.74 Tgas, `storage_unregister` ≈ 2.68 Tgas.

## 4. Mainnet (read-only RPC)

`evidence/mainnet_check.json`, block 224 128 229, all the values in one block:

| | |
|---|---|
| Access keys / code hash | 0 / `DL2f5…` |
| Balance / total_supply | 36 739 081.65 NEAR / 36 732 315.94 wNEAR |
| Surplus | 6 765.71 NEAR |
| Storage stake (168 885 525 bytes × 1e19) | 1 688.86 NEAR |
| `supply + 2 × stake ≤ balance` | **yes**, margin 3 388.0 NEAR ⇒ the solvency part of `Inv` (`solvent_of_stake_bound`) |
| Registered accounts (upper bound) | ≤ 2 677 776 |
| wNEAR on wrap.near itself | 107.55 |
| `supply = Σ balances` (the other part of `Inv`) | not checked on mainnet |

History (`evidence/history_upgrade.json`, `keys_history.json`, archival RPC):

```
29 998 009  the account is created (40 NEAR, no code)
~30 000 000 code 9kQaNisc… (172 779 bytes, its own FT implementation, no storage_unregister)
35 438 886  DeployContract DL2f5… (tx 4xtccqLAv25JU4F9HPRdKAeByGpjzA94GZcXY75cNM4), no migration;
            the new code reads the old state (supply 43 077.6 wNEAR); solvency: yes, margin 66.6 NEAR
40 858 545  DeleteKey (tx DUzJv1DVj3tyEgewoKK8ihHaq72SrJ38xMYeMeGoyFNh) — no keys since then, code DL2f5… before and after
now         0 keys, DL2f5…
```

The old code `9kQaNisc…` was run in the simulator (`oldinv`, `evidence/old_code_invariant.json`): 1000 traces,
31 393 blocks, checking after every block "supply = Σ balances" and "balance ≥ supply + N·minBal + the stake at
init" — **0 violations**; all 455 foreign calls of the callback were rejected. This is a test, not a proof.

## 5. Findings

1. **History ≠ "reachable from `new()` of this code"** (important for the wording). For ~5.4 million blocks wrap.near
   ran different code, which was replaced without a migration by the account's own key. The chain of reasoning for
   mainnet: `Inv` at the upgrade (solvency — checked on the archive; conservation — a test of the old code) → every
   step of the current code preserves `Inv` (proved, and `method_good` holds for **any** receipt, including calls
   made by the key owner in the name of the contract) → solvency now is checked directly. Not excluded by sampling:
   a temporary replacement of the code between 35 438 886 and 40 858 544 (an indexer is needed). `supply = Σ
   balances` on mainnet therefore rests on the test of the old code and on this sampling; it was not checked
   directly.
2. **107.55 wNEAR are locked forever on wrap.near itself.** What is sent to the contract's own address cannot be
   withdrawn by anyone: there are no keys, and the code does not call its own methods in its own name. This is why
   the condition `u ≠ wrap.near` in `T_exit` is necessary. The backing NEAR stays in the surplus.
3. **Force-unregister burns** (as in NEP-145): the balance disappears, the NEAR stays with the contract, the user
   receives only `minBal + 1`. This is `u`'s own choice (`T_force_unregister_burns`).
4. **The refund is taken from the receiver's current balance** (as in NEP-141): if the receiver has already spent
   what it received and holds other tokens, the refund (up to `amount`) is taken from those. The bound is
   `T_no_one_else`: no more than the amount of that transfer.
5. **The callback has a fixed 5 Tgas.** If it runs out of gas, the refund is lost (the tokens stay with the
   receiver). In the model this is the step `resolveFails`; conservation and T_no_one_else hold in that case too.
   The margin in the simulator is ≥ 3.2 Tgas; it was not measured on the mainnet trie.
6. **The wasm imports do not prove immutability**: near-sdk 3.1.0 pulls in `deploy_contract`, `add_key`,
   `delete_account` through the common Promise dispatcher. Immutability rests on "0 keys" + the source (the model)
   + execution (wrap.near sent only `FunctionCall` and `Transfer`).
7. **The exit needs 1 yocto** ⇒ a full-access key (or a contract able to attach a deposit); a key that can only call
   functions cannot withdraw. Tokens credited to a registered but non-existent account (`ghost.near`) wait until
   the account is created.

## 6. Assumptions and the trusted base

| # | Assumption | What supports it |
|---|---|---|
| A1 | The behaviour of the bytes `DL2f5…` = the model | 2000 traces EXACT, 8/8 mutants; not proved for all inputs; the build of the wasm from source was not reproduced |
| A2 | near-contract-sim / nearcore 2.14.0 = mainnet in the semantics of transfers, refunds, callbacks | the simulator runs nearcore's code; mainnet gas numbers may differ |
| A3 | Protocol: 1e19 yocto/byte (checked by RPC), 40 bytes of overhead per entry, ids of 2..64 characters ⇒ an entry ≤ `minBal` | `Env.Sane` |
| A4 | No keys; the code emits no deploy/add_key/delete_account | RPC (0 keys since 40 858 545); the source; execution |
| A5 | Gas is not modelled: running out of gas = a failed receipt with no changes; the user attaches ≥ ~3 Tgas | measurements |
| A6 | The balance of wrap.near is below the total NEAR supply (`hcap`) | 36.7 million of ~1.25 billion |
| A7 | Conservation at the height of the upgrade, and no temporary replacement of the code before the key was deleted | the test of the old code; sampling by height |
| A8 | The recipient of the withdrawal, `u`, exists while the transfer arrives (otherwise the NEAR returns to the contract — step `nearIn`) | NEAR semantics |
| A9 | The parsing layer in `Main.lean` (JSON arguments, id validation, the U128 string, the bytes of the promise result) | only the input classes the harness generates; not proved |
| — | The Lean 4.35 kernel; the axioms `propext`, `Quot.sound`, `Classical.choice` | |

## 7. Not covered

Gas on a trie of mainnet size (168 MB) and the behaviour when gas prices rise; multi-shard delays (the model allows
any order, the simulator has one shard); logs; the return values of the view methods (the state is compared); a
proof for the old code `9kQaNisc…`; a full audit of the 2021 transaction history; censorship by validators and
changes of the protocol constants.

## 8. How to reproduce

Everything needed is in this directory:

    ./check.sh          # proofs, axioms, non-vacuity example, deterministic checks, 2000-trace conformance
    ./check.sh --all    # + the 8 mutants, the old code's invariant run, the read-only mainnet check

The harness is built against the public `near/near-contract-sim` at commit `8e4b69b` (which pins nearcore
2.14.0); both are git dependencies, locked in `harness/Cargo.lock`. The exit status is 0 only if the proofs build
without `sorry`, the axioms are among `propext`, `Classical.choice`, `Quot.sound`, the deterministic checks hold
and the conformance verdict is EXACT (with `--all`: also every mutant is caught, the old code shows 0 violations
and the mainnet solvency hypothesis holds). `check.sh` rewrites `evidence/axioms.txt`, `checks.json`,
`conformance.json` (and with `--all` `mutants.txt`, `old_code_invariant.json`); their contents are deterministic.
The mainnet query of `--all` goes to `out/`, so the snapshot quoted in section 4 stays in `evidence/`.

Requirements: Linux x86-64, `elan` (Lean 4.35.0 is installed from `lean/lean-toolchain`), `rustup` (Rust 1.95.0
from `harness/rust-toolchain.toml`), a C/C++ compiler, `cmake` and libclang (for nearcore's RocksDB bindings),
`python3`, `git`; `--all` also needs GNU sed, bash 4 and network access. Without root, libclang can be taken from
the Python package: `python3 -m pip install libclang`, then set `LIBCLANG_PATH` to its
`site-packages/clang/native` directory and add there a link named after the library's soname
(`ln -s libclang.so libclang.so.18.1`). Paths can be changed with the environment variables `WNEAR_WASM`,
`OLD_WASM`, `OUT_DIR`, `CARGO_TARGET_DIR`, `JOBS` (see the header of `check.sh`).

**Time.** With everything built, `./check.sh` takes ≈ 20 s and `./check.sh --all` ≈ 1.5 min on a 32-core
machine. On a clean machine (32 cores, shared with other jobs; a fresh copy of this directory, no build products;
the toolchains and crate sources had just been downloaded by the pool-proof check; 2026-11-12) `./check.sh` took
7 min 9 s, of which 6 min 40 s to compile the harness with nearcore (8 jobs), and ended with the same EXACT
result; the evidence files it rewrote were byte-identical to the committed ones. There `./check.sh --all` then
took 75 s and `lean/kernel-check.sh` 130 s.

**The wasm inputs.** `wasm/w_near.wasm` is the upstream artefact `w-near/res/w_near.wasm` of
`near/core-contracts` at commit `54f8267`; `evidence/old_9kQaNisc.wasm` is the pre-upgrade code taken from the
chain (see `NOTICE`). `./fetch-wasm.sh` downloads the first again from that commit, checks the hash
(`DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1`) and compares it with the committed copy; with `--old` it also
downloads the old code from an archival RPC node (`view_code` at block 35 438 885) and compares.

**The non-vacuity example.** `lean/Review/WNearVacuity.lean`, from the independent review
(`../docs/REVIEW.md`), builds a concrete reachable state by real steps, applies `exit_always` to it, and shows
the case of a refund in flight that lowers the balance before a withdrawal. It is compiled by `lake build`
(so by `check.sh`) and can be checked alone with `cd lean && lake env lean Review/WNearVacuity.lean`.

**Re-checking the proofs in the kernel and in an independent kernel.** The checks of the independent review,
run in `lean/` after `lake build` (the three tools ship with the Lean 4.35.0 toolchain); `lean/kernel-check.sh`
runs them in this order:

    lake env leanchecker --fresh WNear                  # replays every declaration in the Lean kernel; silent on success
    lake env leanexport WNear > .lake/wnear.ndjson      # exports all declarations (about 350 MB)
    touch .lake/wnear.pp.txt                            # nanoda prints the three headline statements here; the file must exist
    lake env nanoda_bin nanoda.json                     # nanoda_bin 0.4.19: an independent kernel written in Rust

The expected last line is `Checked 59848 declarations with no errors`; `sorryAx` is named there only as an
exported axiom that is not permitted, i.e. it is not used.

## 9. Files

- `lean/WNear/Map.lean` — the association list and its lemmas; `Model.lean` — the model; `Lemmas.lean` — the
  specifications of the methods; `Theorems.lean` — the theorems; `lean/Main.lean` — the executable model
  (`lake exe wnearmodel`: a JSON trace → JSON states); `lean/Axioms.lean` — `#print axioms`;
  `lean/Review/WNearVacuity.lean`, `lean/nanoda.json`, `lean/kernel-check.sh`.
- `harness/` — the trace generator and the deterministic checks (`wnear-gen checks|traces|oldinv`).
- `wasm/w_near.wasm`, `fetch-wasm.sh`, `NOTICE`.
- `scripts/compare.py`, `mutants.sh`, `mainnet_check.py`, `history_check.py`, `keys_history.py`, `env.sh`; `check.sh`.
- `evidence/` — `axioms.txt`, `checks.json`, `conformance.json`, `mutants.txt`, `mainnet_check.json`,
  `history_upgrade.json`, `upgrade_solvency.json`, `keys_history.json`, `old_code_invariant.json`,
  `old_9kQaNisc.wasm` (from the archival RPC, hash checked), `wasm_imports.txt`, `crates_sha256.txt` (the 3.1.0
  crates from crates.io), `check_run.txt`.
- `check.sh` writes the traces and other bulky output to `out/` (about 60 MB) and the harness build to
  `harness/target/`; `--all` writes the mutant builds to `mutants/`. None of these is part of the repository.
