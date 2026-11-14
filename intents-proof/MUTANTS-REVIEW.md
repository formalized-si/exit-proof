# Why 13 one-line changes of the model were not noticed

An independent reviewer wrote 23 one-line changes of `lean/Intents/Ledger.lean`; the replay of the traces noticed
10. This file records, for each of the other 13, why it was missed. Section 1 was written before anything was
changed, from 240 traces of the generator as it was (seed 20261112: 40 of the standard token, 200 of the reply
mock; 12 951 receipts on the contract, 12 691 compared; the run and its counting script were working files, not
kept in this repository).

Three causes:

* **never** — no trace contains a call that reaches the changed line with inputs on which the change matters;
* **shadowed** — the traces contain the call, but the replay executable decided the same question with its own
  copy of the check (in `lean/Main.lean`) before, or instead of, calling the changed function;
* **not observable** — no call the contract accepts maps to inputs on which the change matters.

## 1. Before the extension

| change | cause | what the 240 traces show |
|---|---|---|
| X1 `ft_withdraw` ignores the auth-by-predecessor flag | never | no receipt switches the flag: 0 calls of `disable_auth_by_predecessor_id` / `force_*_auth_by_predecessor_ids`, 0 `set_auth_by_predecessor_id` intents; the flag is on for all 2 155 `ft_withdraw` receipts |
| X4 `ft_force_withdraw` refused to `DAO` | never | no account of the world holds `DAO`; the 176 calls are by the `UnrestrictedWithdrawer` holder (131) or by accounts with no role (45) |
| X5 a credit has no overflow guard | never | no credit of 2^127 or more: the tokens have a supply of 10^30, accounts acting as their own token deposit at most 10^24 |
| X8 reply-length limit 43 | never | of 646 `ft_transfer_call` results read by `ft_resolve_withdraw`, none is 43–46 bytes long (444 of at most 42, 68 of 47 or more, 134 failed) |
| X9 reply-length limit 45 | never | same: no result of exactly 45 bytes |
| X11 the used amount is not capped by the amount | never | no result within the length limit parses to more than the amount: the standard token caps what it reports, the mock's large number is 62 bytes |
| X15 an `FtWithdraw` intent ignores the pause of `intents` | shadowed | 16 `execute_intents` receipts ran with the pause on, 5 of them with an `ft_withdraw` intent; `mExecuteIntents` and `afterCredit` test the pause themselves and never evaluate `Via.ok .intent` with the pause on |
| X16 `UnpauseManager` can pause | never | the only holder of `UnpauseManager` also holds `PauseManager` |
| X17 anyone can pause | shadowed | 50 `pa_pause_feature` calls by accounts with no role, all rejected by the wasm; `mPause` tests the roles itself and calls `adminStep` only for a caller that passed |
| X18 anyone can lock | shadowed | 28 `force_lock_account` calls by accounts with no role; `mLock` tests the roles itself |
| X19 anyone can unlock | shadowed | 12 `force_unlock_account` calls by accounts with no role; `mLock` tests the roles itself |
| X20 a plain transfer with a non-empty return value counts as delivered | never | 1 003 `ft_transfer` results read, none is a success with a non-empty value: neither the standard token nor the mocks return one |
| X21 `ft_withdraw` may debit another owner | not observable | `ft_withdraw(token, receiver_id, amount, memo, msg)` has no owner argument: the debited account is the predecessor, so every receipt is `Via.method p` with `w.owner = p`, where the changed guard equals the original |

## 2. After the extension

What changed, by cause:

* **never** → the generator (`harness/src/main.rs`): one account for every role alone (`dao.near`, `forcer.near`,
  `pause1.near`, `unpause1.near`, `lock1.near`, `unlock1.near`, `acctmgr.near`, and five for the roles outside the
  token paths), a scripted token `stub.near` whose answers each operation chooses and which notifies deposits of any
  amount, the auth-by-predecessor switch, role grants, and nine probes — scripted sequences in which one guard is the
  only reason a call fails (`FORMAT.md`, section 3).
* **shadowed** → the replay (`lean/Main.lean`): it no longer repeats a guard the model has. Who may pause, unpause,
  lock or unlock is asked of `adminStep` itself (`stepAllowed`); the pause of `intents` is left to `Via.ok .intent`
  and `startUnwrap` for every call that contains an intent they guard (`pausedHere`); the lock of a signer is left
  to `debit` / `moveBal` / `adminStep` for every payload that has intents. No definition of the model changed.
* **not observable** → listed as EQUIVALENT with the reason, replayed anyway (it must give no disagreement), and
  the theorems are built with the change applied.

There are two replays now (`lean/OBSERVABLE.md`): the receipt replay — every receipt on the contract through the
ledger functions — and the world-level replay — the receipts of the token and of the contract together through
`Intents.stdStep`. A change counts as noticed when either disagrees with the wasm.

Run of that day (the numbers below are of that run; the present run is in section 5 and
`evidence/model_mutants.json`): `scripts/model_mutants.py` on 240 traces of the extended generator (seed 20261112: 100 of the standard
token, 70 of the fee mock, 70 of the reply mock; 15 248 receipts on the contract in the receipt replay, 5 098
receipts of the 100 standard traces in the world-level replay), `evidence/model_mutants.json`.

| change | what makes it visible now | receipts that disagree, receipt replay | world-level replay | result |
|---|---|---|---|---|
| X1 `ft_withdraw` ignores the auth-by-predecessor flag | probe `auth_flag` and random operations: an account with the flag off calls `ft_withdraw` with an amount it has | 61 | 238 | DETECTED |
| X4 `ft_force_withdraw` refused to `DAO` | `dao.near` calls `ft_force_withdraw` (probes `forced`, `role_sweep`, random operations) | 79 | 308 | DETECTED |
| X5 a credit has no overflow guard | the scripted token notifies a deposit that would lift a supply over 2^128 − 1 (probe `bounds`, random operations) | 91 | 0 | DETECTED |
| X8 reply-length limit 43 | the scripted token answers `ft_transfer_call` with exactly 44 bytes | 43 | 0 | DETECTED |
| X9 reply-length limit 45 | … with exactly 45 bytes | 45 | 0 | DETECTED |
| X11 the used amount is not capped by the amount | the scripted token reports more than the amount; the value `ft_resolve_withdraw` returns differs | 24 | 0 | DETECTED |
| X15 an `FtWithdraw` intent ignores the pause of `intents` | the replay leaves that pause to the model for a call with an `ft_withdraw` intent; probe `intents_pause` relays one with the pause on | 33 | 0 | DETECTED |
| X16 `UnpauseManager` can pause | `unpause1.near`, which holds `UnpauseManager` only, calls `pa_pause_feature` | 38 | 108 | DETECTED |
| X17 anyone can pause | `mPause` asks `adminStep` | 149 | 723 | DETECTED |
| X18 anyone can lock | `mLock` asks `adminStep` | 158 | 326 | DETECTED |
| X19 anyone can unlock | `mLock` asks `adminStep` | 151 | 89 | DETECTED |
| X20 a plain transfer with a non-empty return value counts as delivered | the scripted token's `ft_transfer` succeeds with a value | 70 | 0 | DETECTED |
| X21 `ft_withdraw` may debit another owner | nothing can: the method has no owner argument, the wasm debits the predecessor, so every receipt is `Via.method p` with `w.owner = p`, where the changed guard equals the original | 0 | 0 | EQUIVALENT for both replays; the proofs reject it — `T4_who_can_lower` stops compiling |

All 34 changes (11 of the kit, 23 of the independent reviewer): 33 DETECTED, 1 EQUIVALENT, the unchanged model
passes. The 10 that the independent reviewer's run already noticed are noticed again, and so are the kit's 11.

38 further changes were added, so that every guard of the model has at least one change and so has the step
function of the world: forced internal transfers, the auth-by-predecessor switch, each role list widened and
narrowed, the bounds of `debit` and `moveBal`, the key `ALL`, the four changes of the wNEAR ledger functions that
`scripts/replay_mutants.sh` used to run (two of them, the guards of the unwrap path, were missed before for the
"shadowed" reason), and eight changes of `Intents/World.lean`. Of all 72 changes 67 are DETECTED and 5 are
EQUIVALENT; none is missed.

## 3. Score per guard

As of section 2, with 72 changes. B7 and W4 are counted EQUIVALENT since section 5, and the strict world added
guards; the present score per guard is in section 5 and `evidence/model_mutants_by_guard.json`.

One row per guard or rule of the model; the changes are named by their id in `scripts/model_mutants.py`. "Receipt
replay" and "world replay" count the changes each of the two notices.

| guard or rule | changes | noticed | by the receipt replay | by the world replay | equivalent | missed |
|---|---|---|---|---|---|---|
| FtWithdraw intent: intents are not paused | X15 | 1 | 1 | 0 | 0 | 0 |
| SetAuthByPredecessorId intent: applied unless the account is locked | A9 B7 | 2 | 2 | 1 | 0 | 0 |
| arithmetic of credit and debit | M1 M2 M4 W1 W2 | 5 | 5 | 3 | 0 | 0 |
| credit: supply and balance stay within u128 | X5 | 1 | 1 | 0 | 0 | 0 |
| credit: the amount is positive | X7 | 1 | 1 | 0 | 0 | 0 |
| debit: the account is not locked, unless forced | M3 X22 | 2 | 2 | 2 | 0 | 0 |
| debit: the amount is positive | X6 | 1 | 1 | 1 | 0 | 0 |
| debit: the amount is within balance and supply | B1 | 1 | 1 | 1 | 0 | 0 |
| deposit: ft_on_transfer is not paused | V1 | 1 | 0 | 1 | 0 | 0 |
| deposit: the credited account is the one msg names | V8 | 1 | 0 | 1 | 0 | 0 |
| disable auth by predecessor (self): the flag is on, the account is not locked | A6 B6 | 2 | 2 | 2 | 0 | 0 |
| forced auth switch: locker roles to disable, unlocker roles to enable | A7 A8 A14 | 3 | 3 | 3 | 0 | 0 |
| forced internal move: DAO or UnrestrictedWithdrawer | A1 A2 | 2 | 2 | 1 | 0 | 0 |
| ft_force_withdraw: DAO or UnrestrictedWithdrawer | X2 X3 X4 | 3 | 3 | 3 | 0 | 0 |
| ft_withdraw, ft_force_withdraw: no storage deposit | E1 E2 | 0 | 0 | 0 | 2 | 0 |
| ft_withdraw: auth by predecessor is enabled | X1 | 1 | 1 | 1 | 0 | 0 |
| ft_withdraw: the caller is the owner | X21 | 0 | 0 | 0 | 1 | 0 |
| ft_withdraw: the method is not paused | B2 | 1 | 1 | 1 | 0 | 0 |
| internal move by the owner: the source is not locked | X14 | 1 | 1 | 0 | 0 | 0 |
| internal move: source and destination differ, the amount is positive | X12 X13 | 2 | 2 | 0 | 0 | 0 |
| internal move: the amount is within the source balance | B3 | 1 | 1 | 0 | 0 | 0 |
| internal move: the destination stays within u128 | E4 | 0 | 0 | 0 | 1 | 0 |
| isPaused: the key or ALL | M10 B8 | 2 | 2 | 2 | 0 | 0 |
| lock: DAO, locker or account manager | X18 A4 A5 A12 | 4 | 4 | 4 | 0 | 0 |
| pause: DAO or PauseManager | X16 X17 A10 B4 | 4 | 4 | 4 | 0 | 0 |
| refund rules of ft_resolve_withdraw | M5 M6 M7 M8 M9 M11 X8 X9 X10 X11 X20 | 11 | 11 | 4 | 0 | 0 |
| startWithdraw: the amount is a u128 | E3 | 0 | 0 | 0 | 1 | 0 |
| unlock: DAO, unlocker or account manager | X19 X23 A13 | 3 | 3 | 3 | 0 | 0 |
| unpause: DAO or UnpauseManager | A3 A11 B5 | 3 | 3 | 3 | 0 | 0 |
| unwrap: intents are not paused | W3 | 1 | 1 | 0 | 0 | 0 |
| unwrap: the account is not locked | W4 | 1 | 1 | 0 | 0 | 0 |
| world: what a callback reads is what the other contract returned | V2 V3 V4 V7 | 4 | 0 | 4 | 0 | 0 |
| world: which receipts a call starts | V5 V6 | 2 | 0 | 2 | 0 | 0 |

The 8 changes of the world step (V1 V2 V3 V4 V5 V6 V7 V8) are noticed by the world-level replay only: the receipt
replay does not run `Intents.step`.

The equivalent changes, each with the reason why no receipt reaches the guard with inputs on which it matters, and
what the theorems do with the change applied:

| change | why no receipt can show it | the theorems |
|---|---|---|
| X21 ft_withdraw may debit another owner | ft_withdraw(token, receiver_id, amount, memo, msg) has no owner argument: the wasm debits the predecessor, so every receipt is Via.method p with w.owner = p, and on those inputs the changed guard equals the original | the theorems do not compile: first error in Intents/Theorems.lean, theorem T4_who_can_lower |
| E1 ft_withdraw accepts a withdrawal with a storage deposit | ft_withdraw has no storage_deposit argument (withdraw.rs:25-50 builds the FtWithdraw with storage_deposit: None), so every receipt of the method has w.sd = none | the theorems do not compile: first error in Intents/Theorems.lean, theorem T4_who_can_lower |
| E2 ft_force_withdraw accepts a withdrawal with a storage deposit | ft_force_withdraw has no storage_deposit argument (withdraw.rs:199-225), so every receipt of it has w.sd = none | the theorems do not compile: first error in Intents/Theorems.lean, theorem T4_who_can_lower |
| E3 a withdrawal amount above the u128 range is accepted | the amount of every receipt is a U128 argument; a larger number fails to deserialize before the model is asked | the theorems do not compile: first error in Intents/Ledger.lean, theorem startWithdraw_some |
| E4 an internal move may lift the destination above the u128 range | in every state of a trace the balances of a ledger id sum to its supply, a u128; source and destination differ and the amount is within the source balance, so the destination balance plus the amount is at most the supply | the theorems do not compile: first error in Intents/Ledger.lean, theorem moveBal_some |

Four guards therefore rest on the proofs and on reading the source, not on the replay: that `ft_withdraw` debits
its caller, that the two withdrawal methods carry no storage deposit, that a withdrawal amount is a `u128`, and that
a destination balance stays within `u128`. For the last two the first statement to fail is the lemma that restates
the definition (`startWithdraw_some`, `moveBal_some`); for the first two it is `T4_who_can_lower`.

**E3 and E4: no statement about reachable states fails under them, and that is proved.** Both guards are implied
by the invariant in every reachable state. `startWithdraw_amount_guard_redundant`
(`lean/Intents/StrictTheorems.lean`): in a reachable state `startWithdraw` equals the same function without the
guard `w.amount ≤ U128_MAX` — a debit needs the amount within the total supply, and the supply is at most the
tokens the contract holds, a `u128` (`T1_supply`, `T1_ledger_covered`, the token's own bound).
`moveBal_destination_guard_redundant`: in a reachable state the guard `bal dst + amt ≤ U128_MAX` of `moveBal`
follows from its other two — source and destination differ and the amount is within the source balance, so the
destination balance plus the amount is at most the sum of all balances, which is the supply. So the model with E3
or E4 applied has the same reachable states and the same steps between them as the unchanged model, and every
statement that speaks about reachable states (T1, T1_exact, T2_settles, T3_covered) is as true of it. A theorem can
"fail" under them only if it speaks about ledgers that no run reaches — a supply above the `u128` range;
`lean/Intents/StrictExamples.lean` has one such ledger, on which the guard of E3 is the only thing that stops a
withdrawal — and such a theorem is a restatement of the definition, which is what `startWithdraw_some` and
`moveBal_some` are. The two guards are in the model because its amounts are natural numbers while the contract's are
`u128` with checked arithmetic; they are equivalent changes in the strict sense, not gaps of the replay.


## 4. What the replays still do not compare

Counted by reason in every run (`not_compared` in the summary of `intentsmodel`, `evidence/conformance.json`):

* **gas** — a receipt that failed because the harness forced it to, or because it ran out of the attached gas.
  The model has no gas. That such a receipt changes nothing is compared.
* **the signature itself** — a payload whose signature does not verify (the generator makes some on purpose). The
  model has no ed25519. The other tests of a payload — verifying contract, deadline, registered key, nonce — were
  "not compared" before and are decided now from what the trace records.
* **no receipt is skipped** in these traces. Never called with the permission: `upgrade` (it would replace the
  code); `admin_call`, `cleanup_nonces` and `invalidate_salts` are called by their role holders with empty lists
  only.

A change inside one of these classes would still be missed: there is nothing in the model to change for gas and
signatures, and two sets of rules live in the replay executable, not in the model — the role sets and success
conditions of the eleven guarded methods outside the ledger (`outsideGuards`, `mOutside`), and the entry-point guards
of the NEP-245 deposit and withdrawal methods, for which the model has no function (the pause keys `mt_withdraw`,
`mt_on_transfer` and the auth flag in `mMtWithdraw`, `mMtOnTransfer`; the pause of `ft_on_transfer` in the receipt
replay — the world-level replay takes that one from `Intents.step`). Three sets that were on this list are functions
of the model since the strict world (section 5): the near-plugins rules of the role table (`Intents.aclStep`), the
admission of a signed payload (`Intents.admit`), and the pause and the auth flag of `mt_transfer*`
(`Intents.directOk`). They are compared with the wasm on every receipt, but
changing the model cannot test them. No role list of the model is repeated in the executable any more: every
forced method asks `Via.ok` or `MoveAuth.ok`, every switch asks `adminStep`.

The world-level replay covers the standard token only. The wNEAR world (`IntentsW.step`: the unwrap jobs, the
`do_*` callbacks, the NEAR that wNEAR sends back) is not run by any replay; its two ledger functions are, in the
receipt replay.

## 5. After the strict world

The model gained two files. `lean/Intents/Auth.lean` has the functions for what the replay executable decided with
code of its own before, or did not decide at all: the refund of a transfer call (`Xc.refund`, `resolveTransfer`), the
entry guard of `mt_transfer*` (`directOk`), what is tested of a signed payload before its intents run (`hasKey`,
`admit`, `commitNonce`), the public keys of an account (`addKey`, `removeKey`), and the near-plugins rules of the role
table (`Acl.isAdmin`, `aclStep`). `lean/Intents/Strict.lean` has the strict world; its step function `sstep` uses
these functions, keeps the transfer calls whose `mt_resolve_transfer` is in flight, and changes the role table by
`aclStep` only.

What the replays do with them (`lean/OBSERVABLE.md`):

* **receipt replay** — `mt_resolve_transfer` computes every row with `resolveTransfer`; `mt_transfer*` asks
  `directOk`; a signed payload is admitted by `admit` and its nonce committed by `commitNonce`; `add_public_key` and
  `remove_public_key` are `addKey` / `removeKey`, behind the auth-flag guard of the strict step itself
  (`keyCallAllowed` asks `sstep`); the nine `acl_*` methods are `aclStep`, and whether the caller has the permission —
  which decides the `null` return value — is asked of `aclStep` as well (`aclPermitted`). The three functions section 4
  used to name (`mAcl`, `admitPayload`, the pause and the auth flag in `mMtTransfer`) no longer keep a copy of
  the rules: they ask the model.
* **world-level replay** — the internal transfers of the token's ledger id and the `acl_*` calls run through `sstep`.
  A transfer call leaves an entry in `SWorld.calls`, followed by the receipt id of its `mt_resolve_transfer`; that
  receipt must find its entry with the same previous owner, receiver and amount, the refund is the model's, and the
  entry must be gone afterwards. The role table is advanced by the model and compared with the trace after every
  receipt; before, the grantees were copied from the trace after every `acl_*` call.
* **generator** — two probes, `keys` and `edges` (`FORMAT.md`, section 3). They were added after a first run of the
  new changes on the traces of the generator as it was: six changes gave no disagreement there, because no trace
  reached the guard with inputs on which it matters (R1: no receiver that holds more than it was sent asked for more
  than the amount; P5: no locked account signed a payload none of whose intents tests the lock itself; C6: no account
  without the permission called `acl_revoke_admin` for an existing admin; C7: no admin renounced; C10: the super-admin
  never handed its role over; S5: no `mt_resolve_transfer` of the token's ledger id failed for gas), and no trace
  added or removed a public key. All six are noticed with the two probes.

Run: `scripts/model_mutants.py` on 240 traces of the generator with the two probes (seed 20261112: 100 of the standard
token, 70 of the fee mock, 70 of the reply mock; 15 237 receipts on the contract in the receipt replay, of which 15 093 agree and 0 disagree on the unchanged model;
5 197 receipts of the 100 standard traces in the world-level replay, 5 147 agree, 0 disagree, 50 failed for gas with
nothing changed).

49 changes of the new functions, one row per guard or rule:

| guard or rule | changes | noticed | by the receipt replay | by the world replay | equivalent | missed |
|---|---|---|---|---|---|---|
| mt_resolve_transfer: the refund is the request capped by the amount and by the receiver's balance | R2 R3 R1 | 3 | 3 | 2 | 0 | 0 |
| mt_resolve_transfer: a positive refund moves from the receiver back to the sender | R4 R5 R6 | 3 | 3 | 2 | 0 | 0 |
| mt_transfer*: mt_transfer is not paused, auth by predecessor is enabled | D1 D2 D3 | 3 | 3 | 0 | 0 | 0 |
| signed payload: the verifying contract is this contract | P1 | 1 | 1 | 0 | 0 | 0 |
| signed payload: the deadline has not passed | P2 | 1 | 1 | 0 | 0 | 0 |
| signed payload: the key is one of the signer's | P3 K1 K2 | 3 | 3 | 0 | 0 | 0 |
| signed payload: the nonce is new, and is committed | P4 P6 | 2 | 2 | 0 | 0 | 0 |
| acl_grant_role: a super-admin or an admin of the role | C1 C2 | 2 | 2 | 2 | 0 | 0 |
| acl_revoke_role: a super-admin or an admin of the role | C3 | 1 | 1 | 1 | 0 | 0 |
| acl_renounce_role: the caller's own role goes | C4 | 1 | 1 | 1 | 0 | 0 |
| acl_add_admin: a super-admin or an admin of the role | C5 | 1 | 1 | 1 | 0 | 0 |
| acl_add_super_admin: a super-admin | C8 | 1 | 1 | 1 | 0 | 0 |
| acl_revoke_super_admin: a super-admin | C9 | 1 | 1 | 0 | 0 | 0 |
| acl_transfer_super_admin: a super-admin, who stops being one | C11 C10 | 2 | 2 | 2 | 0 | 0 |
| is_admin: a super-admin, or an admin of that role | C12 C13 | 2 | 2 | 2 | 0 | 0 |
| strict world: a transfer call, and only a transfer call, leaves one mt_resolve_transfer in flight | S1 S3 S4 S10 | 4 | 0 | 4 | 0 | 0 |
| strict world: mt_resolve_transfer takes its entry, moves the refund, and the entry is gone | S2 S8 S5 | 3 | 0 | 3 | 0 | 0 |
| strict world: an acl_* call updates super-admins, admins and grantees | S6 S7 S11 | 3 | 0 | 3 | 0 | 0 |
| strict world: a transfer by the owner moves the balance | S13 | 1 | 0 | 1 | 0 | 0 |
| signed payload: the signer is not locked | P5 | 1 | 1 | 0 | 0 | 0 |
| acl_revoke_admin: a super-admin or an admin of the role | C6 | 1 | 1 | 1 | 0 | 0 |
| acl_renounce_admin: the caller's own admin entry goes | C7 | 1 | 1 | 1 | 0 | 0 |
| add_public_key: the key is not there yet, and is there afterwards | K4 K8 | 2 | 2 | 0 | 0 | 0 |
| remove_public_key: the key is there, and is gone afterwards | K5 K9 | 2 | 2 | 0 | 0 | 0 |
| add_public_key, remove_public_key: the account is not locked | K6 K7 | 2 | 2 | 0 | 0 | 0 |
| strict world: add_public_key and remove_public_key need auth by predecessor enabled | S14 S15 | 2 | 2 | 0 | 0 | 0 |

49 of the 49 are DETECTED. 11 are noticed by the world-level replay only (S1 S2 S3 S4 S5 S6 S7 S8 S10 S11 S13): they
change `sstep` itself, which the receipt replay does not run. 22 are noticed by the receipt replay only, 16 by both.

| change | receipts that disagree, receipt replay | world-level replay |
|---|---|---|
| R2 the refund of a transfer call is not capped by the receiver's balance | 3 | 0 |
| R3 mt_resolve_transfer takes back the whole amount, whatever the receiver asked for | 3 | 35 |
| R4 mt_resolve_transfer never moves a refund | 124 | 414 |
| R5 mt_resolve_transfer with nothing to refund fails | 3 | 0 |
| R6 the refund moves from the sender to the receiver | 124 | 414 |
| D1 mt_transfer ignores the pause of mt_transfer | 1 | 0 |
| D2 mt_transfer ignores the auth-by-predecessor flag of the caller | 25 | 0 |
| D3 mt_transfer is paused by the key intents instead of mt_transfer | 4 | 0 |
| P1 a payload for another verifying contract is accepted | 12 | 0 |
| P2 a payload whose deadline has passed is accepted | 14 | 0 |
| P3 a payload is accepted whatever key signed it | 99 | 0 |
| P4 a payload with a used nonce is accepted | 16 | 0 |
| P6 an executed payload does not commit its nonce | 16 | 0 |
| K1 a key registered for the account is not one of its keys | 590 | 0 |
| K2 a key registered for any account counts as a key of this one | 74 | 0 |
| C1 acl_grant_role needs no permission | 64 | 415 |
| C2 acl_grant_role is refused to an admin of the role | 12 | 41 |
| C3 acl_revoke_role needs no permission | 53 | 12 |
| C4 acl_renounce_role removes nothing | 20 | 190 |
| C5 acl_add_admin needs no permission | 27 | 251 |
| C8 acl_add_super_admin needs no permission | 48 | 313 |
| C9 acl_revoke_super_admin needs no permission | 9 | 0 |
| C11 acl_transfer_super_admin needs no permission | 17 | 136 |
| C12 a super-admin is not an admin of every role | 101 | 186 |
| C13 an admin of one role is an admin of every role | 4 | 86 |
| S1 a transfer call leaves no mt_resolve_transfer in flight | 0 | 415 |
| S2 mt_resolve_transfer leaves its transfer call in flight (it could run again) | 0 | 20 |
| S3 the entry of a transfer call names the sender as the receiver | 0 | 414 |
| S4 a plain transfer leaves an mt_resolve_transfer in flight | 0 | 82 |
| S6 an acl_* call does not change the super-admins | 0 | 124 |
| S7 an acl_* call does not change the grantees | 0 | 171 |
| S8 mt_resolve_transfer removes its entry and moves no refund | 0 | 414 |
| S10 a forced transfer call leaves no mt_resolve_transfer in flight | 0 | 130 |
| S11 an acl_* call does not change the admins of a role | 0 | 52 |
| S13 a transfer by the owner leaves the balances as they are | 0 | 526 |
| R1 the refund of a transfer call is not capped by the amount of the transfer | 37 | 162 |
| P5 a payload of a locked signer is accepted | 10 | 0 |
| C6 acl_revoke_admin needs no permission | 34 | 14 |
| C7 acl_renounce_admin removes nothing | 34 | 253 |
| C10 acl_transfer_super_admin leaves the caller a super-admin | 68 | 242 |
| S5 an mt_resolve_transfer that failed for gas stays in flight | 0 | 6 |
| K4 add_public_key accepts a key the account already has | 25 | 0 |
| K5 remove_public_key accepts a key the account does not have | 25 | 0 |
| K6 a locked account can add a key | 10 | 0 |
| K7 a locked account can remove a key | 10 | 0 |
| K8 add_public_key succeeds and registers nothing | 137 | 0 |
| K9 remove_public_key succeeds and the key stays | 125 | 0 |
| S14 add_public_key runs for an account whose auth-by-predecessor flag is off | 15 | 0 |
| S15 remove_public_key runs for an account whose auth-by-predecessor flag is off | 15 | 0 |

### Two earlier changes can no longer be told apart by a receipt

W4 (an unwrap ignores the account lock) and B7 (a `SetAuthByPredecessorId` intent of a locked account is applied)
were DETECTED in section 3 and are EQUIVALENT now. Both remove a lock test from a function that only an intent of a
signed payload reaches. The contract tests the lock of the signer once per payload, in `commit_nonce`, before the
first intent runs. The model had no such test: the replay tested the lock itself for a payload without intents and
left it to the function of each intent otherwise, so those functions were the only place and a change there showed.
`Intents.admit` now has the contract's test, and a payload of a locked signer never reaches the intent, in the model
as in the wasm. The lock tests that a direct call reaches too are still noticed (M3 and X22 in `debit` through
`ft_withdraw` and the forced withdrawals, X14 in `moveBal` through `mt_transfer`), and so is the test in `admit` (P5).
What the theorems do with the two changes (`evidence/model_mutants.json`, field `proofs`, run of
`./check.sh --mutants --tla` kept as `evidence/check_run.txt`): W4 — they do not compile, first error in
`IntentsW/Backing.lean`, theorem `startUnwrap_some`, a lemma that restates the definition; B7 — they do not compile,
first error in `Intents/StrictTheorems.lean`, theorem `T4_auth_flag_power`, which says that the authentication flag
of an account changes by its `SetAuthByPredecessorId` intent only when the account is not locked. Before that
theorem was stated, B7 broke no statement.

With them the list of `scripts/model_mutants.py` has 121 changes: 114 DETECTED, 7 EQUIVALENT
(X21 B7 E1 E2 E3 E4 W4), none missed; of the 72 changes of section 3, 65 are DETECTED (67 before) and
7 EQUIVALENT (5 before). The numbers in sections 1 to 3 are those of the runs they describe.

### Not exercised by any trace

These are not equivalent changes: a receipt could show each of them, and no trace has such a receipt. They are kept
out of the count above. `MUT_UNEXERCISED=1 scripts/model_mutants.py …` replays the first of them and records that
neither replay disagrees.

| part of the model | why no trace reaches it |
|---|---|
| K3: the implicit half of `hasKey` (a key is a key of the account whose id is its implicit account id, unless removed), and with it the implicit branches of `addKey` and `removeKey` | every account of a trace is a named account and registers its key explicitly; the replay gives the model an `implicit` function that maps a key to a string that is no account id |
| the strict step `payload` as a whole (`runOps`, `runOp` except its `move` case), and `Op.move` with `call = true` | the world-level replay applies the intents of a successful call one by one; what is tested of a payload is compared in the receipt replay through `admit`; no trace has a `Transfer` intent with a notification |
| the strict steps `addKey` / `removeKey` as steps, and `Step.free` | the world-level replay does not follow keys, and runs the receipts that are not internal transfers or `acl_*` calls through `Intents.stdStep` directly; the auth-flag guard of the two steps is asked of `sstep` by the receipt replay (S14, S15) |
| the guard `directOk` at its use in the strict step `transfer` | the world-level replay does not decide whether an internal transfer succeeds (that depends on the rows of other ledger ids): it applies the step when the receipt succeeded. The function itself is compared in the receipt replay (D1, D2, D3) |
