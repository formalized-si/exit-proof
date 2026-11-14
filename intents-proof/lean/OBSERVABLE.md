# What the executable model reads and prints

`intentsmodel` (source `Main.lean`) replays traces in the format of `../FORMAT.md`. It has two
replays: the receipt replay described first (every receipt on the contract, every ledger id,
through the ledger functions), and the world-level replay at the end (`--world`: the receipts
of the token and of the contract together, through the step function of the two-contract
world).

## Input

stdin, JSON Lines, one trace per line. From each trace it uses `world.contract`,
`world.private`, `world.keys`, `init.state` (with the role table `acl`), and from every entry of
`steps` with `recv == world.contract` and a `method`: `pred`, `method`, `args`, `deposit`,
`results`, `ts`, `ok`, `status`, `fault`, `ret`, `state`. Receipts on other accounts are the
environment and are not replayed. The wNEAR account is taken to be `wrap.near` (the harness
world). Traces written before `state.acl`, `state.auth_off`, `ts` and `world.keys` existed are
read too: the roles then come from `world.roles`, and what cannot be decided without the missing
fields is reported as not compared (below).

## What is computed

For each such receipt the model decides, from the inputs only, whether the receipt succeeds and
what the ledger is afterwards. The ledger functions are those of `Intents/Ledger.lean`
(`credit`, `debit`, `startWithdraw`, `Rs.used`, `resolveWithdraw`, `moveBal`, `adminStep`), those
of `Intents/Auth.lean` (`Xc.refund`, `resolveTransfer`, `directOk`, `admit`, `commitNonce`,
`addKey`, `removeKey`, `aclStep`) and, for the debits of the wNEAR ledger, the two of `IntentsW/World.lean`
(`startWithdrawW`, `startUnwrap`), applied to one ledger per token id:

| method | computed with |
|---|---|
| `ft_on_transfer` | `credit` on `nep141:<pred>`; then the inline intents of `msg`, if any |
| `ft_withdraw`, `ft_force_withdraw` | `startWithdraw` (`Via.method` / `Via.force`) |
| `ft_resolve_withdraw` | `Rs.used`, `resolveWithdraw`; return value `used` |
| `mt_transfer`, `mt_batch_transfer`, `mt_transfer_call`, `mt_batch_transfer_call` | `directOk` (the pause of `mt_transfer`, the auth-by-predecessor flag of the caller), then `moveBal .owner` per token id, all or nothing |
| `mt_resolve_transfer` | per row one transfer call `Xc` (previous owner, receiver, amount): `resolveTransfer`, whose refund is `Xc.refund` — the requested one capped by the amount and by the receiver's balance; return value (the amounts minus the refunds) |
| `execute_intents` | per signed payload, per intent: `transfer` → `moveBal .owner`; `ft_withdraw` of wNEAR → `IntentsW.startWithdrawW .intent` (the amount and the storage deposit from the same ledger); `ft_withdraw` of another token → `startWithdraw .intent` (+ `IntentsW.startUnwrap` on `nep141:wrap.near` for a storage deposit); `mt_withdraw` → `debit` per id (+ `IntentsW.startUnwrap` for a storage deposit); `native_withdraw`, `storage_deposit` → `IntentsW.startUnwrap`. Before the intents of a payload: the model's `admit` and `commitNonce` (`admitPayload`, below). The signature is **not** checked |
| `mt_on_transfer` | `credit` on `nep245:<pred>:<id>` per token; then inline intents |
| `mt_withdraw`, `mt_force_withdraw` | `debit` per token id; who may force is `Via.ok` of `Via.force`, the model's role test of a forced withdrawal |
| `mt_resolve_withdraw` | `credit` of `amount - min(used, amount)` per token; return value |
| `do_ft_withdraw`, `do_mt_withdraw`, `do_native_withdraw`, `do_storage_deposit` | no ledger change; success needs the `near_withdraw` result to be an empty success when a storage deposit / unwrap precedes |
| `mt_force_transfer`, `mt_force_batch_transfer`, `mt_force_transfer_call`, `mt_force_batch_transfer_call` | `moveBal (.force pred)` per token id, all or nothing |
| `nft_force_withdraw` | `startWithdraw` (`Via.force`) of one unit of `nep171:<token>:<id>` |
| `pa_pause_feature`, `pa_unpause_feature`, `force_lock_account`, `force_unlock_account` | `adminStep`; return value |
| `disable_auth_by_predecessor_id` | `adminStep (.authOffSelf pred)` |
| `force_disable_auth_by_predecessor_ids`, `force_enable_auth_by_predecessor_ids` | `adminStep (.authForce pred a enable)` for every listed account |
| the intent `set_auth_by_predecessor_id` | `adminStep (.authIntent signer enabled)` |
| `acl_grant_role`, `acl_revoke_role`, `acl_renounce_role`, `acl_add_admin`, `acl_revoke_admin`, `acl_renounce_admin`, `acl_add_super_admin`, `acl_revoke_super_admin`, `acl_transfer_super_admin` | the model's `aclStep` on the table of super-admins, admins and grantees (`Intents/Auth.lean`); return value (`null` for a caller without the permission — asked of `aclStep` too, `aclPermitted` in `Main.lean` — otherwise whether the table had the entry) |
| `add_public_key`, `remove_public_key` | one yoctoNEAR; the auth-by-predecessor flag of the caller, asked of the strict world's own steps `addKey` / `removeKey` (`keyCallAllowed`: `Intents.sstep` on a state where the call shows); then the model's `addKey` / `removeKey` on the keys the replay carries: the account is not locked, the key is not there yet / is there |
| `upgrade`, `admin_call`, `set_fee`, `set_fee_collector`, `add_full_access_key`, `delete_key`, `add_relayer_key`, `delete_relayer_key`, `cleanup_nonces`, `update_current_salt`, `invalidate_salts` | fails for a caller without one of the roles (`Ctl.any`). For a holder: whether the call succeeds (`mOutside` in `Main.lean`: the deposit, the pause of `intents` where it applies, "same value" for the fee and the collector, "key not found" for a relayer key), with the fee, the collector and the relayer keys as replay state; the ledger and the switches do not change. An authorised `upgrade`, and `admin_call` / `cleanup_nonces` / `invalidate_salts` with a non-empty list: `skip` |
| `do_add_relayer_key` called by the contract | fails when the key is already a relayer key |
| a method of `world.private` called by another account, `new` | fails |
| view methods called in a transaction | succeed, no change |
| anything else | outside the model: `skip` |

**Guards are evaluated by the model's functions, not by copies of them.** Who may pause,
unpause, lock, unlock or switch the auth flag is asked of `adminStep` itself (`stepAllowed` in
`Main.lean`: `adminStep` returns the state unchanged for a caller without the role, so the step is
run on a state where its effect is visible and the answer is whether the state changed); who may
force a withdrawal or a transfer is `Via.ok` / `MoveAuth.ok` inside `startWithdraw` / `moveBal`.
Whether the caller of an `acl_*` method has the permission is asked of `aclStep` in the same way
(`aclPermitted`: the same call for an account that is in no list, on a table where the change
shows); the pause and the auth flag of `mt_transfer*` are `directOk`; what is tested of a signed
payload is `admit`.
One guard the contract tests once per call and the model tests per ledger function, and one that
the model tests once per payload:

* the pause of `intents`: `Via.ok .intent` (an `ft_withdraw` intent) and `IntentsW.startUnwrap`
  (`native_withdraw`, `storage_deposit`, a storage deposit) test it; `Main.lean` tests it only for
  an `execute_intents` (or a deposit message) none of whose intents does (`pausedHere`);
* the lock of the signer (`commit_nonce`): the model's `admit` tests it for every payload, before
  any intent runs. `Main.lean` has no test of its own. The lock tests inside the functions an
  intent runs (`debit`, `moveBal .owner`, `adminStep`, `IntentsW.startUnwrap`) are still there,
  but for a signed payload they come second: a change of one of them shows in the replay only
  where a direct call reaches the same function (`../MUTANTS-REVIEW.md`, section 5).

A call that succeeds in the model has run every one of its intents, so the first is sound for the
unchanged model, and a change of that guard in the model shows as a disagreement.

**Signed payloads.** What `execute_signed_intent` tests before the intents run, except the
signature, is decided by the model's `Intents.admit`: `verifying_contract` equals the contract,
the `deadline` is not before the block time `ts`, the `public_key` is a key of the signer
(`Intents.hasKey` on `world.keys`), the `nonce` was not committed by an earlier successful call
of the replay (`Intents.commitNonce`), the signer is not locked. `admitPayload` in `Main.lean`
only builds the `Payload` and the state the question is put on: a deadline is read in the form
`YYYY-MM-DDTHH:MM:SS[.f]Z`; without `ts`, or with a deadline of another form, the deadline is set
to the block time (not expired); in a trace without `world.keys`, or for a payload without a
`public_key` field, the key is put into the table first (not tested). The signature itself is
not checked. The key table starts as `world.keys` and follows the receipts of `add_public_key`
and `remove_public_key`. Implicit keys: the traces register every key explicitly for a named
account, so the replay gives the model an `implicit` function that maps a key to a string that is
no account id (`replayImplicit`); the implicit half of `hasKey` and the implicit branches of
`addKey` / `removeKey` are not exercised by the replay.

The argument decoding, account-id and token-id syntax, the shape test of signed payloads, the
loop of `mt_resolve_withdraw`, the eleven guarded methods outside the ledger, and the dispatch
above live in `Main.lean` and are **not** part of the proved model. The refund of
`mt_resolve_transfer`, the entry guard of `mt_transfer*`, the admission of a signed payload and
the rules of the role table were such code before; they are functions of `Intents/Auth.lean`
now, the same ones the strict world (`Intents/Strict.lean`) and its theorems use. The NEP-245 rows and `execute_intents`
are covered by no theorem; they are here to compare the ledger arithmetic with the wasm.

## Verdict per receipt

* `agree` — the model's success/failure equals `ok`, the model's observable state equals the
  trace's `state` (below), and, where the model computes a return value, it equals `ret.json`.
* `DISAGREE` — otherwise. The model's own state is printed in an extra record
  (`"verdict": "model-state-before-resync"`), then the replay continues from the trace's state.

Three verdicts mean that the outcome was not compared; `why` says why, and the summary counts
them by reason (`not_compared`):

* `env` — the receipt failed for a reason the model does not decide: `gas: a failure forced by
  the harness` (`fault` set), `gas: ran out of the attached gas` (`OutOfGas`,
  `GasLimitExceeded`), `runtime: <status>` (any other status that is not a contract panic). What
  the model does say about such a receipt — that it changes nothing — is compared: a failed
  receipt after which the observable state differs is a `DISAGREE`.
* `auth` — the model accepts, the contract rejected a signed payload for a reason the replay does
  not decide, and nothing changed: `signature: not checked by the model` (status
  `invalid signature`), `signature level: salted nonce, outside the model`, and, for a trace
  without `ts` or without `world.keys`, `signature level: deadline, the trace has no block time`
  / `signature level: public key, the trace lists no keys`. A rejection for any other reason is
  a `DISAGREE`.
* `skip` — `outside the model: <what>`; the replay continues from the trace's state.

## Output

stdout, one line per trace:

```
{"id": 17, "mock": false,
 "steps": [ {"i": 32, "method": "ft_withdraw", "pred": "alice.near", "verdict": "agree",
             "why": "", "model_ok": true, "trace_ok": true, "wnear": false, "state": <observable state>} , … ],
 "summary": {"contract_steps": 71, "agree": 70, "disagree": 0, "skipped": 0, "env": 1, "auth": 0,
             "not_compared": {"gas: ran out of the attached gas": 1},
             "wnear": 18, "wnear_agree": 18, "wnear_disagree": 0, "unwrap_callbacks": 1}}
```

and a last line `{"total": {…}}` with the sums. With `--summary` the `steps` array is omitted.
Exit code 1 when any receipt disagrees.

`wnear` marks a receipt that involves wNEAR (`involvesWNear` in `Main.lean`), decided from its
inputs alone, so failed receipts count too: `ft_on_transfer` called by `wrap.near` or carrying
intents that touch `nep141:wrap.near`; `ft_withdraw`, `ft_force_withdraw`, `ft_resolve_withdraw`
with `token = wrap.near`; `execute_intents` with a `native_withdraw`, a `storage_deposit`, a
withdrawal of wNEAR, a withdrawal with `storage_deposit`, or a `transfer` of `nep141:wrap.near`;
`mt_transfer*` / `mt_resolve_transfer` of that id; `do_native_withdraw`, `do_storage_deposit`,
and `do_ft_withdraw` / `do_mt_withdraw` for wNEAR or with a storage deposit. `wnear_agree` and
`wnear_disagree` are their verdicts (the rest are `env` or `auth`); `unwrap_callbacks` counts
the callbacks after `near_withdraw` that the contract itself called.

The observable state, after the receipt, in the trace's own shape without `held`:

```
{"ledger": {"<token id>": {"<account>": "<amount>", …}, …},   nonzero entries, keys sorted
 "supply": {"<token id>": "<amount>", …},                     nonzero entries
 "paused": ["<feature key>", …],                              sorted
 "locked": ["<account>", …],                                  sorted, the accounts the harness reads
 "auth_off": ["<account>", …],                                sorted, the same accounts
 "acl": {"super_admins": ["<account>", …],                    sorted
         "admins": ["<Role>:<account>", …],                   sorted
         "grantees": ["<Role>:<account>", …]}}                sorted
```

Not part of the observable state, and carried by the replay itself: the registered keys, the
committed nonces, the fee, the fee collector and the relayer keys.

## The world-level replay (`--world`)

`intentsmodel --world` adds a second replay of every trace whose token is the standard one
(`mock == false`). It does not use the dispatch above. It keeps one `Intents.World` — the token
state of `ProvedFT`, the ledger of `nep141:<token>`, and the lists of receipts in flight — and
advances it with `Intents.stdStep`, the step function the theorems of `Intents/` are about, once
or several times per receipt. With it it keeps what the strict world adds (`Intents.SWorld`: the
transfer calls whose `mt_resolve_transfer` is in flight, the super-admins and the admins), and
runs the internal transfers and the `acl_*` calls through `Intents.sstep`, the step function of
the strict world:

| receipt | step |
|---|---|
| on the token, from any account but the contract | `tokCall` |
| the token's `ft_resolve_transfer` callback | `tokResolve i res` (`tokResolveFails i` when it ran out of gas); `res` is what a third-party receiver answered — for a transfer to the contract the world uses the contract's own answer |
| the contract's `ft_transfer` / `ft_transfer_call` (with `storage_deposit` in front) on the token | `tokXfer j` (`tokXferFails j`) |
| the contract's `storage_deposit` on the token | `meStorageDeposit` |
| a receipt on the token without a function call (NEAR arriving) | `tokNearIn` |
| `ft_on_transfer` called by the token | `onTransfer i recv ok` |
| `ft_withdraw`, `ft_force_withdraw` of the token; an `ft_withdraw` intent of a successful `execute_intents` | `ftWithdraw via w` |
| `do_ft_withdraw` after an unwrap | `doFtWithdraw j ok` |
| `ft_resolve_withdraw` of the token | `resolveWd k` (`resolveWdFails k`) |
| `mt_transfer*` of the token's ledger id in a successful receipt, per row | strict `transfer src dst amt call` (`call`: the `_call` methods) |
| `mt_force_*` of the token's ledger id in a successful receipt, per row | strict `forceTransfer who src dst amt call` |
| a `transfer` intent of a successful `execute_intents` | `Intents.runOp … (.move dst amt call)`, the function the strict `payload` step runs per intent (`call`: the intent has a `msg`; no trace has one) |
| `mt_resolve_transfer` with a row of the token's ledger id | strict `resolveTransfer k req` per such row (`resolveTransferFails k` when the receipt failed); `req` is the refund the receiver's answer asks for, the whole amount when the answer is unusable |
| a successful `acl_*` call | strict `acl c` |
| pause, unpause, lock, unlock, the auth switch | `admin a` |

`i`, `j`, `k` are positions in the world's in-flight lists. The replay finds them by receipt id:
every entry of `pend`, `unwrap`, `outbox`, `resolves` and of the strict world's `calls` is paired
with the `rid` of the receipt the wasm created for it (FORMAT.md, section 7a). For a transfer
call that is the `mt_resolve_transfer` among the receipts the transfer created. An
`mt_resolve_transfer` for which the model has no entry, or whose previous owner, receiver or
amount differ from the entry, is a disagreement; so is an entry that is still in flight after
its receipt ran, and an entry the model made for a transfer after which the wasm created no
`mt_resolve_transfer`.

What the trace supplies is what the world leaves open: the caller, the method and its
arguments, the answer of a third-party receiver, whether a receipt failed for gas, and — for a
receipt whose success depends on other ledger ids or on signatures (`execute_intents`, a
transfer of several ids) — whether it succeeded. What a callback of the contract reads is *not*
taken from the trace: `ft_resolve_withdraw` reads what the token model returned, and the replay
checks that it is byte for byte what the receipt read.

Compared after every receipt on the token or on the contract that belongs to this world: its
success where the world decides it; the balances and the supply of `nep141:<token>`; the paused
keys, locked accounts and auth flags; the token balance of the contract; the token balance of
every watched account and the token's supply; the role table (super-admins, admins of a role,
grantees), which the model advances by `aclStep` — before, the world-level replay copied the
grantees from the trace after every `acl_*` call.

Not run by the world-level replay, although part of the strict world: the `payload` step as a
whole (the intents of a successful call are applied one by one; what is tested of a payload is
compared in the receipt replay, through `admit`), the steps `addKey` / `removeKey` (the
world-level replay does not follow keys; the receipt replay runs their functions and asks
`sstep` for their auth-flag guard), and `Step.free` (the other receipts go through
`Intents.stdStep` directly). Whether an internal transfer succeeds is not decided here either
(it depends on the rows of other ledger ids); the receipt replay decides it.

Not in this world: receipts of the contract about other ledger ids (counted as
`contract_receipts_of_other_ledger_ids`), and the whole wNEAR side — `IntentsW.step` is not run
by any replay; only its two ledger functions are, in the receipt replay. The token's NEAR balance
is not in the traces: the token model runs with parameters under which its NEAR conditions hold
(no storage stake, a balance and a cap no trace approaches).

Output: `"world"` next to `"summary"` in every line, and in the last line next to `"total"`:

```
"world": {"traces": 1, "mock_traces_left_out": 0, "token_receipts": 19, "contract_receipts": 31,
          "contract_receipts_of_other_ledger_ids": 40, "agree": 49, "disagree": 0, "env": 1}
```

`env`: receipts that failed for gas, after which the world state still equals the trace.
`world_disagreements` lists the first five disagreements of a trace with the reason. Exit code 1
when either replay disagrees.

`held` (the token contract's balance of the contract) is the token's side and is not printed:
the replay is of the contract alone, with the token as the environment the trace recorded.
