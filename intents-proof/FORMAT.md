# Trace format of the intents harness

Written by `harness/target/release/intents-gen traces …`, read by `harness/scripts/monitor.py`
and replayed through the Lean model (`lean/Main.lean`, `scripts/conformance.sh`). It follows the conventions of the token-standard kit
(`id`, `init`, `ops`, `steps`, `obs`, `settled`; amounts as decimal strings; `ret`, `calls`).

A trace file is JSON Lines: **one line is one trace**. A trace holds **one record per executed
receipt** (`steps`) and the views after every block (`obs`).

All amounts are decimal strings (they exceed 2^64, and on the ledger id of the scripted token they
reach 2^128 − 1). Account ids and token ids are strings.
Ledger token ids are the contract's own: `nep141:<token account>` and
`nep245:<token account>:<token id inside it>`.

## 1. What is fixed before a trace starts (not in the trace)

Every trace starts from the same world, built once and cloned:

| account | what it is |
|---|---|
| `intents.near` | the contract under test: the wasm given on the command line, initialised with `new({"config": {"wnear_id": "wrap.near", "fees": {"fee": 0, "fee_collector": "admin.near"}, "roles": …}})` |
| `token.near` | reference NEP-141 token (near-contract-standards 5.29.0); in mock mode the fee-keeping mock |
| `wrap.near` | the wNEAR bytes |
| `mt.near` | a second deployment of the same intents wasm, used as the NEP-245 token contract |
| `owner.near`, `alice.near`, `bob.near`, `carol.near` | plain accounts, registered with both tokens and funded; each also has balances inside `mt.near` (`nep141:token.near`, `nep141:wrap.near`) |
| `recv1.near`, `recv2.near` | receiver contracts whose `ft_on_transfer` / `mt_on_transfer` answer is scripted per operation; registered and funded |
| `unreg.near` | an existing account registered with no token |
| `ghost.near` | no such account exists (it can still own ledger balances) |
| `evil.near` | a contract that makes a private method of `intents.near` the `promise_then` callback of its own promise (`f_<method>`: after a failing promise, `s_<method>`: after a promise that returns `"0"`) |
| `stub.near` | the scripted token: a stub contract that keeps no balances. Each operation chooses what its `ft_transfer`, `ft_transfer_call` and `storage_deposit` return; its method `mint` makes it call `intents.near::ft_on_transfer` with the arguments the operation chose (so it "deposits" any amount). Nothing backs its ledger id `nep141:stub.near` |
| `pauser.near` | holds `PauseManager` and `UnpauseManager` |
| `forcer.near` | holds `UnrestrictedWithdrawer` |
| `locker.near` | holds `UnrestrictedAccountLocker` and `UnrestrictedAccountUnlocker` |
| `dao.near` | holds `DAO` |
| `pause1.near`, `unpause1.near` | hold `PauseManager` only, `UnpauseManager` only |
| `lock1.near`, `unlock1.near` | hold `UnrestrictedAccountLocker` only, `UnrestrictedAccountUnlocker` only |
| `acctmgr.near` | holds `UnrestrictedAccountManager` |
| `fees1.near`, `relayer1.near`, `upgrader1.near`, `salt1.near`, `gc1.near` | hold one role each of those that guard nothing on the token paths: `FeesManager`, `RelayerKeysManager`, `Upgrader`, `SaltManager`, `GarbageCollector`. With `dao.near`, `forcer.near`, `pause1.near`, `unpause1.near`, `lock1.near`, `unlock1.near`, `acctmgr.near` every one of the twelve roles has an account that holds it and nothing else |
| `roleadmin.near` | admin (not grantee) of `PauseManager`, `UnrestrictedWithdrawer`, `UnrestrictedAccountLocker` |
| `admin.near` | super-admin (no role); grants and revokes in traces |
| `temp.near` | no permission at the start; the only account whose permissions change in a trace |

The role table at the start of a trace is `init.state.acl`. Roles are the same in `mt.near` and
do not change there. `intents.near` and `mt.near` are registered with both tokens.
Each of the four users has registered the ed25519 key it signs with in `intents.near`
(`add_public_key`), so that it can sign intents. The ledger of `intents.near` is empty at the
start of every trace.

## 2. The trace object

```
{ "id": 17, "seed": 20261112, "mock": false, "h0": 176,
  "world": {…}, "init": {…}, "ops": […], "steps": […], "obs": […],
  "settled": true, "refund_receipts": 147, "derive_errors": [] }
```

* `id`, `seed` — the trace is a function of (`seed`, `id`) and the wasm files.
* `mock` — `true` when `token.near` is the non-standard mock (section 7).
* `h0` — block height of the start state; the first receipts run at `h0 + 2`.
* `settled` — no transaction or receipt was left pending at the end.
* `refund_receipts` — number of the runtime's refund receipts (predecessor `system`: gas refunds
  and refunds of the deposit of a failed call). They move only NEAR and are **not listed** in `steps`.
* `derive_errors` — harness self-check, empty when the per-receipt states were derivable (section 5).
* A line `{"id", "seed", "mock", "sim_panic": "<message>"}` replaces a trace when the simulator
  itself stopped; such a line has no other fields.

### `world`

```
"world": {
  "contract": "intents.near",
  "assets":  [ {"ledger": "nep141:token.near", "contract": "token.near", "inner": null},
               {"ledger": "nep141:wrap.near",  "contract": "wrap.near",  "inner": null},
               {"ledger": "nep245:mt.near:nep141:token.near", "contract": "mt.near", "inner": "nep141:token.near"},
               {"ledger": "nep245:mt.near:nep141:wrap.near",  "contract": "mt.near", "inner": "nep141:wrap.near"} ],
  "ids":     [ the four asset ids, "nep141:alice.near", "nep141:bob.near", "nep245:alice.near:x", "nep141:stub.near" ],
  "holders": [ every account id that can own a ledger balance in a trace ],
  "private": [ "ft_resolve_withdraw", "ft_resolve_deposit", "do_ft_withdraw", "mt_resolve_withdraw",
               "mt_resolve_deposit", "mt_resolve_transfer", "do_mt_withdraw", "do_native_withdraw",
               "do_storage_deposit",
               "do_nft_withdraw", "nft_resolve_deposit", "nft_resolve_withdraw", "do_auth_call",
               "do_add_relayer_key", "state_migrate", "acl_init_super_admin" ],
  "scripted_token": "stub.near",
  "flag_watch": [ the nine accounts whose lock flag and auth-by-predecessor flag are read ],
  "roles":   {"pause": "pauser.near", "force_withdraw": "forcer.near", "lock": "locker.near", "super_admin": "admin.near",
              "dao": "dao.near", "pause_only": "pause1.near", "unpause_only": "unpause1.near", "lock_only": "lock1.near",
              "unlock_only": "unlock1.near", "account_manager": "acctmgr.near", "fees": "fees1.near",
              "relayer_keys": "relayer1.near", "upgrader": "upgrader1.near", "salts": "salt1.near",
              "garbage_collector": "gc1.near", "role_admin": "roleadmin.near", "no_role_at_start": "temp.near"},
  "keys":    {"owner.near": ["ed25519:…"], "alice.near": […], "bob.near": […], "carol.near": […]},
  "fees":    {"fee": 0, "fee_collector": "admin.near"} }
```

* `assets` — ledger token ids that a contract backs, and where the backing is read:
  `inner == null` → `<contract>::ft_balance_of(intents.near)`; otherwise
  `<contract>::mt_balance_of(intents.near, <inner>)`.
* `ids` — every ledger token id a trace can create. The three after the assets are created when a
  plain account calls `ft_on_transfer` / `mt_on_transfer` itself (the caller is the "token"), the
  last one by the scripted token; nothing backs them.
* `private` — the methods the wasm marks `#[private]`: the nine of the token paths, then seven
  more that are only ever called directly by other accounts.
* `roles` — a legend of who is who; the role table itself is `state.acl`.
* `keys` — the public keys each account registered in the contract (`add_public_key`) before the
  trace starts. Operations of kind `key` (the probe `keys`, below) add and remove keys during a
  trace; the trace does not record the key table again: a replay follows it from the successful
  receipts of `add_public_key` and `remove_public_key` (`pred` is the account, `args.public_key`
  the key).
* `fees` — the fee and the fee collector the contract was initialised with (`set_fee` and
  `set_fee_collector` fail when the value does not change).

### `state` (used in `init`, in every step and in every `obs` entry)

```
"state": {
  "ledger": { "<ledger token id>": { "<account>": "<amount>", … }, … },   // mt_balance_of, nonzero entries only
  "supply": { "<ledger token id>": "<amount>", … },                        // mt_supply, nonzero entries only
  "held":   { "<asset ledger id>": "<amount>", … },                        // the token contract's balance of intents.near, nonzero only
  "paused": [ "<feature key>", … ],                                        // pa_all_paused, sorted
  "locked": [ "<account>", … ],                                            // is_account_locked, sorted
  "auth_off": [ "<account>", … ],                                          // is_auth_by_predecessor_id_enabled is false, sorted
  "acl": { "super_admins": [ "<account>", … ],                             // acl_get_permissioned_accounts, sorted
           "admins":   { "<Role>": [ "<account>", … ], … },                // roles with no admin are left out
           "grantees": { "<Role>": [ "<account>", … ], … } } }             // roles with no grantee are left out
```

A missing key means zero (or "not paused" / "not locked" / "enabled"). `ledger` covers all
`world.ids` × `world.holders`. `locked` and `auth_off` are read for `world.flag_watch`: the four
users, the two receivers, `unreg.near`, `ghost.near` and `evil.near`; no operation switches
either flag of another account.

### `init`

`{"state": <state>, "tokens": [], "view_errors": [], "tokens_state": {…}}` — the views before the
first operation. `tokens_state` describes the two NEP-141 tokens at that moment (it is the same in
every trace of a run):

```
"tokens_state": { "token.near": { "supply": "<ft_total_supply>",
                                  "balances": { "<holder>": "<ft_balance_of>", … },   // every world.holders entry, zeros included
                                  "registered": [ "<holder>", … ] },                  // storage_balance_of is not null
                  "wrap.near":  { … } }
```

## 3. `ops`: what the generator submitted

One entry per signed transaction, in submission order:

```
{ "i": 20, "h": 189, "tx": "<hash>", "kind": "withdraw", "signer": "alice.near",
  "recv": "intents.near", "method": "ft_withdraw", "args": {…}, "deposit": "1",
  "gas_tgas": null, "label": "<one sentence>", "probe": null,
  "replies": [ {"stub": "recv1.near", "method": "ft_on_transfer", "does": "returns \"0\""} ],
  "faults":  [ "ft_resolve_withdraw held 2 blocks" ] }
```

* `h` — height when it was submitted; its first receipt runs at `h + 2`.
* `gas_tgas` — attached gas when the generator limited it; `null` means 300 Tgas.
* `probe` — `null` for a random operation; otherwise the name of the scripted sequence the
  operation belongs to (below).
* `replies` — what a scripted receiver, or the scripted token, does when this transaction's flow
  calls it (`stub`, `method`, and in `does` the bytes it returns or the call it makes).
* `faults` — delays (`held k blocks`: the receipt leaves k blocks late, later receipts overtake
  it) and forced failures (`runs out of gas`: the receipt fails with all its effects undone) that
  the simulator applies to receipts this transaction spawns. A non-empty list means outcomes of
  this operation were partly forced by the harness.
* `kind` — `deposit`, `donate`, `withdraw`, `force_withdraw`, `transfer`, `transfer_call`,
  `pause`, `unpause`, `lock`, `private_direct`, `private_callback`, `self_token`, `mt_deposit`,
  `mt_withdraw`, `mt_donate`, `intent`, `noise`, and since the extension: `stub_deposit` (the
  scripted token notifies a deposit), `force_transfer` (`mt_force_*`), `auth` (the
  auth-by-predecessor switch), `acl` (near-plugins `acl_*`), `key` (`add_public_key` /
  `remove_public_key` called by an account for itself), `guarded` (a role-guarded method
  outside the token paths: fees, salts, relayer keys, full-access keys, `cleanup_nonces`,
  `admin_call`, `upgrade` — called by accounts without the role and, except `upgrade`, by the
  holder of the role with arguments that change nothing in the ledger).

Probes. A trace contains zero, one or two of the eleven probes (25 % / 45 % / 30 %), each a scripted sequence
of operations in which one guard is the only reason a call fails; every operation of a probe runs
to its end before the next one is submitted. Operations submitted earlier may still be running.

| `probe` | what the sequence does |
|---|---|
| `auth_flag` | an account's auth-by-predecessor flag is switched off (by itself, by a role holder, or by its signed intent); it then calls `ft_withdraw`, `mt_transfer` and `disable_auth_by_predecessor_id`, its signed intent is relayed, an account without the role tries to switch the flag back, a right one (or a signed intent) does, and the account withdraws again |
| `intents_pause` | `intents` is paused; signed `ft_withdraw`, `transfer` and `native_withdraw` intents are relayed, the account withdraws by the method; unpause; a signed `ft_withdraw` again |
| `pause_roles` | a key (one of five feature keys, or `ALL`) is paused by the holder of `UnpauseManager` only, by an account without a pause role, by a right one; unpaused by the holder of `PauseManager` only, by a wrong account; the method the key guards and the same action as a signed intent are called; unpaused by a right one |
| `lock_roles` | an account is locked by the holder of the unlocker role only, by a wrong account, by a right one; the locked account withdraws, its signed `transfer`, `native_withdraw` and `set_auth_by_predecessor_id` intents are relayed, it calls `disable_auth_by_predecessor_id`; a forced withdrawal from it; unlock by the locker-only holder, a wrong account, a right one; it withdraws again |
| `forced` | `ft_force_withdraw` by two accounts without the role, by `dao.near`, by `forcer.near`; one of the four `mt_force_*` by an account without the role and by a right one |
| `grants` | `temp.near` calls a method a role guards; an account that may not grant the role tries to; the role reaches `temp.near` (granted by the super-admin, by an admin of the role, or by itself after it was made an admin of the role or a super-admin); it calls the method; an account that may not revoke tries to; the role is revoked or renounced; it calls the method again |
| `bounds` | the scripted token notifies deposits that bring the supply of its ledger id to 2^128 − 1 exactly, then one unit more, then the amount 2^128; an internal transfer of one unit more than a balance of that size and of the balance itself; a withdrawal whose refund would lift the supply over the bound (its callback is held back while a deposit fills the supply up); the holders withdraw |
| `role_sweep` | one of the 24 guarded methods is called, with well-formed arguments, by the holder of each of the twelve roles in turn and by an account with no role (for `upgrade` the two holders that could run it are left out: it would replace the code under test) |
| `keys` | an account adds its own key again (refused: it is there) and removes a key it does not have (refused); a payload of the account without intents, signed with the key of another account, is relayed before that key is added for the account (refused), after (accepted), and after it is removed again (refused); the account removes its own key (its payload is refused), adds it back (accepted); then either its auth-by-predecessor flag is switched off and it calls `add_public_key` and `remove_public_key` (both refused), or it is locked and calls both (refused) and its payload without intents is relayed (refused: the lock) |
| `edges` | an account moves an amount to `recv1.near`, then sends it a second amount with `mt_transfer_call`, and the receiver asks for more than that second amount back (the refund is capped by the amount, although the receiver holds more); a third `mt_transfer_call` whose `mt_resolve_transfer` is made to run out of gas (the receiver keeps what it was sent); `temp.near` is made an admin of a role, an account without the permission calls `acl_revoke_admin` for it, `temp.near` renounces the entry; the super-admin hands its role to `temp.near` with `acl_transfer_super_admin`, calls `acl_add_super_admin` (it may no longer), and `temp.near` hands the role back |
| `replies` | withdrawals of the scripted token, which answers `ft_transfer_call` with a number padded with JSON whitespace to exactly 43, 44, 45 or 46 bytes, with other bytes of exactly 44 or 45, with the largest `u128` written in 44 bytes, with more than the amount, with a leading `+`; and one plain `ft_transfer` that succeeds with a non-empty value |

An `intent` operation is `execute_intents({"signed": [...]})` sent by a relayer. Each element is
`{"standard": "raw_ed25519", "payload": "<JSON text>", "public_key": "ed25519:…", "signature": "ed25519:…"}`;
the signature is over the payload text, and the text is
`{"signer_id", "verifying_contract", "deadline", "nonce", "intents": [{"intent": "ft_withdraw" | "mt_withdraw" | "native_withdraw" | "storage_deposit" | "transfer" | "set_auth_by_predecessor_id", …}]}`.
Some payloads are wrong on purpose (another key, another verifying contract, a past deadline,
another `signer_id`, a payload sent twice, a signature made over another text). The payloads of
the probe `keys` have an empty list of intents: whether such a payload is accepted depends only
on what is tested before the intents run.

`ops` is context for a reader. Everything a replay needs is in `steps`.

## 4. `steps`: one record per executed receipt

In execution order (block by block, and inside a block in the order the runtime ran them).
All receipts are listed, whichever account they ran on, except the refund receipts of section 2.

```
{ "i": 32, "h": 191, "ts": "1600000191000000000", "rid": "<receipt id>", "tx": "<transaction hash>", "op": 20,
  "pred": "alice.near", "recv": "intents.near",
  "actions": ["FunctionCall"], "method": "ft_withdraw", "methods": ["ft_withdraw"],
  "args": {"token": "token.near", "receiver_id": "owner.near", "amount": "234…386"},
  "deposit": "1", "gas": 300000000000000, "gas_burnt": 4796082841990,
  "ok": true, "status": "ok", "ret": {"kind": "promise", "rid": "<receipt id>"},
  "callback": false, "results": [],
  "logs": ["EVENT_JSON:{…}"], "events": [ {"standard": "nep245", "event": "mt_burn", "data": […], …} ],
  "calls": [ {"rid": "…", "recv": "token.near", "actions": ["FunctionCall"], "method": "ft_transfer",
              "methods": ["ft_transfer"], "args": {…}, "deposit": "1", "gas": 279315613941204}, … ],
  "fault": null, "held_blocks": null,
  "moves": [ ["intents.near", "nep141:token.near", "alice.near", "-234…386"],
             ["intents.near", "nep141:token.near", null,         "-234…386"] ],
  "state": <state>, "state_src": "derived" }
```

| field | meaning |
|---|---|
| `i` | index in `steps` |
| `h` | block the receipt ran in |
| `ts` | the timestamp of that block in nanoseconds (what `env::block_timestamp()` returns in it), as a decimal string |
| `op` | index in `ops` of the transaction it descends from |
| `pred`, `recv` | predecessor account and the account it ran on |
| `actions` | nearcore action names; a call has `["FunctionCall"]` |
| `method` | the called method, `null` for a receipt without a function call |
| `methods` | all function calls of the receipt. Only a withdrawal with `storage_deposit` makes a receipt with two (`storage_deposit`, then the transfer, on the token); `method` and `args` are the first one's |
| `args` | the arguments **decoded** from JSON; `{"$raw": "<text>"}` when they are not JSON; `null` without a call |
| `deposit` | attached deposit in yoctoNEAR |
| `gas`, `gas_burnt` | attached gas and what the receipt burnt (gas units) |
| `ok` | `true`: the receipt succeeded (returned a value or a promise) |
| `status` | `"ok"`, or the failure as text: `Panic("<message>")` (the contract's own panic), `OutOfGas`, `GasLimitExceeded`, `AccountDoesNotExist(…)`, `Action(…)` for other failures outside the method's logic (`MethodNotFound`, `CodeDoesNotExist`, `NewReceiptValidationError(… FunctionCallZeroAttachedGas)` when a created call would get no gas), `Host(…)` |
| `ret` | `{"kind": "none"}` (empty return value), `{"kind": "value", "json": <decoded>}`, `{"kind": "bytes", "hex": …}` (not JSON), `{"kind": "promise", "rid": <receipt whose result becomes this receipt's result>}`; `null` when the receipt failed |
| `callback` | the receipt waited on promise results |
| `results` | the promise results it read, in index order: `{"ok": true, "hex": "<bytes>", "json": <decoded, if JSON>, "from": <rid>}` or `{"ok": false, "from": <rid>}`. `from` is the receipt that produced the final value (a receipt that returned a promise passes its slot on). An empty successful result has `"hex": ""` and no `json` |
| `logs`, `events` | the logs, and the decoded `EVENT_JSON:` ones. A failed receipt's logs are still listed; its effects are not applied |
| `calls` | the receipts this one created, refunds excluded: function calls and plain transfers, in creation order |
| `fault` | the fault the harness forced on this receipt (`OutOfGas`), else `null` |
| `held_blocks` | how many blocks late a forced delay sent it, else `null` |
| `moves` | balance changes **of this receipt**, each measured by the simulator with the views just before and just after the receipt: `[contract, token id or null, holder or null, signed amount]`. `holder == null` is the total supply. Contracts measured: `intents.near` (all `world.ids`: `mt_balance_of` of every holder, `mt_supply`), `token.near` and `wrap.near` (`ft_balance_of` of every account, `ft_total_supply`), `mt.near` (its two inner ids). Zero changes are not listed. A change can be as large as 2^128 − 1 in either direction |
| `state` | the observable state **after this receipt** (section 5) |
| `state_src` | `"views"`: this is the last receipt of its block and `state` is what the views returned after the block; `"derived"`: an earlier receipt of a block, see below |

## 5. How `state` after a receipt is obtained

Views can be called between blocks; several receipts can run in one block. For the last receipt
of a block `state` is the views' answer after that block. For an earlier receipt it is the
previous state plus this receipt's `moves` (ledger, supply, held — these are view measurements
taken by the simulator around the receipt itself) and, for `paused`, `locked`, `auth_off` and
`acl`, the receipt's own events when it succeeded: `Pausable` `pause` / `unpause`,
`account_locked` / `account_unlocked`, `set_auth_by_predecessor_id`, and the six
`AccessControllable` events (`role_granted`, `role_revoked`, `admin_added`, `admin_revoked`,
`super_admin_added`, `super_admin_revoked`).

The harness checks the derivation at every block: the state derived through all receipts of the
block must equal the views after the block. A difference is recorded as `derive_mismatch` in that
block's `obs` entry (and the views win). In all runs so far there was none.

## 6. `obs`: the views after every block

```
{ "h": 193, "ts": "1600000193000000000", "state": <state>, "tokens": ["nep141:token.near", …], "pending_ops": [19, 22] }
```

* `tokens` — every ledger token id the contract enumerates (`mt_tokens`).
* `pending_ops` — operations that still have a receipt waiting (refund receipts not counted).
  Empty means the block ends in a quiescent state.
* optional `view_errors`, `derive_mismatch` — harness self-checks.

There is one entry per block from `h0 + 1` to the end; blocks in which no receipt ran are included.

## 7. Replaying a trace through a model of `intents.near`

(`intentsmodel` has a second mode that also replays the steps on the token, section 7a.)

Start from the empty ledger (`init.state`). Walk `steps` in order. For a step with
`recv == "intents.near"` and a `method`:

* inputs: `pred`, `method`, `args`, `deposit`, `results` (for a callback), and the state before
  it (the previous step's `state`; `init.state` before the first);
* expected: `ok`; for `ok == true` the return value `ret`, the created `calls`
  (`recv`, `method`, `args`, `deposit`), the `events`, and `state.ledger`, `state.supply`,
  `state.paused`, `state.locked`, `state.auth_off`, `state.acl` after it; for `ok == false` no
  change of those six.

Steps on other accounts are the environment: only they change `state.held`, and their results
reach the contract through `results` of its callbacks. Gas is recorded but a model that ignores
gas must treat a step with `status` `OutOfGas` / `GasLimitExceeded`, or with a non-null `fault`,
as an environment-chosen failure of that receipt.

Things a replay must know:

* `execute_intents` carries signed payloads: `args.signed[i].payload` is JSON text. A model that
  does not check signatures can take `ok` of the step as given and replay the intents of the
  payloads when `ok == true` (the call is atomic: one failing payload fails the whole call).
  An intent `ft_withdraw` / `mt_withdraw` with `storage_deposit`, `native_withdraw` and
  `storage_deposit` also debit the signer's `nep141:wrap.near` balance and make the contract call
  `wrap.near::near_withdraw`; the callbacks `do_ft_withdraw`, `do_mt_withdraw`,
  `do_native_withdraw`, `do_storage_deposit` then run as real callbacks (`pred == recv`).

* What `execute_intents` tests of a payload besides its signature can be decided from the trace:
  the verifying contract, the deadline against the step's `ts`, the public key against
  `world.keys` as changed by the successful `add_public_key` / `remove_public_key` receipts before
  it, the nonce against the payloads of earlier successful calls. A payload "signed
  over another text" has an invalid signature; nothing else in a trace does.
* The near-plugins `acl_*` methods do not fail for a caller without the permission: they return
  `null` (`ret` is `{"kind": "value", "json": null}`) and change nothing.
* A direct call of `ft_on_transfer` / `mt_on_transfer` by a plain account is legal: the caller is
  taken as the token (`nep141:<pred>`, `nep245:<pred>:<id>`). The scripted token `stub.near` is
  such a caller; what it returns to the contract's `ft_transfer` / `ft_transfer_call` is in
  `results` of the `ft_resolve_withdraw` step.
* Steps with `recv == "mt.near"` belong to the second deployment and are environment, although
  they run the same wasm. `mt.near` calls `intents.near::mt_on_transfer` (NEP-245 deposits);
  `token.near` and `wrap.near` call `intents.near::ft_on_transfer`.
* `state.held` is absent from the contract's own state; it is the token side.
* Mock traces (`"mock": true`) use a token that breaks NEP-141 on purpose. The contract's
  receipts in them are still real executions and can be replayed; the backing relation is
  expected to fail there.

## 7a. Replaying a trace through a model of the token and the contract together

The steps with `recv` equal to the token (`world.assets[0].contract`) can be replayed too, in one
state with the contract's steps. What is needed besides section 7:

* the token before the first step: `init.tokens_state` (balances, registered accounts, supply);
* which receipt a later receipt belongs to. `calls` of a step lists the receipts it created with
  their `rid`; a callback's `results[k].from` is the receipt that produced what it read. So the
  settlement callback `ft_resolve_transfer` of a transfer, the `ft_on_transfer` it waits for, the
  token receipt of a withdrawal and its `ft_resolve_withdraw` can each be found by `rid`;
* what to compare the token with: the token balance of every watched account and the token's
  supply after a step are the values of `init.tokens_state` plus the `moves` of the steps so far
  with the token as their first entry; `state.held` is the token balance of the contract.

The token's NEAR balance is not recorded.

## 8. Files

* `harness/results/sample/trace-<id>.json` — sample traces (one trace per file, same object).
* `harness/results/summary.json` — counts of the main run.
* `harness/scripts/show.py <file> <id> [op]` — prints a trace for reading.

## 9. Changes since the first version of this file

* `init.tokens_state` added (section 2).
* `methods` added to steps and to `calls` entries (section 4).
* operations of kind `intent` added: `execute_intents` with signed payloads (sections 3 and 7);
  the pause key `intents` is among the keys the generator pauses.
* 2026-11-13, access control and bounds: `state.auth_off` and `state.acl`; `ts` in steps and in
  `obs`; `probe` in `ops`; `world.scripted_token`, `world.flag_watch`, `world.keys`, `world.fees`,
  more entries in `world.roles` and `world.private`; the account `stub.near` and thirteen new role
  accounts; the
  operation kinds `stub_deposit`, `force_transfer`, `auth`, `acl`, `guarded`; the intent
  `set_auth_by_predecessor_id`; amounts and `moves` up to 2^128 − 1 (a change larger than
  2^127 used to be written as `"out-of-range"`). A reader of the earlier format still works on
  the new one if it ignores unknown fields; `intentsmodel` reads both.
* 2026-11-13, keys and edges: the probes `keys` and `edges` and the operation kind `key`
  (section 3). No field was added. What changed for a reader: the key table is no longer constant
  during a trace (`world.keys` is its start), payloads without intents occur, and an
  `mt_resolve_transfer` receipt can carry a forced failure (`fault`).
