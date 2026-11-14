# Harness for the deposit and withdrawal paths of `intents.near`

Runs the code deployed as `intents.near` on NEAR mainnet inside near-contract-sim (nearcore's own
runtime, in process), drives its token deposit and withdrawal paths and its role-guarded entry
points with random multi-account traces and checks on every trace that the internal ledger never
credits more tokens than the token contracts hold for the contract, and that no guarded method
runs for an account without the role. Read-only towards the chain: one `view_code` RPC query
fetches the wasm; nothing is signed or sent to any network.

Trace format: `../FORMAT.md`. Current numbers: `../README.md` and `../evidence/`.

## What each statement rests on

| statement | level of evidence |
|---|---|
| the wasm under test is the deployed one | hash check: sha256 of the fetched bytes in base58 is `BtA1BEFNS619KkvXFsgcpQ21Tb5yMm32aaUkn7xNothk`; the simulator reports the same code hash |
| it runs on the simulator unmodified | executed (init, views, every path below) |
| the relations of "Monitors" hold | held on every receipt of the N traces of the main run; a random search, not a proof |
| the monitors can fire | executed: the mock token run and `scripts/selftest.py` |

## Layout

```
fetch-wasm.sh          read-only fetch of the deployed code + hash check          -> wasm/intents.wasm
build.sh               builds the generator (needs libclang at build time)        -> target/release/intents-gen
build-mock.sh          builds the mock token from mock-token/                     -> wasm/mock_fee_token.wasm
run.sh                 main run + mock run + monitor self-test                    -> results/
src/main.rs            world, random operations, trace writer
scripts/monitor.py     the monitors (no model of the contract inside)
scripts/selftest.py    doctors clean traces, checks that every monitor reports
scripts/show.py        prints a trace for reading
wasm/ft.wasm           reference NEP-141 token (near-contract-standards 5.29.0)
wasm/w_near.wasm       the wNEAR bytes
mock-token/            the fee-keeping mock (not NEP-141), source
wasm/mock_reply_token.wasm  the reply mock (a standard transfer, a malformed reply for some amounts), derived from mock-token/ by ../scripts/mk_reply_mock.py
src-ref/intents/       near/intents at 16d04f6e, for reading (a local clone, not kept in this repository)
results/               summary.json, sample/, mock/, selftest.log, probe.json, wasm.sha256
```

## Running

```
./fetch-wasm.sh                 # once
./build.sh && ./build-mock.sh   # once
TRACES=4000 MOCK_TRACES=400 SEED=20261112 JOBS=16 ./run.sh
python3 -I scripts/show.py results/sample/trace-1.json 1        # read one trace
./target/release/intents-gen traces wasm/intents.wasm wasm/ft.wasm wasm/w_near.wasm 20261112 17 1 > t.jsonl   # regenerate trace 17
```

A trace is a function of (seed, id) and the wasm files. The simulator is the public
`near/near-contract-sim` at commit `8e4b69b` (nearcore 2.14.0), pinned in `Cargo.lock`.

## The world

`intents.near` (the wasm under test, initialised with `new` as the repository's tests do),
`token.near` (reference NEP-141), `wrap.near` (wNEAR bytes), `mt.near` (a second deployment of
the same wasm, used as the NEP-245 token contract), `stub.near` (a scripted token: it keeps no
balances, every operation chooses what its `ft_transfer` / `ft_transfer_call` return, and it
notifies deposits of any amount), four users, two receiver contracts with scripted answers, an
account registered with no token, an account that does not exist, and a contract that tries to
run the private callbacks as callbacks of its own promises.

Roles: `dao.near` (`DAO`); `pauser.near` (`PauseManager` + `UnpauseManager`), `pause1.near` and
`unpause1.near` (one of the two each); `forcer.near` (`UnrestrictedWithdrawer`); `locker.near`
(locker + unlocker), `lock1.near`, `unlock1.near` (one each); `acctmgr.near`
(`UnrestrictedAccountManager`); `fees1.near`, `relayer1.near`, `upgrader1.near`, `salt1.near`,
`gc1.near` (one each of the five roles that guard nothing on the token paths) — so each of the
twelve roles has a holder with that role alone; `roleadmin.near` (admin, not grantee, of three roles); `admin.near` (super-admin, no
role); `temp.near` (nothing at the start — the only account whose permissions change in a
trace). Details: FORMAT.md section 1.

## What the generator covers

* Deposits by `ft_transfer_call` of both tokens: empty `msg`, another account as plain text or
  JSON, `execute_intents: []` with and without `refund_if_fails`, malformed messages, zero and
  excessive amounts, attached deposit 0 / 1 / 2, gas limits.
* Tokens sent with a plain `ft_transfer` / `mt_transfer` (no notification).
* Withdrawals `ft_withdraw` by `ft_transfer` and by `ft_transfer_call` to: registered accounts,
  an account not registered with the token, a missing account, the contract itself, receivers
  that keep everything, return everything, return a part, return more than they got, return
  garbage or a number, panic, pad the answer to the size limit, and receivers that first send
  the tokens on, deposit them back, withdraw as themselves or call a private callback.
* Role-guarded entry points — `ft_force_withdraw`, `mt_force_withdraw`, `nft_force_withdraw`, the
  four `mt_force_*` transfers, `pa_pause_feature` / `pa_unpause_feature`, `force_lock_account` /
  `force_unlock_account`, `force_disable_auth_by_predecessor_ids` /
  `force_enable_auth_by_predecessor_ids` — each called by a holder of every role that suffices
  (the specific role, `DAO`, the account manager where it counts), by holders of the neighbouring
  role only (unpauser for a pause, unlocker for a lock, …), by holders of unrelated roles, by an
  admin of the role that is no grantee, by the super-admin, and by accounts with no role.
* The eleven guarded methods outside the token paths (`upgrade`, `admin_call`, `set_fee`,
  `set_fee_collector`, `add_full_access_key`, `delete_key`, `add_relayer_key`,
  `delete_relayer_key`, `cleanup_nonces`, `update_current_salt`, `invalidate_salts`): by accounts
  that hold none of the required roles and by the holder of the role, with arguments that leave
  the ledger alone (empty lists for `admin_call`, `cleanup_nonces`, `invalidate_salts`). The one
  exception is `upgrade`: no holder of `DAO` or `Upgrader` calls it, because it would replace
  the code under test.
* Role grants: the nine near-plugins `acl_*` methods that change the role table, by the
  super-admin, by an admin of the role, and by accounts that are neither; a role reaches
  `temp.near`, is used and is taken away again.
* The auth-by-predecessor switch: `disable_auth_by_predecessor_id`, the forced variants, the
  `set_auth_by_predecessor_id` intent; withdrawals and transfers by an account whose flag is off.
* The scripted token: answers to `ft_transfer_call` of exactly 43, 44, 45 and 46 bytes (a number
  padded with JSON whitespace, other bytes, the largest `u128`), a reported amount above the
  amount, a leading `+`; a plain `ft_transfer` that succeeds with a non-empty value; panics.
* Amounts at the `u128` bounds, on the ledger id of the scripted token: deposits that bring a
  supply to 2^128 − 1 exactly and one unit beyond, the amount 2^128 as an argument, transfers and
  withdrawals of balances of that size, a withdrawal refund that would overflow the supply.
  The simulator measures a balance change as a sign and a `u128`, so nothing had to be left out.
* Eleven probes (FORMAT.md section 3; the last two, `keys` and `edges`, were added for the public keys of
  an account and for the edges of transfer calls and of the role table; `edges` makes one
  `mt_resolve_transfer` run out of gas on purpose, which the monitor counts under `own_callback_failed`
  as "fault injected"): scripted sequences in which one guard is the only reason a
  call fails — the auth flag, the pause of `intents`, who may pause, who may lock, forced
  operations, a role granted and revoked, the `u128` bounds, the token's answers — and a sweep
  in which one guarded method is called by the holder of each of the twelve roles and by an
  account with none.
* NEP-245: deposits `mt_transfer_call` / `mt_batch_transfer_call` from `mt.near`, withdrawals
  `mt_withdraw` by `mt_batch_transfer` and `mt_batch_transfer_call`, forced ones.
* Inside the ledger: `mt_transfer`, `mt_batch_transfer`, `mt_transfer_call` with scripted
  `mt_on_transfer` answers.
* Signed intents through `execute_intents` (standard `raw_ed25519`): `ft_withdraw` (with and
  without `msg`, `storage_deposit`, `min_gas`), `mt_withdraw`, `native_withdraw`,
  `storage_deposit`, `transfer`, `set_auth_by_predecessor_id`; wrong key, wrong verifying
  contract, past deadline, another signer id, replayed payload, a signature over another text;
  intents relayed while `intents` is paused and for a locked signer.
* Interleaving: bursts of operations in one block, 0–5 blocks between operations, receipts held
  back 1–4 blocks (the notification, the token call, the token's settlement, the contract's
  callback), so that other deposits and withdrawals land between a debit and its callback.
* Forced failures of token-side receipts (they fail with all effects undone).
* Strangers calling the nine private methods directly, from a contract, and as the callback of a
  failing or succeeding promise of their own; the seven other private methods directly.
* Pause / unpause of every relevant feature key and of `ALL`; lock / unlock of ledger accounts
  (also of the contract's own account inside `mt.near`).
* Accounts that are no tokens calling `ft_on_transfer` / `mt_on_transfer` themselves.

## What it does not cover

NEP-171 (NFT) paths (`nft_force_withdraw` is called, but nobody holds an NFT); the `token_diff`,
`auth_call` and key-management intents; `add_public_key` / `remove_public_key` during a trace;
deposits whose `msg` carries real signed intents; signature standards other than `raw_ed25519`;
salted (versioned) nonces; an authorised `upgrade`; `admin_call` with promises, `cleanup_nonces`
with nonces and `invalidate_salts` with salts (their authorised calls carry empty lists); a role
table of `mt.near`
that changes; a super-admin that gives its own permission away; tokens other than the contracts
above; the contract's own NEAR balance (NEAR left in the contract after a failed
`storage_deposit` or native transfer is not tracked); storage growth over long histories; more
than one shard, congestion, and real block timing (the simulator runs one shard). Gas exhaustion
is covered only as attached-gas limits on the entry call and forced failures of token receipts.

## Monitors

Per backed asset `a` (a ledger token id whose tokens another contract holds: `nep141:token.near`,
`nep141:wrap.near`, `nep245:mt.near:nep141:token.near`, `nep245:mt.near:nep141:wrap.near`):

* `L(a)` — sum over all accounts of `mt_balance_of`;
* `S(a)` — `mt_supply`;
* `H(a)` — the token contract's balance of `intents.near`;
* `U(a)` — tokens that reached the contract with no deposit notification: every change of `H`
  made by a token receipt that is neither a `*_transfer_call` naming the contract as receiver,
  nor the token's own `*_resolve_transfer`, nor a call made by the contract itself;
* `G(a)` — what finished transactions left in the contract without a ledger owner (each one is
  reported as `tx_stranded`).

The backing monitor checks three relations:

1. **after every receipt:** `L(a) <= H(a) - U(a)` (`overcredit`);
2. **for every finished transaction:** `dL(a) = dH(a) - dU(a)`, over the changes its own receipts
   made (`tx_overcredit` when the left side is larger, `tx_stranded` when it is smaller);
3. **in every block with no receipt pending:** `L(a) = H(a) - U(a) - G(a)` (`quiescent_gap`).

Why these. The claim is that every ledger unit is backed by a token unit the token contract
attributes to `intents.near`. `U` is subtracted so that a donation cannot hide an over-credit of
the same size. While flows are pending, `H - U - L` is exactly the value in flight: a deposit the
token already moved but the contract has not credited (or the token has not refunded) yet, a
withdrawal already debited but not yet delivered or refunded, a return that reached the contract
but is not re-credited yet. Each of these is non-negative, so the inequality is the relation that
must hold at every point, and the monitor needs no knowledge of which flows are pending. The
equality must come back when nothing is pending; relation 2 says which transaction a difference
belongs to, relation 3 catches a difference that belongs to none.

`L`, `S`, `H` come from views: after every block directly, and for every receipt inside a block
from the balance changes the simulator measures with the same views just before and just after
that receipt (FORMAT.md section 5). The derived states are compared with the views at every
block; a difference would be reported as `derive_mismatch`.

Other monitors: `supply_mismatch` (`L = S` for every ledger id, after every receipt),
`withdraw_inexact` (a finished withdrawal without nested calls lowers the owner's ledger balance by
exactly what left the holdings), `private_ran` (a private method called by another account fails
and changes nothing), `failed_changed` (a failed receipt changes no measured balance),
`own_callback_failed`, `ran_while_paused`, `locked_spent`, `holdings_taken`,
`unknown_ledger_token`. `monitor.py`'s header has the exact wording.

Access control, also without a model of the contract:

* `unauthorized_ran` — a role-guarded method called by an account that holds none of the required
  roles must fail and change no balance, pause, lock, auth flag or role; a near-plugins `acl_*`
  method called by an account that is neither a super-admin nor (for the four methods where that
  suffices) an admin of the role must answer `null`, emit no event and leave the role table as it
  was. Who holds what is read from the role table before the receipt (`state.acl`, a view). Which
  roles a method requires is the table `ROLES` in `monitor.py`, taken from the source at
  `16d04f6ec4401263f8914638710260da50bb46b0` with file and line: the 22 exported methods that
  carry `#[access_control_any(roles(…))]` and the two of `#[pausable(…)]`, 24 in all. The source
  has two more guarded methods behind the feature `far`; the deployed wasm does not export them.
* `auth_off_ran` — a method that authenticates its predecessor (`ft_withdraw`, `mt_withdraw`,
  `mt_transfer*`, …) must fail for an account whose auth-by-predecessor flag is off.

## Results of a run of 1 000 traces (seed 20261112, 2026-11-13, the generator with nine probes)

Summary of this run: `../evidence/monitors_summary_1000.json` (`results/` holds the last run made). This is the
run described in detail. It was made before the probes `keys` and `edges` were added, so the present generator
gives other counts for the same seed: `../evidence/check_run.txt` is its run of 1 000 traces, and the paragraph on
4 000 traces below is of the present generator.

1 000 traces, 57 480 operations (9 513 of them in probes), 115 310 receipts (130 894 refund
receipts of the runtime not listed), 96 134 blocks observed.

* `overcredit`: 0 in 461 240 checks (receipt × backed asset). `tx_overcredit`: 0.
  `quiescent_gap`: 0 in 108 356 checks. `supply_mismatch`: 0.
* `unauthorized_ran`: 0 in 5 908 calls by accounts without the permission (table below).
  `auth_off_ran`: 0 in 483 calls by accounts whose auth-by-predecessor flag was off.
* `private_ran`: 0 in 3 426 attempts. `failed_changed`: 0. `ran_while_paused`: 0 in 668 calls of
  paused entry points. `locked_spent`: 0 in 358 attempts. `holdings_taken`: 0.
* `tx_stranded`: 446 (423 after a failed `*_transfer_call` of the contract, 23 after a failed wNEAR unwrap) and `withdraw_inexact`: 274. A withdrawal with `msg` whose
  `ft_transfer_call` receipt failed as a whole keeps its debit on purpose (the source says why: the token's
  `ft_resolve_transfer` may have failed after the transfer went through), so the tokens stay in the contract assigned
  to nobody. `own_callback_failed`: 81 — 25 under injected failures of the wNEAR unwrap, where the wNEAR debit is
  kept as well, and 56 where `ft_resolve_withdraw` of the scripted token panics because the refund would lift the
  supply of that ledger id over 2^128 − 1, and the refund is lost (55 in the `bounds` probe and 1 in random operations). That needs a ledger supply
  next to the `u128` bound, which a token whose holdings back the ledger cannot reach. None of these is a ledger
  total above the holdings.
* Simulator and harness failures (panic, unsettled trace, derivation mismatch, view error): 0.

Calls of guarded methods by the class of the caller, succeeded / failed (a caller with a required
role fails for other reasons: no balance, a wrong deposit, a value that does not change, a paused feature):

| methods | holds a required role | holds other roles only | admin of a required role, no grantee | super-admin, no role | no role |
|---|---|---|---|---|---|
| `pa_pause_feature`, `pa_unpause_feature` | 2 352 / 28 | 0 / 833 | 0 / 25 | 0 / 49 | 0 / 293 |
| `force_lock_account`, `force_unlock_account` | 925 / 35 | 0 / 619 | 0 / 13 | 0 / 31 | 0 / 211 |
| `force_disable_…` / `force_enable_auth_by_predecessor_ids` | 1 225 / 31 | 0 / 503 | 0 / 9 | 0 / 33 | 0 / 147 |
| `ft_force_withdraw`, `mt_force_withdraw`, `nft_force_withdraw` | 630 / 356 | 0 / 565 | 0 / 30 | 0 / 34 | 0 / 154 |
| the four `mt_force_*` transfers | 386 / 360 | 0 / 494 | 0 / 30 | 0 / 26 | 0 / 88 |
| the eleven guarded methods outside the token paths | 268 / 55 | 0 / 658 | 0 / 0 | 0 / 31 | 0 / 137 |
| all | 5 786 / 865 | 0 / 3 672 | 0 / 107 | 0 / 204 | 0 / 1 030 |

Of the 5 013 calls in the four right-hand columns, 4 990 were rejected with the role check's own message
("Insufficient permissions …"); the other 23 failed earlier (a deposit attached to a method that takes none).
The `acl_*` methods: 566 calls by an account that may change the role table (553 succeeded), 895 by an
account that may not — 858 answered `null` and changed nothing, 37 failed (an unknown role name, a deposit).
In this run every one of the 24 guarded methods was called by a holder of each of the twelve roles and by an account with no role, with the one exception named above: `upgrade` by `DAO` and by `Upgrader`. The summary has both tables per method (`guarded_calls`,
`guarded_calls_by_role_of_the_caller`).

The token's answers read by `ft_resolve_withdraw`: to `ft_transfer_call` — 1 738 of at most 42 bytes, 60 of
exactly 43, 187 of 44, 124 of 45, 61 of 46, 0 longer, 459 failed; 148 reported more than the
amount. To `ft_transfer` — 3 142 successes with no value, 220 successes with a value, 863 failures.
428 receipts moved 2^127 or more of a ledger id; a supply reached 2^128 − 1 in 218 receipts.

Deposits credited: 13 744 notified by the tokens and 2 800 notified by callers that are no token (the scripted
token among them); rejected and refunded by the token 1 053. Withdrawals through the entry points of backed
ids: delivered 2 116, transfer failed and refunded 606, `*_transfer_call` accepted in full 287, in part
255, returned in full 919, failed 274; of ids nothing backs 1 543; 1 906 had other ledger changes between the
debit and the callback. Signed intents executed: `ft_withdraw` 1 619, `mt_withdraw` 424, `native_withdraw` 176,
`storage_deposit` 154, `transfer` 586, `set_auth_by_predecessor_id` 131. Twelve sample traces of the last
run: `results/sample/`.

The monitor on code that lacks a role check: a wasm built from the same source with the
`#[access_control_any(…)]` attribute removed from `mt_force_transfer` and `mt_force_batch_transfer`, 200 traces
of the same generator — `unauthorized_ran` fired 49 times, on the receipts where an account without the role made
a well-formed call (`../evidence/unauthorized_ran_on_a_variant.json`). With the attribute removed from
`mt_force_transfer` alone nothing changes: that method delegates to `mt_force_batch_transfer`, which tests the role
itself (29 such calls, none ran). On the deployed wasm the monitor fired on none.

The same with 4 000 traces and 400 of the mock, by the present generator with eleven probes
(`TRACES=4000 MOCK_TRACES=400 ../check.sh`, summary in `../evidence/monitors_summary.json`): 463 687 receipts,
`overcredit` 0 in 1 854 748 checks, `quiescent_gap` 0 in 445 620, `unauthorized_ran` 0 in 23 106 calls,
`auth_off_ran` 0 in 2 189, `private_ran` 0 in 13 647, `ran_while_paused` 0 in 2 490, `locked_spent` 0 in
1 439; no simulator or harness failure. `tx_stranded` 1 722 (1 615 after a failed `*_transfer_call` of the
contract, 105 after a failed wNEAR unwrap, 2 after a forced failure of the token's own settlement),
`withdraw_inexact` 993, `own_callback_failed` 671 (115 under injected failures of the wNEAR unwrap; 215 refunds of
the scripted token over the `u128` bound, 212 in the `bounds` probe and 3 in random operations; 341
`mt_resolve_transfer` callbacks that the `edges` probe makes run out of gas on purpose). Every guarded method was
called by a holder of each role and by an account with none, `upgrade` by `DAO` and by `Upgrader` excepted. The
mock: the backing monitor fired on 400 of 400 traces.

## The monitors are not vacuous

* `mock-token/` is the reference token with one change: a tenth of every `ft_transfer_call`
  stays with the token contract while the receiver is told the full amount. It does not satisfy
  NEP-141. The same generator on it: 200 traces, the backing monitor fires in 200 of them
  (`overcredit` 400, `tx_overcredit` 1 426 in the run with nine probes; `../evidence/monitors_summary_mock_200.json`). The ledger is backed
  only for tokens that deliver what they announce.
* `scripts/selftest.py` changes one recorded fact in a clean trace (a balance, an outcome, a
  measured move, a switch, a return value) and checks that the matching monitor reports it: 16
  doctorings for the 14 kinds, each caught on every applicable trace of the 49 clean ones among 80
  (`../evidence/selftest_1000.log`). For `unauthorized_ran`: a rejected guarded call recorded as
  successful, a rejected pause or lock recorded with the switch changed, a role grant by an
  account that is no admin recorded as answered `true`; for `auth_off_ran`: a rejected call
  recorded as successful.

## Build notes

libclang is needed only to build (RocksDB bindings of nearcore): set `LIBCLANG_PATH` (or `python3 -m pip install
libclang`, as `../../upgrade-window/README.md` describes). `target/` started as a copy of an existing build of the same
simulator commit; a build from nothing takes 10–30 minutes and several GB.
