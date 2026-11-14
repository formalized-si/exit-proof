# token-monitors: check your NEAR fungible token against the proved NEP-141 properties

You give the kit the compiled wasm of your token and a short config that says how to initialize it.
The kit deploys the wasm in a local simulator that runs the real nearcore runtime, drives it with
1000 random multi-account traces and checks 14 monitors on what an outside observer sees. It writes
a certificate file with the hashes of your wasm, the counts of every monitor and a verdict.

Nothing is deployed, signed or sent to any network. The only network use in the whole kit is
optional: `fetch-code.sh` and the mainnet examples of `check.sh` read public contract code with a
read-only query.

```
./inspect.sh     token.wasm                 # hashes and exported methods
./try-config.sh  token.wasm my.json         # make the init and setup calls, show what happened
./certify.sh     token.wasm my.json         # 1000 traces -> certificate.json; exit 0 only for PASS
./verify-certificate.sh certificate.json token.wasm [--rerun]
./check.sh                                  # the kit checks itself
```

## What a PASS means

- The wasm with the sha256 and NEAR code hash in the certificate, initialized as the config in the
  certificate says, was run through the stated number of random traces: transfers of every size
  including more than the balance and zero, `ft_transfer_call` to receivers that return numbers,
  return garbage, fail, call the token back or burn their gas, storage calls, strangers trying the
  settlement callback, repeated inits, malformed arguments.
- Every one of the 14 monitors made checks, every kind of step those checks depend on happened, and
  not one check was a violation. The counts are in the certificate.
- The run is deterministic. Anyone with the same wasm and this kit can repeat it with
  `verify-certificate.sh --rerun` and must get the same result digest.

## What a PASS does not mean

- It is not a proof. P1-P5 are proved for a model of `near-contract-standards` 5.29.0
  (`PROPERTIES.md`, `proofs/`); for your wasm the kit shows that no execution of this run
  contradicted them. A flaw that needs an input the traces did not produce is not found.
- It says nothing about NEAR-side storage accounting (deposits kept, refunds paid, the storage
  minimum, solvency) and nothing about gas. Three of the ten reference mutants change only those
  and pass unnoticed; see the table below.
- It covers only the methods the run reached. Mint, burn, pause, fee, blocklist, upgrade and owner
  methods are not called unless your config calls them, and then only as the config calls them. The
  certificate lists every exported method that no call reached, under `not_checked`.
- It is about code in a simulator, initialized with test arguments. It says nothing about the
  state, the access keys, the owner rights or the upgrade path of a deployed contract. Compare the
  `near_code_hash` in the certificate with the code hash of your account to know the certificate is
  about the code you deployed.
- Events, error texts and `ft_metadata` are not judged.

## The properties

| Property | In one sentence | Monitors |
|---|---|---|
| P1 Conservation | The total supply always equals the sum of the balances; a transfer moves exactly its amount | `P1.supply_eq_sum`, `P1.exact_transfer` |
| P2 Settlement | An accepted `ft_transfer_call` is always settled; the refund is at most the amount, is what the receiver's reply asks for, moves only between receiver and sender, and what the token reports is what moved | `P2.settlement_completed`, `P2.refund_le_amount`, `P2.reported_refund_eq_returned`, `P2.receiver_keeps_used`, `P2.pair_conserved`, `P2.refund_follows_reply`, `P2.rejected_call_no_effect` |
| P3 Callback ownership | Nobody but the token's own pending transfer can run the settlement callback | `P3.foreign_resolve_fails`, `P3.foreign_resolve_no_effect` |
| P4 Balance ownership | A balance falls only through its holder's own successful call | `P4.lowered_only_by_holder`, `P4.non_transfer_op_changes_others` |
| P5 Storage (balance side only) | `storage_unregister` without force never destroys a positive balance | `P5.unregister_refused` |

`PROPERTIES.md` states each monitor exactly and names the theorem it follows from.

## Writing a config for your token

1. **Look at the wasm.** `./inspect.sh token.wasm` prints its hashes and exported methods and
   names the likely init methods.
2. **Write the init call.** Start from `examples/reference.json`. Put your init method and its
   arguments under `init`, with the supply going to `owner.near` (an account the simulator already
   has). If only a factory or an owner may call the init, add that account under `accounts`, set
   `init.caller` to it, and if the token checks its own name set `token_account` (see
   `examples/factory-minted.json`).
3. **Try it.** `./try-config.sh token.wasm my.json` makes the calls and prints each one with the
   token's own failure text (a missing argument is named there), the supply, and who holds what.
   Repeat until it says `SET-UP OK`.
4. **Add what the token needs after init.** If tokens are minted or distributed after init, add
   those calls under `setup` (register the receiver with `storage_deposit` first if your token
   requires it). If your init calls another contract, add a stub for it under `stubs`. If an
   account other than the simulator's own ends up holding tokens, list it under `track`.
   `try-config.sh` tells you when the supply and the watched balances disagree.
5. **Certify.** `./certify.sh token.wasm my.json --out certificate.json`. About a minute on 8
   cores.

`CONFIG.md` documents every field and the simulated world. For the four mainnet token codes among
the examples, writing the config took one to four attempts with `try-config.sh`.

## The certificate

`certificate.json` holds:

| Field | Content |
|---|---|
| `verdict`, `reasons` | PASS, FAIL or INCONCLUSIVE, and why when it is not PASS |
| `wasm` | file name, size, `sha256`, `near_code_hash` (the base58 form NEAR shows for a contract) |
| `config`, `config_sha256` | the config as used, and the sha256 of its JSON with sorted keys and no whitespace |
| `run` | traces requested and judged, seed, rounds, blocks, token receipts, `trace_digest` (a hash over all traces) |
| `setup` | the init and setup calls with their outcome, the supply, the holders, the funder, the watched accounts |
| `monitors` | per monitor: the property, the statement, `checks`, `violations`; on a violation also up to three examples |
| `coverage`, `operations` | how often each kind of step happened |
| `exports` | exported methods outside the standards, never called, called only by the set-up |
| `not_checked` | what this run does not cover, in words, including the methods no call reached |
| `kit` | version, `bundle_sha256` (one hash over the files that decide a run: the list `BUNDLE` in `scripts/kitlib.py`), simulator and runtime commits |
| `result_digest` | one hash over the inputs, the kit, the traces, the counts and the verdict; a re-run must reproduce it |

Exit status of `certify.sh`: 0 PASS; 1 FAIL; 2 INCONCLUSIVE; 3 the run did not happen (bad
arguments, an invalid config, a tool failure) and no certificate was written.

INCONCLUSIVE is the vacuity guard. A monitor with zero checks has not passed: if your token accepts
no `ft_transfer_call`, or nothing was minted, or the supply sits where no user can move it, the
certificate says so in words (for example "P2.settlement_completed made no check: no
ft_transfer_call was accepted in any trace") and the exit status is 2.

`tests/guards/` holds eight such cases that `check.sh` runs, among them a full 1000-trace run on a
token whose `ft_transfer_call` always fails: no monitor fires on it, and the verdict is
INCONCLUSIVE, not PASS.

A FAIL on your own token comes with examples: the trace number, the round, the operation and the
balances that disagree. `--keep-traces DIR` keeps the full traces.

## The kit checks itself

`./check.sh` rebuilds the trace generator, the reference token (the near-sdk-rs fungible-token
example with `near-contract-standards` 5.29.0) and ten one-line mutants of it, then requires: the
reference token passes; every mutant either fails with the monitors of the property it breaks or
is one of those listed as outside the monitors; every example config passes; every guard case ends
INCONCLUSIVE or is refused; the configs of `tests/setup/`, which together use every key of the
config format, are set up as expected; a certificate verifies and an altered one does not. Exit status 0 only
if all of that holds. `check.sh` writes its own table to `build/check/summary.md`; this is the
one it produced when the kit was assembled (a full run takes about a quarter of an hour on a busy
32-core machine once the trace generator is built):

| Build | Change | Breaks | Result | Monitors that fired (violations in 1000 traces) |
|---|---|---|---|---|
| reference | none: the near-sdk-rs example, near-contract-standards 5.29.0 | - | PASS | none |
| M0_control | none: the same library built through the path patch the mutants use | - | PASS | none |
| M1_refund_not_capped | the unused amount the receiver reports is no longer capped by the transferred amount | P2 | caught | `P2.settlement_completed` (190) |
| M2_unparsable_means_used | an unparsable, failed or too long receiver result counts as fully used instead of fully refunded | P2 | caught | `P2.refund_follows_reply` (497) |
| M3_receiver_not_debited | the refund is credited to the sender without debiting the receiver | P2 | caught | `P2.receiver_keeps_used` (1442), `P2.pair_conserved` (1442), `P1.supply_eq_sum` (50617) |
| M4_storage_off_by_one | the storage minimum is measured one byte short | P5, NEAR side | **outside**: changes only how much NEAR a registration costs | none |
| M5_resolve_gas_3tgas | the settlement callback gets 3 Tgas instead of 5 | gas | **outside**: changes only the gas of the callback, which still completes in the simulator | none |
| M6_withdraw_overdraft | a withdrawal larger than the balance empties the account instead of being refused, while the receiver is credited in full | P1 | caught | `P1.exact_transfer` (124), `P1.supply_eq_sum` (26666), four P2 monitors (134, 198, 2, 186) |
| M7_force_unregister_no_burn | a forced unregistration removes the balance but leaves it in the total supply | P1 | caught | `P1.supply_eq_sum` (23822) |
| M8_unregister_default_force | `storage_unregister` without the force argument burns a positive balance | P5, balance side | caught | `P5.unregister_refused` (128) |
| M9_deposit_refund_to_account | `storage_deposit` refunds the excess NEAR to the registered account instead of the payer | P5, NEAR side | **outside**: changes only who receives a NEAR refund | none |
| M10_resolve_not_private | `#[private]` removed from the token's `ft_resolve_transfer` | P3 | caught | `P3.foreign_resolve_fails` (926), `P3.foreign_resolve_no_effect` (264), `P4.lowered_only_by_holder` (556) |

So the monitors catch 7 of the 10 mutants. The other 3 change only NEAR amounts or gas,
which no monitor reads; a PASS says nothing about faults of that kind.

## Limits

- Random testing: 1000 traces of 12 to 29 rounds each, 5 users, 2 scripted receivers, 1 hostile
  contract, one shard. Faults that need longer histories, more parties or cross-shard timing are
  not exercised. `--traces N` and `--seed S` change the amount and the choice of traces.
- The simulator runs the nearcore runtime in one process; it is not a network. Gas prices,
  congestion and validators are not modelled.
- The generator speaks NEP-141 and NEP-145 only. A token with transfer hooks, fees or pauses is
  judged with those switches as your `setup` leaves them.
- The monitors assume `ft_balance_of` and `ft_total_supply` are honest views of the state. A token
  whose views lie consistently is not detected.
- `P2.refund_follows_reply` judges only replies every library version parses the same way (a number
  in a string, or a failure).
- A token that needs an init the config cannot express (several coordinated contracts, time-locked
  phases) ends as INCONCLUSIVE at the set-up, with the token's own failure text.

## Requirements and layout

Linux x86-64, `python3` (3.10 or newer, standard library only), `rustup` (the toolchains are named
in `harness/rust-toolchain.toml` and `reference/token/rust-toolchain.toml`), a C/C++ compiler, `cmake`
and libclang for the nearcore runtime (`scripts/env.sh` explains `LIBCLANG_PATH`). `check.sh` also
needs `cargo-near` for the reference token. The first build of the trace generator compiles the
runtime and takes 5 to 20 minutes; after that a certificate takes about a minute.

Everything the kit builds or downloads goes to `build/` (or `$TOKEN_MONITORS_BUILD`); nothing built
is stored in the kit.

| Path | Content |
|---|---|
| `certify.sh`, `try-config.sh`, `inspect.sh`, `verify-certificate.sh`, `fetch-code.sh`, `check.sh` | the commands |
| `CONFIG.md`, `PROPERTIES.md` | the config format; the properties and monitors |
| `harness/` | the trace generator `ftmon` (Rust, on near-contract-sim at a pinned commit, nearcore 2.14.0) |
| `monitors/monitors.py` | the monitors |
| `scripts/` | certificate writer, config validation, self-check, build helpers |
| `examples/` | example configs and `examples.json` (which wasm each one is for) |
| `reference/` | the reference token's source, the mutant list, the builder |
| `tests/guards/`, `tests/setup/` | configs that must not pass; configs that use every key of the format |
| `proofs/` | the Lean proofs of P1-P5 and `proofs/check.sh` to rebuild them (optional, needs elan) |
