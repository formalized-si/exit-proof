# Proved Token Standard: near-contract-standards 5.29.0 (NEP-141 + NEP-145)

Most fungible tokens on NEAR are built on `near-contract-standards` (`FungibleToken` + the NEP-145
storage management). For version **5.29.0** this directory holds three things:

1. **Properties you can read** — `PROPERTIES.md` (English text) and `properties.json` (the same text
   + the name of the Lean theorem + the sha256 of the text of its statement). They sit next to the
   code and are checked against the proofs with one command.
2. **Proofs** — Lean 4.35, a line-by-line model of the library, 16 theorems without `sorry`. They are
   theorems about a model; a certificate ties the model to the bytes of a concrete token by hash
   equality and execution.
3. **A kit for the token author** — `certify-token.sh token.wasm` deploys the *compiled* token in
   near-contract-sim, runs 1000 random traces against the executable Lean model and writes
   `certificate.json`: PASS, or FAIL with the first divergence and the name of the property.

Why: a dependency is code its users did not check themselves. "Formally verified dependencies are
needed, but then properties expression need to be readable and bundled with code." (Illia
Polosukhin, 2026-11-06; see `../docs/BACKGROUND.md`.) Here the properties travel with the code, and
the certificate ties them to a concrete wasm, not to the source of the library.

## Summary

| | Result |
|---|---|
| Theorems | 16 (P1–P5), Lean 4.35, no `sorry`; axioms `propext`, `Quot.sound`, `Classical.choice` (P3 — only `propext`) |
| The near-sdk-rs example (`examples/fungible-token/ft`, tag `near-sdk-v5.29.0`), built with cargo-near | **PASS**: 1000 traces, 33 118 receipts, 33 291 blocks, 20 029 return values, 9 702 events, 3 468 outgoing calls, 217 637 balance comparisons — 0 divergences |
| 10 mutants: 9 of the library, 1 of the example token (one line each, built into the same example) | **10 of 10 FAIL**, each with its first divergence pointing at the expected property; the unmutated control — PASS |
| Build | the example rebuilds byte for byte (`249fdb76…`, base58 `3Ty4ENxJ…`, 124 181 bytes), cargo-near 0.22, Rust 1.93.0 |
| Time | a certificate ≈ 8 s (8 threads); the token build ≈ 13 s; `check.sh --all` ≈ 3 min |

## How to use it

| Step | Command | Look at |
|---|---|---|
| Read the properties | — | `PROPERTIES.md`, `properties.json` |
| Check the proofs | `cd lean && lake build && lake env lean Axioms.lean` | `evidence/axioms.txt` |
| Check that the texts belong to these theorems | `python3 scripts/properties.py check lean properties.json` | `{"ok": true}` |
| Certify your token | `./certify-token.sh path/to/token.wasm [init_method init_args_json]` | `cert-<sha>/certificate.json` |
| Repeat everything | `./check.sh` (≈1 min), `./check.sh --all` (+ the mutants, ≈3 min) | `evidence/check_run.txt` |

The init arguments must give the initial supply to the account `owner.near` (it exists in the harness).
The default: `new_default_meta '{"owner_id":"owner.near","total_supply":"1000000000000000000000000000000"}'`.
Variables: `TRACES` (1000), `SEED` (20261112), `JOBS` (8), `OUT`, `KEEP=1` (keep the traces).

Requirements: Linux x86-64, `elan` (Lean 4.35.0 is installed from `lean/lean-toolchain`), `rustup`
(Rust 1.95.0 for the harness, 1.93.0 for the token, from the `rust-toolchain.toml` files), a C/C++
compiler, `cmake` and libclang (for nearcore's RocksDB bindings), `python3`, `git`; cargo-near 0.22
for rebuilding the example token and for the mutants. The harness is built against the public
`near/near-contract-sim` at commit `8e4b69b` (which pins nearcore 2.14.0); both are git
dependencies, locked in `harness/Cargo.lock`. Without root, libclang can be taken from the Python
package: `python3 -m pip install libclang`, then set `LIBCLANG_PATH` to its
`site-packages/clang/native` directory and add there a link named after the library's soname
(`ln -s libclang.so libclang.so.18.1`). See `scripts/env.sh`.

`check.sh` exits with 0 only if the proofs build without `sorry`, the axioms are among `propext`,
`Classical.choice`, `Quot.sound`, `properties.json` matches the Lean sources, the example token's wasm
has the pinned hash and its certificate is PASS (with `--all`: also the control is PASS and every
mutant is FAIL with the expected property). `certify-token.sh` exits with 0 only for PASS.

On a clean machine (32 cores, shared with other jobs; a fresh copy of this directory, no build
products; 2026-11-12) `./check.sh` took 7 min 6 s, of which 6 min 50 s to compile the harness with
nearcore (8 jobs), with the result PASS and a certificate byte-identical to
`evidence/certificate_example.json`; cargo-near was not installed, so the rebuild of the example
was skipped. After `cargo install cargo-near@0.22.0 --locked` (6 min 41 s), `./check.sh --all` took
3 min 14 s: the example rebuilt from source to the same bytes although the cargo home was in a
different directory (rustc embeds the registry path in panic locations; `check.sh` maps it to the
path of the pinned build), the control was PASS and 10 of 10 mutants were FAIL with the expected
properties.

## The properties (in short; the full text is in `PROPERTIES.md`)

| | Property | Theorems |
|---|---|---|
| P1 | `total_supply` = the sum of the balances in every reachable state | `P1_conservation`, `P1_inv_step` |
| P2 | The refund of an `ft_transfer_call` is ≤ the amount transferred and ≤ what the receiver holds now; the receiver loses exactly the refund; the sum sender + receiver is preserved, and if the sender has unregistered the refund is burned; the callback does not fail for arithmetic reasons | `P2_settlement`, `P2_settlement_call`, `P2_settlement_never_fails` |
| P3 | `ft_resolve_transfer` takes effect only as the token's own callback: from a user, from another contract, as the callback of someone else's promise with any results, by a transaction signed with the token's own key — it fails and nothing changes | `P3_callback_private`, `P3_callback_private_sys` |
| P4 | A holder's balance is lowered only by the holder's own call (`ft_transfer`, `ft_transfer_call`, `storage_unregister(force)`) or by the refund of a transfer made **to** the holder, by no more than the amount of that transfer | `P4_balance_ownership`, `P4_who_can_lower`, `P4_pending_origin` |
| P5 | `storage_unregister`: with force — removal, the whole balance burned, a payout of `min + 1 yocto`; with a zero balance — the same without a burn; without force and with a balance > 0 — a failure with no changes; unregistered — `false`, no changes. `storage_deposit` takes exactly `min` and refunds the rest. The token's NEAR always covers the storage and all deposit refunds | `P5_unregister_force`, `P5_unregister_zero`, `P5_unregister_refused`, `P5_unregister_unknown`, `P5_storage_deposit`, `P5_storage_solvent` |

## The model (`lean/ProvedFT/Model.lean`)

- Line by line after `core_impl.rs`, `storage_impl.rs`, `events.rs` of 5.29.0 and the code generation of
  near-sdk 5.29.0 (`#[private]`, a non-payable method refusing a deposit, a repeated `#[init]`, a view
  accepting a deposit).
- Exact u128 arithmetic (`checked_*` and `overflow-checks = true` ⇒ an overflow is a failure with no
  changes), `NearToken::saturating_*` saturate.
- A promise result is bytes: `promise_result_checked(0, 42)` (longer than 42 bytes ⇒ "nothing was
  used"), `serde_json` parsing → `U128` (`str::parse::<u128>`, whitespace, escaping).
- `GAS_FOR_RESOLVE_TRANSFER` = 5 Tgas with weight 0: the callback carries exactly 5 Tgas — compared on
  every call.
- The NEP-141 events (`ft_transfer`, `ft_burn` with the memo `refund`) and the return values — as data.
- Runtime: the deposit is credited, transfers are debited, the storage stake is checked; a failed
  receipt changes nothing. An account entry = `40 + (prefix + 4 + id length) + 16` bytes; the storage
  minimum = such an entry for an id of 64 characters.
- System: any calls by anyone in any order; the callback of any transfer in flight with any result, or
  a lost one (gas); NEAR arriving. A receipt whose predecessor is the token itself is either its
  callback or a transaction signed with its key (no promise results).
- The initial state is whatever the `#[init]` of the concrete token left; the kit checks `InitOK` on
  it (the sum of the balances = supply, the NEAR covers the storage and `min` for every account).

## The certification kit (`certify-token.sh`)

| Part | What it does |
|---|---|
| `harness/` (`ftcert-gen`) | Deploys the wasm in near-contract-sim, runs init; finds the prefix of `accounts` in storage by a trial registration; 4 deterministic checks of P3; traces: 9 accounts (ids of 7 to 64 characters, 2 stub receivers, `ghost.near` without an account, `evil.near` — a WAT contract that makes `ft_resolve_transfer` the callback of its own failing promise); operations: transfers, `ft_transfer_call` with receiver replies (numbers, garbage, the 42/43-byte boundary, `5`, a panic, moving the tokens away, unregistering, a reply at the length limit, a number instead of a string), a callback delay of 1–4 blocks, a forced failure, all `storage_*`, views as transactions, a repeated init, direct and foreign calls of the callback, bad arguments |
| `lean/Main.lean` (`ftmodel`) | Replays the receipts through `ProvedFT.exec` |
| `scripts/compare.py` | For every receipt: success/failure, the return value, the NEAR transfers, the outgoing calls (the arguments of `ft_on_transfer`, the arguments and gas of the callback), the events; for every block: supply, NEAR, storage_usage, the whole account map. Plus monitors that need no model: P1 (supply = Σ), P2 (used ≤ amount), P3 (a successful callback is only the token's own), P4 (who lowered a balance in the block) |
| `scripts/cert.py` | `certificate.json`: the sha256 of the wasm, the version of the standard, the hashes of the Lean files and of `properties.json`, the properties with their status, the counters, the first divergence, the reasons for a FAIL |

A divergence is attributed to the property whose proof covers that behaviour (the token's own callback
→ P2, a foreign callback → P3, transfers → P4, `storage_*`/NEAR → P5, supply → P1); only the first
divergence of a trace is counted — after it the states already differ.

**P3 is a property the kit checks on the token's wasm.** In near-contract-standards 5.29.0 the caller
check of the settlement callback is the documented responsibility of the token: the token puts
`#[private]` on its `ft_resolve_transfer` (the example does; the legacy macro
`impl_fungible_token_core!` adds it), and the library's `FungibleToken::ft_resolve_transfer` has no
check of its own. A token that implements the trait by hand without the attribute is open to the
behaviour of mutant M10: any contract makes `ft_resolve_transfer` the callback of its own failing
promise and moves the victim's balance to itself (the class of the SWEAT incident, see
`../docs/BACKGROUND.md`). So P3 is checked on the token's wasm and is not inherited from the library.

## Mutants (`scripts/mutants.py`, `evidence/mutants.json`, `evidence/mutants.diff`)

10 mutants: 9 of the library (M1–M9), 1 of the example token (M10). Every mutation is one line; each
is built with cargo-near into the same example; the kit is run with its default settings.

| Mutant | Line | Result | First divergence → property | Diverging traces of 1000 | Monitors without the model |
|---|---|---|---|---|---|
| M0 control | unchanged (the same build through a path patch) | **PASS** | — | 0 | — |
| M1 | `.min(amount.0)` → `.min(u128::MAX)`: unused is not capped by the amount | FAIL | the callback fails in the wasm and succeeds in the model → **P2** | 147 | — |
| M2 | `.unwrap_or(amount)` → `.unwrap_or(U128(0))`: garbage = "everything used" | FAIL | the callback's return value → **P2** | 534 | — |
| M3 | the debit of the receiver on a refund is removed | FAIL | the map after the callback → **P2** | 719 | P1 (11 803 blocks) |
| M4 | `account_storage_usage … - 1`: the storage minimum is a byte short | FAIL | the reply of `storage_deposit` (1.24e21 instead of 1.25e21) → **P5** | 1000 | — |
| M5 | `GAS_FOR_RESOLVE_TRANSFER` 5 → 3 Tgas | FAIL | the callback's gas → **P2** | 776 | — |
| M6 | `checked_sub` → `saturating_sub` in `internal_withdraw`: an overdraft | FAIL | an `ft_transfer` above the balance succeeds → **P4** | 421 | P1 (7 087) |
| M7 | `total_supply -= balance` → `-= 0` on force-unregister | FAIL | supply ≠ Σ balances → **P1** | 445 | P1 (7 030) |
| M8 | `force.unwrap_or(false)` → `true` | FAIL | an unregister without force with a balance > 0 succeeds → **P5** | 222 | — |
| M9 | the excess of `storage_deposit` goes to the registered account, not to the payer | FAIL | the NEAR transfers → **P5** | 548 | — |
| M10 | `#[private]` removed from the example's `ft_resolve_transfer` | FAIL | the callback of `evil.near` succeeds → **P3** | 329 | P3 (406), P4 (240: the victim's balance is lowered) |

The deterministic P3 checks in the certificate of M10: direct calls of `ft_resolve_transfer` by a user, by a contract and with the token's key still fail (there is no promise result), while the callback of `evil.near` succeeds and zeroes the victim's balance (5·10²⁹ → 0). Without `#[private]` a direct call shows nothing — only the path through someone else's `promise_then` is dangerous.

The wasm hashes of the mutant builds in `evidence/mutants.json` depend on the directory they were built
in (the patched library is a path dependency and rustc embeds source paths in panic locations); the
results and the counts do not.

## Observations

1. **A reply of the receiver longer than 42 bytes = "nothing was used".** `promise_result_checked(0, 42)`:
   `"0…07"` of 42 bytes is parsed, of 43 — a full refund (both boundaries are in the traces).
2. **A key on the token's account is outside the standard.** Transactions signed with the token's key pay
   gas from its NEAR; in the first run this produced a divergence in the NEAR balance. P5 (storage
   solvency) assumes that only the code spends the token's NEAR. The comment of the example asks for the
   same: "do not keep keys on the account". The random traces send no such transactions; a deterministic
   check of the callback signed with the token's key exists (a failure: there is no promise result).
3. `storage_unregister` of an unregistered account succeeds and leaves 1 yocto with the token;
   `storage_deposit` for an already registered account returns the whole deposit to the payer.
4. The header of the example describes "tracking the storage change before and after a call and refunding
   the excess" — the 5.29.0 code does not do that (storage is paid by a fixed `min` at registration).

## Limits

| Modelled | Not modelled / not covered |
|---|---|
| The NEP-141/145 methods of the library as the example exposes them | The token's own methods (mint, burn, pause, owner, `ft_metadata`): the kit does not call them; a token with such methods can get PASS while they violate P1–P5 |
| The callback's gas (exactly 5 Tgas) | The rest of gas; running out of gas = a failed receipt; a callback that ran out of gas is a lost one (`resolveFails`), there is no refund |
| The NEP-141 events as JSON data | Other logs (`Closed @…`, `Account @… burned`) and the byte-exact `EVENT_JSON` string |
| Any order of receipts in the model | Multi-shard delays: the simulator has one shard, overlaps come from delaying the callback by 1–4 blocks (1458 of the 1734 callbacks ran with other transactions' receipts between the steps) |
| The initial state after init — checked by `InitOK` | The `#[init]` itself (every token has its own) |
| | The parsing layer (JSON arguments, id validation, the forms of replies and events) is not proved — it is checked only on the harness's inputs |
| | PASS is agreement on 1000 traces, not a proof for all inputs; the receivers are scripted stubs (a nested `ft_transfer_call` is not generated, although the model covers it) |
| | Keys on the token's account, code upgrades, the mainnet protocol constants (the simulator = the nearcore runtime in process) |

## Files

- `lean/ProvedFT/Map.lean`, `Model.lean`, `Lemmas.lean`, `Theorems.lean`; `lean/Main.lean` (`ftmodel`); `lean/Axioms.lean`
- `PROPERTIES.md`, `properties.json`, `scripts/properties.py`
- `certify-token.sh`, `harness/` (`ftcert-gen`), `scripts/compare.py`, `scripts/cert.py`, `scripts/env.sh`
- `token/example-ft/` — the near-sdk-rs example (crates.io dependencies `=5.29.0`, the release profile of
  the workspace, a `Cargo.lock` with the checksums of the crates); `token/out/fungible_token.wasm`,
  `token/EXAMPLE_WASM_SHA256` (the build repeats byte for byte: `check.sh` compares the hash);
  `fetch-wasm.sh` compares the example's source with the upstream commit; `NOTICE`
- `scripts/mutants.py`, `check.sh`
- `evidence/`: `axioms.txt`, `certificate_example.json`, `conformance_example.json`, `probe_example.json`,
  `mutants.json`, `mutants.diff`, `mutants_certificates/`, `example_wasm_sha256.txt`, `check_run.txt`
- `check.sh` and `certify-token.sh` write their working output to `runs/`, `mutants/`, `std/` (the
  library source downloaded from crates.io for the mutants) and `cert-*/`; none of these is part of the
  repository.
