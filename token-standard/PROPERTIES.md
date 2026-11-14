# Properties of near-contract-standards 5.29.0 (FungibleToken + StorageManagement)

Scope: the NEP-141 core and NEP-145 storage implementation in `near-contract-standards` 5.29.0
(`fungible_token/core_impl.rs`, `fungible_token/storage_impl.rs`, `fungible_token/events.rs`),
exposed the way the near-sdk-rs example token does it (`examples/fungible-token/ft`, tag
`near-sdk-v5.29.0`): `#[payable]` `ft_transfer` / `ft_transfer_call` / `storage_*`,
`#[private]` `ft_resolve_transfer`, view methods.

The receiver's `ft_on_transfer` is arbitrary: it may call the token back in any order, return any
bytes (a number, an unparsable value, a value longer than 42 bytes) or fail. Any account may send any
call at any time, including other contracts' callbacks with promise results of their choice.

Machine-readable form with the sha256 of every theorem statement: `properties.json`.
Lean sources: `lean/ProvedFT/` (`Model.lean` is the model, `Theorems.lean` the statements below).

## P1. Conservation

**In every reachable state, `total_supply` equals the sum of all account balances.**

| Lean theorem | One sentence |
|---|---|
| `ProvedFT.P1_conservation` | If a state is reachable from an initial state satisfying `InitOK`, then `supply = total accts`. |
| `ProvedFT.P1_inv_step` | Every step (any call by anyone, any settlement with any result, a dropped settlement, NEAR arriving) preserves the invariant `Inv` (supply = sum of balances, no duplicate accounts, supply ≤ u128::MAX, storage solvency, well-formed callbacks in flight). |

## P2. transfer_call settlement

**When the settlement callback of an `ft_transfer_call` of `amount` from a sender to a receiver runs,
whatever the receiver did, the refund to the sender is at most `amount` and at most what the receiver
still holds; the receiver loses exactly the refund and no other account changes; if the sender is
still registered, the sender gains exactly the refund, so the sender + receiver total and the supply
are conserved; if the sender has unregistered, the refund is burned.**

| Lean theorem | One sentence |
|---|---|
| `ProvedFT.P2_settlement` | In a reachable state, running the `i`-th callback in flight `(sn, rc, amt)` with any promise result gives a refund `f ≤ amt`, `f ≤ bal rc`, debits `rc` by exactly `f`, leaves every other account but `sn` unchanged, removes the callback from the list, sends no NEAR, and either credits `sn` with `f` (sum of the two and supply unchanged) or, if `sn` is unregistered, burns `f`. |
| `ProvedFT.P2_settlement_call` | The same for one call of `ft_resolve_transfer` from any state: also `f ≤` the unused amount the receiver reported, and the call returns `amt - f` (sender registered) or `amt` (sender gone). |
| `ProvedFT.P2_settlement_never_fails` | In every state satisfying the invariant, the settlement callback succeeds for any promise result: no overflow or underflow can stop it (only gas can, which the model treats as a dropped callback). |

## P3. Callback ownership

**`ft_resolve_transfer` takes effect only as the token's own settlement callback: called by any other
account, by another contract, as another contract's callback with promise results of its choice, or
by a transaction signed with the token account's own key, it fails and changes nothing.**

| Lean theorem | One sentence |
|---|---|
| `ProvedFT.P3_callback_private` | With any predecessor other than the token, any arguments, deposit and promise results, `ft_resolve_transfer` fails. |
| `ProvedFT.P3_callback_private_sys` | A `call` step of `ft_resolve_transfer` by any account (the token's own key included: a transaction carries no promise result) leaves the whole system state unchanged. |

Note: in 5.29.0 the caller check is not inside the library. `FungibleToken::ft_resolve_transfer`
has none; the token contract must mark its own `ft_resolve_transfer` `#[private]` (the example does).
The property is therefore a property of the token, and the kit checks it on the token's wasm.

## P4. Balance ownership

**No step other than a call by the holder lowers the holder's balance, except the settlement of an
`ft_transfer_call` made to that holder, which takes back at most the amount of that transfer.**

| Lean theorem | One sentence |
|---|---|
| `ProvedFT.P4_balance_ownership` | A step that is not a call by `u` either does not lower `u`'s balance, or is the settlement of a callback `(sn, u, amt)` in flight and lowers it by at most `amt`. |
| `ProvedFT.P4_who_can_lower` | A step that lowers `u`'s balance is `u`'s own `ft_transfer`, `ft_transfer_call` or `storage_unregister(force = true)`, or the settlement of a transfer to `u`. |
| `ProvedFT.P4_pending_origin` | A callback in flight `(p, rc, x)` is created only by a successful `ft_transfer_call` of `p`, with `p ≠ rc`, `x > 0`, which credited `rc` exactly `x` and debited `p` exactly `x`. |

## P5. Storage

**`storage_unregister` with 1 yoctoNEAR: with `force = true` it removes the caller's account, burns
its whole balance and pays the caller the storage minimum + 1 yoctoNEAR; with a zero balance it does
the same with or without force and burns nothing; without force and with a positive balance it fails
and changes nothing; for an unregistered caller it changes nothing and returns false.
`storage_deposit` registers an account for exactly the storage minimum and refunds the rest. In
every reachable state the token holds enough NEAR for its storage plus every refund it owes.**

| Lean theorem | One sentence |
|---|---|
| `ProvedFT.P5_unregister_force` | In a reachable state, a registered `u` with balance `b` calling `storage_unregister(force = true)` with 1 yocto is removed, `total_supply` drops by exactly `b`, the token's NEAR drops by `minBal`, and `u` is sent `minBal + 1`. |
| `ProvedFT.P5_unregister_zero` | A registered `u` with balance 0 calling `storage_unregister` with any `force` and 1 yocto is removed, the supply is unchanged, and `u` is sent `minBal + 1`. |
| `ProvedFT.P5_unregister_refused` | A registered `u` with a positive balance calling `storage_unregister` without `force = true` changes nothing at all. |
| `ProvedFT.P5_unregister_unknown` | An unregistered `u` calling `storage_unregister` with 1 yocto gets `false`, no balance and not the supply changes, nothing is sent, and the token keeps the yocto. |
| `ProvedFT.P5_storage_deposit` | `storage_deposit` for an unregistered account with `d ≥ minBal` registers it with balance 0, keeps exactly `minBal` and refunds `d - minBal` to the caller; with `d < minBal` it changes nothing. |
| `ProvedFT.P5_storage_solvent` | In every reachable state the token's NEAR covers the base storage stake plus `minBal` per registered account, and hence the actual stake of the account entries. |

## Axioms

`#print axioms` for all 16 theorems (`evidence/axioms.txt`): `propext`, `Quot.sound`, and for most
also `Classical.choice` (from `omega` / `simp`); `P3_callback_private*` use only `propext`.
No `sorry`, no `native_decide`, no new axioms.

## Checking that these texts belong to these proofs

```
python3 scripts/properties.py check lean properties.json   # statement hashes + Lean file hashes
cd lean && lake build && lake env lean Axioms.lean            # proofs and axioms
```

A statement's hash is the sha256 of its text in `Theorems.lean` from `theorem NAME` up to the `:=`
of the proof, with whitespace runs collapsed to one space. The Lean file hashes pin the definitions
(`Model.lean`) the statements refer to.

## What a certificate for a token adds

The theorems are about the model. `certify-token.sh` checks that a compiled token wasm behaves like the
model: on random multi-account traces it compares every receipt (success, return value, NEAR sent,
calls sent including the settlement callback's 5 Tgas, NEP-141 events) and the state after every
block. On a PASS, P1–P5 describe that wasm on the traces run; it is a test, not a proof for all inputs.
