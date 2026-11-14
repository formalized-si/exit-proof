# The properties and the monitors

## Where the properties come from

P1-P5 are theorems proved in Lean 4 about a line-by-line model of `near-contract-standards`
5.29.0 (`FungibleToken` + NEP-145 storage management), exposed the way the near-sdk-rs
fungible-token example exposes it. The sources are in `proofs/lean/ProvedFT/` (`Model.lean` is the
model, `Theorems.lean` the statements); `proofs/properties.json` quotes every statement with its
sha256, and `proofs/check.sh` rebuilds the proofs and compares the quotes. In the model the
receiver's `ft_on_transfer` is arbitrary (it may call the token back, return any bytes or fail) and
any account may send any call at any time.

A theorem about a model says nothing about your wasm by itself. The monitors are the bridge: each
one is a statement that follows from the theorems and that an outside observer can test on an
execution, reading only `ft_total_supply`, `ft_balance_of` and the receipts the token executed. The
monitors use no model, no storage layout, no error texts and no log format, so they apply to a
token built on another library version or written without the library. What they establish is
agreement on the executions of one run, not a proof.

## P1. Conservation

In every reachable state the total supply equals the sum of all account balances.
(`P1_conservation`, `P1_inv_step`)

## P2. Settlement of `ft_transfer_call`

When the settlement callback of an `ft_transfer_call` of `amount` runs, whatever the receiver did,
the refund to the sender is at most `amount` and at most what the receiver still holds; the receiver
loses exactly the refund and no other account changes; the sender gains exactly the refund (if the
sender has unregistered, the refund is burned). The callback cannot fail for arithmetic reasons.
(`P2_settlement`, `P2_settlement_call`, `P2_settlement_never_fails`)

## P3. Callback ownership

`ft_resolve_transfer` takes effect only as the token's own settlement callback: called by any other
account, by another contract, as another contract's callback with results of its choice, or by a
transaction signed with the token's own key, it fails and changes nothing.
(`P3_callback_private`, `P3_callback_private_sys`)

## P4. Balance ownership

No step other than a call by the holder lowers the holder's balance, except the settlement of an
`ft_transfer_call` made to that holder, which takes back at most the amount of that transfer.
(`P4_balance_ownership`, `P4_who_can_lower`, `P4_pending_origin`)

## P5. Storage

`storage_unregister` with force burns the caller's whole balance and removes the account; without
force and with a positive balance it fails and changes nothing; `storage_deposit` keeps exactly the
storage minimum and refunds the rest; the token always holds enough NEAR for its storage and the
refunds it owes. (`P5_unregister_force`, `P5_unregister_zero`, `P5_unregister_refused`,
`P5_unregister_unknown`, `P5_storage_deposit`, `P5_storage_solvent`)

Only the balance side of P5 is monitored. Everything about NEAR amounts is outside the monitors.

## The monitors

"Round of its own" means the operation was the only one submitted in that round, so every balance
change of the round belongs to it. Rounds of several interleaved operations get only the monitors
marked "every round".

| Monitor | What is checked | When | Follows from |
|---|---|---|---|
| `P1.supply_eq_sum` | `ft_total_supply` equals the sum of `ft_balance_of` over the watched accounts | after every block of every round | `P1_conservation` |
| `P1.exact_transfer` | a successful `ft_transfer` of `a` lowers the sender by exactly `a`, raises the receiver by exactly `a`, changes nobody else and not the supply; a failed one changes nothing | every `ft_transfer` in a round of its own | the `ft_transfer` step of the model, on which P1 and `P4_who_can_lower` rest; NEP-141 itself |
| `P2.settlement_completed` | the token's own settlement callback runs, succeeds and returns the used amount | every accepted `ft_transfer_call` in a round of its own | `P2_settlement_never_fails` |
| `P2.refund_le_amount` | the used amount the token reports is at most the amount; the tokens that moved back to the sender are between 0 and the amount | every settlement; the reported side also in every round | `P2_settlement` |
| `P2.reported_refund_eq_returned` | amount minus the used amount the settlement returns equals the tokens that actually moved back to the sender | every settlement in a round of its own | `P2_settlement_call` |
| `P2.receiver_keeps_used` | the receiver ends with exactly the amount minus the reported refund, minus what it paid out itself | settlements where the receiver did not unregister | `P2_settlement` |
| `P2.pair_conserved` | only the sender, the receiver and the accounts the receiver paid itself change; the changes sum to zero; the supply does not change | same | `P2_settlement` |
| `P2.refund_follows_reply` | the receiver returns the unused amount `u`: the refund is `min(u, amount)`; the receiver fails: the refund is the whole amount | settlements after a plain reply (a number in a string, or a failure) | `P2_settlement_call` |
| `P2.rejected_call_no_effect` | a rejected `ft_transfer_call` changes no balance and not the supply | every rejected call in a round of its own | a failed receipt changes no state; `P4_balance_ownership` |
| `P3.foreign_resolve_fails` | the settlement callback run by a stranger fails. Four ways: a direct call by a user, a call by a contract, the callback of another contract's promise, a transaction signed with the token's key | every such receipt, every round | `P3_callback_private` |
| `P3.foreign_resolve_no_effect` | such an attempt changes no balance and not the supply | every attempt in a round of its own | `P3_callback_private_sys` |
| `P4.lowered_only_by_holder` | a balance falls in a round only if its holder made a successful call to the token in that round | every watched account with a positive balance, every round | `P4_balance_ownership` |
| `P4.non_transfer_op_changes_others` | `storage_deposit`, `storage_withdraw`, a view sent as a transaction, a repeated init and NEAR sent to the token change no balance; `storage_unregister` changes none but the caller's | every such operation in a round of its own | `P4_who_can_lower` |
| `P5.unregister_refused` | `storage_unregister` without `force: true` by an account with a positive balance changes no balance and not the supply | every such call in a round of its own | `P5_unregister_refused` |

## What no monitor looks at

- NEAR amounts: the storage deposit a registration keeps, the refunds, the storage minimum, the
  token's own solvency (`P5_storage_deposit`, `P5_storage_solvent`, the NEAR side of
  `P5_unregister_*`).
- Gas: how much the token attaches to `ft_on_transfer` and to its settlement callback.
- Events, error texts, `ft_metadata`.
- Methods outside NEP-141 and NEP-145 (mint, burn, pause, fees, upgrades), unless your config calls
  them in `setup`. The certificate lists the exported methods no call reached.

## The vacuity guard

A monitor that judged nothing has not passed. The certificate counts the checks of every monitor,
and the verdict is INCONCLUSIVE, never PASS, when

- a monitor made zero checks (for example "no ft_transfer_call was accepted in any trace"), or
- a kind of step the checks depend on never happened: the supply was never positive, no transfer of
  a positive amount succeeded, no transfer failed, no settlement refunded anything, no settlement
  kept the whole amount, no stranger tried the callback for a positive amount, no balance ever
  fell, or
- the token could not be set up, or a trace did not finish.

The reason is written in the certificate in words.
