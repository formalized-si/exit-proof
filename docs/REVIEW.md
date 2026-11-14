# Independent adversarial review of the two proofs (2026-11-12)

The reviewer took no part in the proofs; the task was to find where the statements are weaker than claimed.
The files of the review: `../pool-proof/lean/Review/PoolVacuity.lean` and
`../wnear-proof/lean/Review/WNearVacuity.lean`.

## Verdict

| Target | Verdict |
|---|---|
| pool-proof (`exit_guarantee`) | correct, with corrections to the wording |
| wnear-proof (`exit_always`) | correct, with corrections; for mainnet the headline is `T_exit` under `Inv` |

Both are theorems about a model, tied to the deployed bytes by hash equality and execution.

## What was confirmed

- **Non-vacuity.** For both theorems concrete reachable worlds were built by real steps (deposits, stake,
  epochs, rewards, calls by others, a callback with a partial refund), the theorems were applied to them, and
  the conclusion is non-trivial (alice withdraws 101.000000000000005555555556 NEAR; bob — 3 NEAR + 1 yocto).
  The checks are `decide +kernel`; deliberately false statements are rejected. PUA was shown to be necessary:
  without the return of the stake the withdrawal fails.
- **Hygiene.** No `sorry/admit/native_decide/implemented_by/extern/unsafe/opaque/macro/syntax/elab/set_option`
  in the proofs; `#print axioms` agrees with the reports; `leanchecker --fresh` passes (~52 s each); the
  independent kernel nanoda_bin 0.4.19 passes on the export (60 236 and 59 848 declarations); `sorryAx` is not
  used.
- **The model against the source.** The five riskiest places of each contract agree line by line; the
  abstractions found (gas, the type of the fee) widen the model in the safe direction.

How to repeat these checks: section 8 of `../pool-proof/REPORT.md` and of `../wnear-proof/REPORT.md`
(`lake build` compiles the two files above; `lean/kernel-check.sh` runs `leanchecker --fresh` and nanoda).

## Corrections to the wording (adopted in `../tools/proofs.json`)

Pool: "In the model: from any state reachable from `new()` with no outflow from the pool account, `unstake_all`
by u succeeds at once, when u has stake, and leaves ≥ `get_account_total_balance(u)`. Then, if u calls nothing
itself, in any state with the epoch ≥ +4 in which the protocol has returned the stake (PUA), `withdraw_all`
succeeds and issues a transfer to u of at least that amount. That PUA comes to hold is an assumption about the
protocol, not a theorem." The theorem carries the bound `ncalls < 10^12` on the number of calls the pool has
received.

wNEAR: "In any state with `Inv`, a registered u ≠ wrap.near that calls `near_withdraw(b)` with 1 yocto, where b
is the balance at the moment of execution, always succeeds, and the contract sends u a transfer of b + 1. For
mainnet this is conditional: solvency was checked, `supply = Σ balances` for the current state was not." `T_exit`
needs the full invariant `Inv`.
