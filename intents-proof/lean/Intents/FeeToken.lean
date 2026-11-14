/-
  T5: the token assumption is needed.

  A fee-on-transfer token: `ft_transfer` / `ft_transfer_call` keep `fee` out of the transferred
  amount (burned here), while the notification to the receiver and the settlement callback still
  carry the full amount. This is not a NEP-141 standard token; it is modelled as a variant of
  the token step. With it the backing statement fails: the contract credits the reported amount,
  not the amount that arrived.
-/
import Intents.Examples

namespace Intents
open ProvedFT

/-- The standard token, except that a transfer of `x` credits the receiver `x - fee`. -/
def feeExec (E : Env) (fee : Nat) (s : St) (r : Rcpt) : Option Out :=
  match exec E s r with
  | none => none
  | some o =>
    match r.m with
    | .ft_transfer rc x _ | .ft_transfer_call rc x _ _ =>
      if fee ≤ x then
        some { o with st := { o.st with accts := set o.st.accts rc (bal o.st.accts rc - fee),
                                        supply := o.st.supply - fee } }
      else none
    | _ => some o

namespace Examples

/-- **T5. With a fee-on-transfer token the ledger is not covered.** The shortest run: one
    deposit of 100 with a fee of 1 — the token's `ft_transfer_call`, the contract's
    `ft_on_transfer`, the token's settlement. Afterwards nothing is in flight, the ledger says
    100 and the contract holds 99. -/
theorem T5_fee_token_breaks_backing :
    let S := run K (feeExec E 1) S0 deposit
    S.pend = [] ∧ S.unwrap = [] ∧ S.outbox = [] ∧ S.resolves.length = 0 ∧
    total S.L.bals = 100 ∧ bal S.c.accts K.me = 99 ∧
    ¬ (total S.L.bals ≤ bal S.c.accts K.me) := by
  decide

/-- The same three steps with the standard token: 100 and 100 (`T1_ledger_covered` applies). -/
theorem T5_standard_token_same_run :
    let S := run K (exec E) S0 deposit
    total S.L.bals = 100 ∧ bal S.c.accts K.me = 100 := by
  decide

/-- With a zero fee the variant is the standard token on this run. -/
example :
    let S := run K (feeExec E 0) S0 deposit
    total S.L.bals = 100 ∧ bal S.c.accts K.me = 100 := by
  decide

end Examples
end Intents
