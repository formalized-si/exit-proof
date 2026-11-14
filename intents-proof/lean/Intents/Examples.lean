/-
  Non-vacuity: concrete runs of the model on which the hypotheses of the theorems hold and their
  conclusions say something. Nothing here is used by the theorems.

  The world: token `token.near` with accounts `intents.near` (the contract), `alice.near`
  (holds 100) and `bob.near`; `carol.near` is not registered on the token.
-/
import Intents.Exact

namespace Intents.Examples
open ProvedFT Intents

def E : Env :=
  { self := "token.near", minBal := 1250000000000000000000, base := 0, entry := fun _ => 0,
    cap := 1000000000000000000000000000000000 }

def K : Cfg := { tok := E, me := "intents.near" }

/-- The token after its `new`: three registered accounts, `alice.near` holds 100. -/
def c0 : St :=
  { accts := [("intents.near", 0), ("alice.near", 100), ("bob.near", 0)], supply := 100,
    near := 5000000000000000000000 }

def S0 : World := { c := c0 }

theorem init0 : Init K S0 := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨by decide, by decide, by decide, trivial⟩
  · rfl
  · decide
  · decide
  · decide

theorem reach0 (l : List Step) : Reach K (run K (exec E) S0 l) :=
  reach_run (Reach.init S0 init0) l

/-- `alice.near` deposits 100 with `ft_transfer_call(intents.near, 100, "")`: the token's
    transfer, the contract's `ft_on_transfer`, the token's settlement. -/
def deposit : List Step :=
  [ .tokCall "alice.near" 1 (.ft_transfer_call "intents.near" 100 none "") [],
    .onTransfer 0 "alice.near" true,
    .tokResolve 0 .failed ]

/-- After the deposit: the ledger credits `alice.near` 100, the contract holds 100 tokens,
    nothing is in flight. (The `.failed` given to the settlement step is ignored: the callback
    reads the contract's own answer `"0"`.) -/
example :
    let S := run K (exec E) S0 deposit
    S.L.bals = [("alice.near", 100)] ∧ S.L.supply = 100 ∧
    bal S.c.accts "intents.near" = 100 ∧ bal S.c.accts "alice.near" = 0 ∧
    S.pend.length = 0 ∧ S.outbox.length = 0 ∧ S.resolves.length = 0 := by
  decide

/-- Between the token's transfer and `ft_on_transfer` the 100 tokens are already in the
    contract's balance and nothing is credited: the state `T3_covered` talks about. -/
example :
    let S := run K (exec E) S0 (deposit.take 1)
    S.pend.map Pend.raw = [("alice.near", "intents.near", 100)] ∧
    S.pend.map Pend.ann = [.dep none] ∧
    bal S.c.accts "intents.near" = 100 ∧ S.L.supply = 0 ∧ uncredited S = 100 := by
  decide

/-- T1 on this run (every prefix of it is reachable). -/
example (n : Nat) :
    let S := run K (exec E) S0 (deposit.take n)
    total S.L.bals ≤ bal S.c.accts "intents.near" :=
  T1_ledger_covered K _ (reach0 _)

/-- The deposit fails inside the contract (`ok = false`: paused, bad `msg`, out of gas): no
    credit, and the token's settlement returns the 100 to `alice.near`. -/
example :
    let S := run K (exec E) S0
      [ .tokCall "alice.near" 1 (.ft_transfer_call "intents.near" 100 none "") [],
        .onTransfer 0 "alice.near" false,
        .tokResolve 0 (.ok []) ]
    S.L.supply = 0 ∧ bal S.c.accts "intents.near" = 0 ∧ bal S.c.accts "alice.near" = 100 := by
  decide

/-- A plain withdrawal of 40 to `bob.near`: debit, `ft_transfer`, `ft_resolve_withdraw`. -/
def withdrawPlain : List Step :=
  deposit ++
  [ .ftWithdraw (.method "alice.near") { owner := "alice.near", receiver := "bob.near", amount := 40 },
    .tokXfer 0,
    .resolveWd 0 ]

/-- The ready callback after the transfer: all 40 left, nothing to refund. -/
example :
    let S := run K (exec E) S0 (withdrawPlain.take 5)
    S.resolves.map (fun r => (r.owner, r.amount, r.isCall, r.left, r.refund)) =
      [("alice.near", 40, false, 40, 0)] ∧
    S.L.bals = [("alice.near", 60)] ∧ bal S.c.accts "intents.near" = 60 ∧
    debitedInFlight S = 40 ∧ movedOut S = 40 := by
  decide

/-- After the resolve: ledger 60, held 60, `bob.near` has 40. Equality. -/
example :
    let S := run K (exec E) S0 withdrawPlain
    S.L.bals = [("alice.near", 60)] ∧ S.L.supply = 60 ∧
    bal S.c.accts "intents.near" = 60 ∧ bal S.c.accts "bob.near" = 40 ∧
    S.resolves.length = 0 := by
  decide

/-- T2 on this run, at the resolve step. -/
example :
    let S := run K (exec E) S0 (withdrawPlain.take 5)
    ∃ r, S.resolves[0]? = some r ∧
      bal (stdStep K S (.resolveWd 0)).L.bals r.owner = bal S.L.bals r.owner + r.refund ∧
      (r.amount - r.refund = r.left ∨
        (r.isCall = true ∧ r.res = PR.failed ∧ r.left = 0 ∧ r.refund = 0)) := by
  intro S
  have hr : ∃ r, S.resolves[0]? = some r := by
    have : S.resolves.length = 1 := by decide
    cases h : S.resolves[0]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some r => exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hr
  obtain ⟨_, h2, _, _, h5⟩ := T2_settles K S (reach0 _) 0 r hr
  exact ⟨r, hr, h2, h5⟩

/-- The plain transfer fails on the token (`carol.near` is not registered there): the resolve
    refunds all 40; `alice.near` is back at 100 and the contract still holds 100. -/
example :
    let S := run K (exec E) S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "carol.near", amount := 40 },
        .tokXfer 0,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 100)] ∧ bal S.c.accts "intents.near" = 100 := by
  decide

/-- A withdrawal of 40 with `ft_transfer_call` to `bob.near`, whose `ft_on_transfer` reports 15
    unused: the token moves 15 back, its settlement returns `"25"`, and `ft_resolve_withdraw`
    credits `alice.near` 15. -/
def withdrawCall : List Step :=
  deposit ++
  [ .ftWithdraw (.method "alice.near")
      { owner := "alice.near", receiver := "bob.near", amount := 40, msg := some "m" },
    .tokXfer 0,
    .tokResolve 0 (.ok (encU128 15)),
    .resolveWd 0 ]

/-- While `bob.near` holds the 40: the ledger is at 60 and the contract holds 60. -/
example :
    let S := run K (exec E) S0 (withdrawCall.take 5)
    S.pend.map Pend.raw = [("intents.near", "bob.near", 40)] ∧
    S.L.supply = 60 ∧ bal S.c.accts "intents.near" = 60 ∧ bal S.c.accts "bob.near" = 40 ∧
    debitedInFlight S = 40 ∧ movedOut S = 40 := by
  decide

/-- After the token's settlement: 15 came back, 25 left; the callback is ready to refund 15. -/
example :
    let S := run K (exec E) S0 (withdrawCall.take 6)
    S.resolves.map (fun r => (r.owner, r.amount, r.isCall, r.left, r.refund)) =
      [("alice.near", 40, true, 25, 15)] ∧
    bal S.c.accts "intents.near" = 75 ∧ bal S.c.accts "bob.near" = 25 := by
  decide

/-- After the resolve: ledger 75 = held 75. -/
example :
    let S := run K (exec E) S0 withdrawCall
    S.L.bals = [("alice.near", 75)] ∧ S.L.supply = 75 ∧ bal S.c.accts "intents.near" = 75 := by
  decide

/-- The receiver answers garbage: the token treats everything as unused, takes the 40 back and
    returns `"0"`; the contract refunds all 40. -/
example :
    let S := run K (exec E) S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40, msg := some "m" },
        .tokXfer 0,
        .tokResolve 0 (.ok [1, 2, 3]),
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 100)] ∧ bal S.c.accts "intents.near" = 100 ∧
    bal S.c.accts "bob.near" = 0 := by
  decide

/-- The token's settlement callback is dropped (out of gas): `bob.near` keeps the 40, the
    contract's callback reads a failure and refunds nothing. Ledger 60 = held 60. -/
example :
    let S := run K (exec E) S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40, msg := some "m" },
        .tokXfer 0,
        .tokResolveFails 0,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 60)] ∧ bal S.c.accts "intents.near" = 60 ∧
    bal S.c.accts "bob.near" = 40 := by
  decide

/-- The contract's own resolve callback does not run after a failed plain transfer
    (`T2_no_callback`): `alice.near` stays debited 40 although nothing left; the contract holds
    100 against a ledger of 60. The ledger is covered; 40 tokens are assigned to nobody. -/
example :
    let S := run K (exec E) S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "carol.near", amount := 40 },
        .tokXfer 0,
        .resolveWdFails 0 ])
    S.L.bals = [("alice.near", 60)] ∧ bal S.c.accts "intents.near" = 100 ∧
    S.resolves.length = 0 := by
  decide

/-- T4: `bob.near` cannot start a withdrawal from `alice.near`'s balance with `ft_withdraw`. -/
example :
    let S := run K (exec E) S0 deposit
    stdStep K S (.ftWithdraw (.method "bob.near")
      { owner := "alice.near", receiver := "bob.near", amount := 40 }) = S := by
  intro S
  simp [stdStep, step, startWithdraw, Via.ok]

/-- T4: a holder of `UnrestrictedWithdrawer` can (`ft_force_withdraw`), and a locked account
    does not stop it. -/
example :
    let S := run K (exec E) S0 (deposit ++
      [ .admin (.acl [("dao.near", .DAO), ("ops.near", .UnrestrictedWithdrawer)]),
        .admin (.lock "dao.near" "alice.near"),
        .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40 },
        .ftWithdraw (.force "ops.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40 } ])
    S.L.ctl.locked = ["alice.near"] ∧ S.L.bals = [("alice.near", 60)] ∧
    S.outbox.map Wd.amount = [40] := by
  decide

/-- T4: pausing `ft_withdraw` blocks the account's own withdrawal. -/
example :
    let S := run K (exec E) S0 (deposit ++
      [ .admin (.acl [("dao.near", .DAO)]),
        .admin (.pause "dao.near" "ft_withdraw"),
        .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40 } ])
    S.L.bals = [("alice.near", 100)] ∧ S.outbox.length = 0 := by
  decide

/-- An internal move (an `mt_transfer` by `alice.near`) keeps the total. -/
example :
    let S := run K (exec E) S0 (deposit ++ [ .move .owner "alice.near" "bob.near" 30 ])
    S.L.bals = [("alice.near", 70), ("bob.near", 30)] ∧ S.L.supply = 100 := by
  decide

/-- The storage-deposit path of an `FtWithdraw` intent: `do_ft_withdraw` after a successful
    wNEAR unwrap sends `storage_deposit(carol.near)` and `ft_transfer` in one receipt; the
    transfer now succeeds because `carol.near` gets registered. -/
example :
    let S := run K (exec E) S0 (deposit ++
      [ .ftWithdraw .intent
          { owner := "alice.near", receiver := "carol.near", amount := 40,
            sd := some 1250000000000000000000 },
        .doFtWithdraw 0 true,
        .tokXfer 0,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 60)] ∧ bal S.c.accts "intents.near" = 60 ∧
    bal S.c.accts "carol.near" = 40 := by
  decide

/-! ### The exact books (`T1_exact`, `T1_equality`) -/

theorem sane : E.Sane := ⟨fun _ => Nat.zero_le _, by decide, by decide⟩

/-- The run `withdrawCall` (deposit, withdrawal with `ft_transfer_call`, partial refusal,
    resolve) starts with an empty token balance and has no losing step. -/
theorem withdrawCall_exact : ReachExact K (run K (exec E) S0 withdrawCall) := by
  refine reachExact_run (ReachExact.init S0 init0 (by decide)) withdrawCall ?_
  show Lossless K S0 _ ∧ Lossless K _ _ ∧ Lossless K _ _ ∧ Lossless K _ _ ∧ Lossless K _ _ ∧
    Lossless K _ _ ∧ Lossless K _ _ ∧ True
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  · intro x memo h; exact Method.noConfusion h
  · intro r hr hbad
    have h1 : ((run K (exec E) S0 (withdrawCall.take 6)).resolves.map Rs.left)[0]? =
        some r.left := by
      rw [List.getElem?_map]
      exact congrArg (Option.map Rs.left) hr
    have h2 : (run K (exec E) S0 (withdrawCall.take 6)).resolves.map Rs.left = [25] := by decide
    rw [h2] at h1
    simp at h1
    omega

/-- `T1_exact` on every state of that run would say: ledger + owed = held. At its end (a quiet
    state) `T1_equality` gives ledger total = tokens held; both are 75. -/
example :
    let S := run K (exec E) S0 withdrawCall
    total S.L.bals = bal S.c.accts K.me ∧ total S.L.bals = 75 := by
  intro S
  refine ⟨T1_equality K sane S withdrawCall_exact ?_, by decide⟩
  refine ⟨by decide, by decide, ?_, ?_⟩
  · have : S.resolves.length = 0 := by decide
    exact List.eq_nil_of_length_eq_zero this
  · have : S.pend.length = 0 := by decide
    rw [List.eq_nil_of_length_eq_zero this]
    intro e he; simp at he

/-- A gift is a losing step: after a plain `ft_transfer` of 7 to the contract the ledger is
    covered but not equal (0 < 7), and `Lossless` excludes exactly this step. -/
example :
    let st : Step := .tokCall "alice.near" 1 (.ft_transfer "intents.near" 7 none) []
    let S := run K (exec E) S0 [st]
    total S.L.bals = 0 ∧ bal S.c.accts K.me = 7 ∧ ¬ Lossless K S0 st := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact h 7 none rfl

end Intents.Examples
