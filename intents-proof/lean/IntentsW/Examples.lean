/-
  Non-vacuity: concrete runs of the wNEAR world on which the hypotheses of the theorems hold and
  their conclusions say something, and the rows of the failure table of NOTES.md, section 12.
  Nothing here is used by the theorems.

  The world: wNEAR at `wrap.near` with accounts `intents.near` (the contract), `alice.near`
  (holds 100) and `bob.near`; `carol.near` is not registered on wNEAR. Small numbers: the storage
  deposit of wNEAR is 10 here.
-/
import IntentsW.Native
import IntentsW.TokenSide

namespace IntentsW.Examples
open ProvedFT (bal total)
open Intents IntentsW

def E : WNear.Env :=
  { self := "wrap.near", minBal := 10, base := 0, entry := fun _ => 0, cap := 1000000 }

def K : Cfg := { tok := E, me := "intents.near" }

/-- wNEAR: three registered accounts, `alice.near` holds 100; 1000 NEAR units on the account. -/
def c0 : WNear.St :=
  { accts := [("intents.near", 0), ("alice.near", 100), ("bob.near", 0)], supply := 100,
    near := 1000 }

def S0 : World := { c := c0 }

deriving instance DecidableEq for Intents.Pend

theorem sane : E.Sane := ⟨by decide, fun _ => Nat.zero_le _, by decide, by decide⟩

theorem init0 : Init K S0 := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨by decide, by decide, by decide, trivial⟩
  · rfl
  · decide
  · decide
  · decide
  · intro e he; cases he

theorem reach0 (l : List Step) : Reach K (run K S0 l) :=
  reach_run (Reach.init S0 init0) l

theorem me_ne : K.me ≠ K.tok.self := by decide

/-! ### Deposits (W1, W3) -/

/-- `alice.near` deposits 100 wNEAR with `ft_transfer_call(intents.near, 100, "")`: wNEAR's
    transfer, the contract's `ft_on_transfer`, wNEAR's settlement. -/
def deposit : List Step :=
  [ .tokCall "alice.near" 1 (.ft_transfer_call "intents.near" 100) [],
    .onTransfer 0 "alice.near" true,
    .tokResolve 0 .failed ]

/-- After the deposit: the ledger credits `alice.near` 100, the contract holds 100 wNEAR,
    nothing is in flight. (The `.failed` given to the settlement step is ignored: the callback
    reads the contract's own answer `"0"`.) -/
example :
    let S := run K S0 deposit
    S.L.bals = [("alice.near", 100)] ∧ S.L.supply = 100 ∧
    WNear.bal S.c.accts "intents.near" = 100 ∧ WNear.bal S.c.accts "alice.near" = 0 ∧
    S.pend.length = 0 ∧ S.outbox.length = 0 ∧ S.resolves.length = 0 := by
  decide

/-- Between wNEAR's transfer and `ft_on_transfer` the 100 wNEAR are already in the contract's
    balance and nothing is credited: the state `W3_covered` talks about, and the new callback
    `W3_arrival` talks about. -/
example :
    let S := run K S0 (deposit.take 1)
    S.pend.map Pend.raw = [("alice.near", "intents.near", 100)] ∧
    S.pend.map Pend.ann = [.dep none] ∧
    WNear.bal S.c.accts "intents.near" = 100 ∧ S.L.supply = 0 ∧ uncredited S = 100 := by
  decide

/-- `W3_covered` and `W3_arrival` on that state. -/
example :
    let S := run K S0 (deposit.take 1)
    (∃ L', credit S.L "alice.near" 100 = some L') ∧
    ∃ p d x rs, deposit.head? = some (Step.tokCall p d (.ft_transfer_call K.me x) rs) ∧ 0 < x := by
  intro S
  have hpi : S.pend[0]? = some ⟨"alice.near", "intents.near", 100, .dep none⟩ := by decide
  refine ⟨(W3_covered K S (reach0 _) 0 _ hpi rfl "alice.near").2, ?_⟩
  obtain ⟨p, d, x, rs, h1, _, _, hx, _⟩ := W3_arrival K S0
    (.tokCall "alice.near" 1 (.ft_transfer_call "intents.near" 100) [])
    ⟨"alice.near", "intents.near", 100, .dep none⟩ (by decide) rfl (by decide)
  exact ⟨p, d, x, rs, by rw [← h1]; rfl, hx⟩

/-- W1 on every prefix of a run (each prefix is reachable). -/
example (l : List Step) (n : Nat) :
    let S := run K S0 (l.take n)
    total S.L.bals ≤ WNear.bal S.c.accts "intents.near" :=
  W1_ledger_covered K _ (reach0 _)

/-- The credit step is the first case of `W3_credit_only_on_arrival`: it raises the total. -/
example :
    let S := run K S0 (deposit.take 1)
    S.L.supply < (step K S (.onTransfer 0 "alice.near" true)).L.supply := by
  decide

/-- The deposit fails inside the contract (`ok = false`: paused, bad `msg`, out of gas): no
    credit, and wNEAR's settlement returns the 100 to `alice.near`. -/
example :
    let S := run K S0
      [ .tokCall "alice.near" 1 (.ft_transfer_call "intents.near" 100) [],
        .onTransfer 0 "alice.near" false,
        .tokResolve 0 (.ok (some 0)) ]
    S.L.supply = 0 ∧ WNear.bal S.c.accts "intents.near" = 0 ∧
    WNear.bal S.c.accts "alice.near" = 100 := by
  decide

/-- The deposit fails inside the contract and wNEAR's settlement callback is dropped too: no
    credit, the 100 wNEAR stay in the contract's balance, assigned to nobody. -/
example :
    let S := run K S0
      [ .tokCall "alice.near" 1 (.ft_transfer_call "intents.near" 100) [],
        .onTransfer 0 "alice.near" false,
        .tokResolveFails 0 ]
    S.L.supply = 0 ∧ WNear.bal S.c.accts "intents.near" = 100 ∧ S.pend.length = 0 := by
  decide

/-! ### Withdrawals of wNEAR as a token (W2) -/

/-- A plain withdrawal of 40 wNEAR to `bob.near`: debit, `ft_transfer`, `ft_resolve_withdraw`. -/
def withdrawPlain : List Step :=
  deposit ++
  [ .ftWithdraw (.method "alice.near") { owner := "alice.near", receiver := "bob.near", amount := 40 },
    .tokXfer 0,
    .resolveWd 0 ]

/-- The ready callback after the transfer: all 40 left, nothing to refund. -/
example :
    let S := run K S0 (withdrawPlain.take 5)
    S.resolves.map (fun r => (r.owner, r.amount, r.isCall, r.left, r.refund)) =
      [("alice.near", 40, false, 40, 0)] ∧
    S.L.bals = [("alice.near", 60)] ∧ WNear.bal S.c.accts "intents.near" = 60 ∧
    debitedInFlight S = 40 ∧ movedOut S = 40 := by
  decide

/-- After the resolve: ledger 60, held 60, `bob.near` has 40. -/
example :
    let S := run K S0 withdrawPlain
    S.L.bals = [("alice.near", 60)] ∧ S.L.supply = 60 ∧
    WNear.bal S.c.accts "intents.near" = 60 ∧ WNear.bal S.c.accts "bob.near" = 40 ∧
    S.resolves.length = 0 := by
  decide

/-- `W1_can_pay` on this run: the state with the withdrawal in the outbox. -/
example :
    let S := run K S0 (withdrawPlain.take 4)
    S.outbox.map Wd.amount = [40] ∧ total S.L.bals + 40 ≤ WNear.bal S.c.accts K.me := by
  intro S
  have hj : S.outbox[0]? =
      some { owner := "alice.near", receiver := "bob.near", amount := 40 } := by decide
  exact ⟨by decide, W1_can_pay K S (reach0 _) 0 _ hj⟩

/-- `W2_settles` on this run, at the resolve step. -/
example :
    let S := run K S0 (withdrawPlain.take 5)
    ∃ r, S.resolves[0]? = some r ∧
      bal (step K S (.resolveWd 0)).L.bals r.owner = bal S.L.bals r.owner + r.refund ∧
      (r.amount - r.refund = r.left ∨
        (r.isCall = true ∧ r.res = ProvedFT.PR.failed ∧ r.left = 0 ∧ r.refund = 0)) := by
  intro S
  have hr : ∃ r, S.resolves[0]? = some r := by
    have : S.resolves.length = 1 := by decide
    cases h : S.resolves[0]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some r => exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hr
  obtain ⟨_, h2, _, _, h5⟩ := W2_settles K S (reach0 _) 0 r hr
  exact ⟨r, hr, h2, h5⟩

/-- The plain transfer fails on wNEAR (`carol.near` is not registered there): the resolve
    refunds all 40; `alice.near` is back at 100 and the contract still holds 100. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "carol.near", amount := 40 },
        .tokXfer 0,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 100)] ∧ WNear.bal S.c.accts "intents.near" = 100 := by
  decide

/-- A withdrawal of 40 with `ft_transfer_call` to `bob.near`, whose `ft_on_transfer` reports 15
    unused: wNEAR moves 15 back, its settlement returns `"25"`, and `ft_resolve_withdraw`
    credits `alice.near` 15. -/
def withdrawCall : List Step :=
  deposit ++
  [ .ftWithdraw (.method "alice.near")
      { owner := "alice.near", receiver := "bob.near", amount := 40, msg := some "m" },
    .tokXfer 0,
    .tokResolve 0 (.ok (some 15)),
    .resolveWd 0 ]

/-- After wNEAR's settlement: 15 came back, 25 left; the callback is ready to refund 15. -/
example :
    let S := run K S0 (withdrawCall.take 6)
    S.resolves.map (fun r => (r.owner, r.amount, r.isCall, r.left, r.refund)) =
      [("alice.near", 40, true, 25, 15)] ∧
    WNear.bal S.c.accts "intents.near" = 75 ∧ WNear.bal S.c.accts "bob.near" = 25 := by
  decide

/-- After the resolve: ledger 75 = held 75. -/
example :
    let S := run K S0 withdrawCall
    S.L.bals = [("alice.near", 75)] ∧ S.L.supply = 75 ∧
    WNear.bal S.c.accts "intents.near" = 75 := by
  decide

/-- The receiver answers garbage: wNEAR treats everything as unused, takes the 40 back and
    returns `"0"`; the contract refunds all 40. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40, msg := some "m" },
        .tokXfer 0,
        .tokResolve 0 (.ok none),
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 100)] ∧ WNear.bal S.c.accts "intents.near" = 100 ∧
    WNear.bal S.c.accts "bob.near" = 0 := by
  decide

/-- wNEAR's settlement callback is dropped (out of gas): `bob.near` keeps the 40, the
    contract's callback reads a failure and refunds nothing. Ledger 60 = held 60. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40, msg := some "m" },
        .tokXfer 0,
        .tokResolveFails 0,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 60)] ∧ WNear.bal S.c.accts "intents.near" = 60 ∧
    WNear.bal S.c.accts "bob.near" = 40 := by
  decide

/-- The contract's own resolve callback does not run after a failed plain transfer
    (`W2_no_callback`): `alice.near` stays debited 40 although nothing left; the contract holds
    100 against a ledger of 60. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "carol.near", amount := 40 },
        .tokXfer 0,
        .resolveWdFails 0 ])
    S.L.bals = [("alice.near", 60)] ∧ WNear.bal S.c.accts "intents.near" = 100 ∧
    S.resolves.length = 0 := by
  decide

/-! ### The native path (N1–N3) -/

/-- A `NativeWithdraw` of 30 by `alice.near` to `bob.near`: the debit, `near_withdraw(30)` on
    wNEAR, `do_native_withdraw`. -/
def native : List Step :=
  deposit ++
  [ .unwrap "alice.near" 30 (.native "bob.near"),
    .nearWithdraw 0,
    .doJob 0 true ]

/-- After the intent: `alice.near` is debited 30, the `near_withdraw` is in flight, wNEAR is
    untouched (the contract still holds 100 against a ledger of 70). -/
example :
    let S := run K S0 (native.take 4)
    S.L.bals = [("alice.near", 70)] ∧ S.L.supply = 70 ∧
    S.jobs = [⟨"alice.near", 30, .native "bob.near"⟩] ∧
    WNear.bal S.c.accts "intents.near" = 100 ∧ S.uDebited = 30 := by
  decide

/-- After `near_withdraw`: exactly 30 wNEAR burned (the contract's balance and wNEAR's supply
    both 70), wNEAR sent the contract 31 = 30 + the attached yocto, the callback is ready. -/
example :
    let S := run K S0 (native.take 5)
    WNear.bal S.c.accts "intents.near" = 70 ∧ S.c.supply = 70 ∧ S.c.near = 971 ∧
    S.paid = [("intents.near", 31)] ∧
    S.ready = [⟨⟨"alice.near", 30, .native "bob.near"⟩, true⟩] ∧
    S.uBurned = 30 ∧ S.nGot = 31 ∧ S.L.bals = [("alice.near", 70)] := by
  decide

/-- After the callback: 30 NEAR sent on; ledger 70 = held 70; nothing in flight. The books:
    debited 30 = burned 30, received 31, sent on 30. -/
example :
    let S := run K S0 native
    S.L.bals = [("alice.near", 70)] ∧ S.L.supply = 70 ∧
    WNear.bal S.c.accts "intents.near" = 70 ∧
    S.jobs.length = 0 ∧ S.ready.length = 0 ∧
    (S.uDebited, S.uBurned, S.uKept, S.nGot, S.nFwd) = (30, 30, 0, 31, 30) := by
  decide

/-- `N1_start` and `N1_debit` on this run. -/
example :
    let S := run K S0 deposit
    let S' := step K S (.unwrap "alice.near" 30 (.native "bob.near"))
    S'.jobs = S.jobs ++ [⟨"alice.near", 30, .native "bob.near"⟩] ∧ S'.c = S.c ∧
    bal S'.L.bals "alice.near" + 30 = bal S.L.bals "alice.near" := by
  intro S S'
  have hs : ∃ L', startUnwrap S.L "alice.near" 30 = some L' := by
    cases h : startUnwrap S.L "alice.near" 30 with
    | some L' => exact ⟨L', rfl⟩
    | none =>
      have hne : (startUnwrap S.L "alice.near" 30).isSome = true := by decide
      rw [h] at hne; exact absurd hne (by simp)
  obtain ⟨L', hs⟩ := hs
  obtain ⟨h1, h2, h3, _, _⟩ := N1_start K S "alice.near" 30 (.native "bob.near") rfl L' hs
  obtain ⟨_, h4, _⟩ := N1_debit S.L L' "alice.near" 30 hs
  refine ⟨h2, h3, ?_⟩
  show bal (step K S (.unwrap "alice.near" 30 (.native "bob.near"))).L.bals "alice.near" + 30 = _
  rw [h1]; exact h4

/-- `N2_unwrap_succeeds`, `N2_burn_is_debit` and `W1_can_unwrap` on this run: with the
    `near_withdraw` in flight, the receipt succeeds and burns exactly the 30 debited. -/
example :
    let S := run K S0 (native.take 4)
    let S' := step K S (.nearWithdraw 0)
    WNear.bal S'.c.accts K.me + 30 = WNear.bal S.c.accts K.me ∧ S'.c.supply + 30 = S.c.supply ∧
    S'.paid = S.paid ++ [(K.me, 31)] := by
  intro S S'
  have hj : S.jobs[0]? = some ⟨"alice.near", 30, .native "bob.near"⟩ := by decide
  obtain ⟨h1, h2, h3, _, _⟩ := N2_burn_is_debit K sane S (reach0 _) (by decide) 0 _ hj
  exact ⟨h1, h2, h3⟩

/-- `N3_forward` on this run: the callback sends on exactly the 30 debited. -/
example :
    let S := run K S0 (native.take 5)
    (step K S (.doJob 0 true)).nFwd = S.nFwd + 30 ∧ (step K S (.doJob 0 true)).L = S.L := by
  intro S
  have hk : S.ready[0]? = some ⟨⟨"alice.near", 30, .native "bob.near"⟩, true⟩ := by decide
  obtain ⟨h1, _, _, _, h5, _⟩ := N3_forward K S 0 _ hk true
  exact ⟨(h5 ⟨rfl, rfl⟩).1, h1⟩

/-- `N3_books` and `N3_near_le` on every state of every run. -/
example (l : List Step) :
    let S := run K S0 l
    S.nFwd ≤ S.uBurned ∧ S.uBurned ≤ S.uDebited ∧ S.uBurned ≤ S.nGot ∧ S.nFwd ≤ S.nGot :=
  N3_near_le K _ (reach0 _)

/-- A `StorageDeposit` intent whose `contract_id` is wNEAR itself, for the unregistered
    `carol.near`: the unwrap, then `storage_deposit(carol.near)` with the 10 NEAR registers
    `carol.near` on wNEAR. No wNEAR balance changes in that last receipt. -/
example :
    let S := run K S0 (deposit ++
      [ .unwrap "alice.near" 10 (.storage "wrap.near" "carol.near"),
        .nearWithdraw 0,
        .doJob 0 true,
        .meStorageDeposit "carol.near" 10 ])
    S.L.bals = [("alice.near", 90)] ∧ WNear.bal S.c.accts "intents.near" = 90 ∧
    WNear.get S.c.accts "carol.near" = some 0 ∧ S.paid = [("intents.near", 11)] := by
  decide

/-- The same for `bob.near`, who is registered already: wNEAR sends the whole deposit back to
    the contract (the second transfer in `paid`); the debit of 10 stays. -/
example :
    let S := run K S0 (deposit ++
      [ .unwrap "alice.near" 10 (.storage "wrap.near" "bob.near"),
        .nearWithdraw 0,
        .doJob 0 true,
        .meStorageDeposit "bob.near" 10 ])
    S.L.bals = [("alice.near", 90)] ∧ WNear.bal S.c.accts "intents.near" = 90 ∧
    S.paid = [("intents.near", 11), ("intents.near", 10)] := by
  decide

/-! ### A withdrawal of wNEAR with a storage deposit -/

/-- An `FtWithdraw` intent of 40 wNEAR to the unregistered `carol.near` with
    `storage_deposit = 10`. -/
def wsd : Wd := { owner := "alice.near", receiver := "carol.near", amount := 40, sd := some 10 }

def withdrawSd : List Step :=
  deposit ++
  [ .ftWithdraw .intent wsd,
    .nearWithdraw 0,
    .doJob 0 true,
    .tokXfer 0,
    .resolveWd 0 ]

/-- The intent debits the same ledger twice: 40 + 10 (`W2_debit`); one unwrap of 10 in flight. -/
example :
    let S := run K S0 (withdrawSd.take 4)
    S.L.bals = [("alice.near", 50)] ∧ S.L.supply = 50 ∧
    S.jobs.map (fun u => (u.owner, u.amount)) = [("alice.near", 10)] ∧ S.uDebited = 10 ∧
    debitedInFlight S = 50 := by
  decide

/-- The end: 10 burned, 40 sent to `carol.near` (registered by the storage deposit in the same
    receipt as the transfer). Ledger 50 = held 50. -/
example :
    let S := run K S0 withdrawSd
    S.L.bals = [("alice.near", 50)] ∧ WNear.bal S.c.accts "intents.near" = 50 ∧
    WNear.bal S.c.accts "carol.near" = 40 ∧ S.c.supply = 90 ∧
    (S.uDebited, S.uBurned, S.uKept, S.nGot, S.nFwd) = (10, 10, 0, 11, 10) := by
  decide

/-! ### The failure table (NOTES.md, section 12) -/

/-- Row "the intent itself fails": nothing changes (here: more than the balance; `intents`
    paused; the account locked). -/
example :
    (let S := run K S0 deposit
     (step K S (.unwrap "alice.near" 130 (.native "bob.near"))).L.bals = [("alice.near", 100)] ∧
     (step K S (.unwrap "alice.near" 130 (.native "bob.near"))).jobs.length = 0) ∧
    (let S1 := run K S0 (deposit ++
        [.admin (.acl [("dao.near", .DAO)]), .admin (.pause "dao.near" "intents")])
     (step K S1 (.unwrap "alice.near" 30 (.native "bob.near"))).L.bals = [("alice.near", 100)] ∧
     (step K S1 (.unwrap "alice.near" 30 (.native "bob.near"))).jobs.length = 0) ∧
    (let S2 := run K S0 (deposit ++
        [.admin (.acl [("dao.near", .DAO)]), .admin (.lock "dao.near" "alice.near")])
     (step K S2 (.unwrap "alice.near" 30 (.native "bob.near"))).L.bals = [("alice.near", 100)] ∧
     (step K S2 (.unwrap "alice.near" 30 (.native "bob.near"))).jobs.length = 0) := by
  decide

/-- Row "`near_withdraw` fails" (`N4_unwrap_fails`, `W1_kept`): the debit of 30 stays, wNEAR is
    untouched — the contract holds 100 against a ledger of 70, 30 wNEAR are held and assigned to
    nobody — no NEAR arrives and none is sent on. -/
example :
    let S := run K S0 (deposit ++
      [ .unwrap "alice.near" 30 (.native "bob.near"),
        .nearWithdrawFails 0,
        .doJob 0 true ])
    S.L.bals = [("alice.near", 70)] ∧ WNear.bal S.c.accts "intents.near" = 100 ∧
    S.c.supply = 100 ∧ S.paid = [] ∧ S.jobs.length = 0 ∧ S.ready.length = 0 ∧
    S.resolves.length = 0 ∧
    (S.uDebited, S.uBurned, S.uKept, S.nGot, S.nFwd) = (30, 0, 30, 0, 0) := by
  decide

/-- Row "the `do_*` callback fails after a successful unwrap" (`N3_forward`,
    `N4_callback_fails`): the debit stays, the 30 wNEAR are burned, the 31 NEAR arrived at the
    contract and nothing is sent on. -/
example :
    let S := run K S0 (deposit ++
      [ .unwrap "alice.near" 30 (.native "bob.near"),
        .nearWithdraw 0,
        .doJob 0 false ])
    S.L.bals = [("alice.near", 70)] ∧ WNear.bal S.c.accts "intents.near" = 70 ∧
    S.c.supply = 70 ∧ S.ready.length = 0 ∧ S.resolves.length = 0 ∧
    (S.uDebited, S.uBurned, S.uKept, S.nGot, S.nFwd) = (30, 30, 0, 31, 0) := by
  decide

/-- Row "withdrawal of wNEAR with a storage deposit, `near_withdraw` fails", plain
    `ft_transfer`: `ft_resolve_withdraw` gives the 40 back, the storage deposit of 10 stays
    debited; nothing was burned, the contract holds 100 against a ledger of 90. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw .intent wsd,
        .nearWithdrawFails 0,
        .doJob 0 true,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 90)] ∧ WNear.bal S.c.accts "intents.near" = 100 ∧
    (S.uDebited, S.uBurned, S.uKept, S.nGot, S.nFwd) = (10, 0, 10, 0, 0) := by
  decide

/-- Row "… `do_ft_withdraw` fails after a successful unwrap", plain `ft_transfer`: 10 burned,
    the 40 refunded, the 11 NEAR stay with the contract. Ledger 90 = held 90. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw .intent wsd,
        .nearWithdraw 0,
        .doJob 0 false,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 90)] ∧ WNear.bal S.c.accts "intents.near" = 90 ∧
    (S.uDebited, S.uBurned, S.uKept, S.nGot, S.nFwd) = (10, 10, 0, 11, 0) := by
  decide

/-- Row "… the token receipt (`storage_deposit` + `ft_transfer`) fails", plain `ft_transfer`:
    10 burned and sent on with the receipt, the 40 refunded. Ledger 90 = held 90. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw .intent wsd,
        .nearWithdraw 0,
        .doJob 0 true,
        .tokXferFails 0,
        .resolveWd 0 ])
    S.L.bals = [("alice.near", 90)] ∧ WNear.bal S.c.accts "intents.near" = 90 ∧
    (S.uDebited, S.uBurned, S.uKept, S.nGot, S.nFwd) = (10, 10, 0, 11, 10) := by
  decide

/-- `N4_unwrap_fails`, `N4_callback_fails` and `W1_kept` applied. -/
example :
    let S := run K S0 (deposit ++ [ .unwrap "alice.near" 30 (.native "bob.near") ])
    let S1 := step K S (.nearWithdrawFails 0)
    let S2 := step K S1 (.doJob 0 true)
    S1.L = S.L ∧ S1.c = S.c ∧ S1.uKept = S.uKept + 30 ∧ S2.L = S1.L ∧ S2.nFwd = S1.nFwd ∧
    total S2.L.bals + S2.uKept ≤ WNear.bal S2.c.accts K.me := by
  intro S S1 S2
  have hj : S.jobs[0]? = some ⟨"alice.near", 30, .native "bob.near"⟩ := by decide
  obtain ⟨a1, a2, _, a4, a5, _⟩ := N4_unwrap_fails K S 0 _ hj
  have hk : S1.ready[0]? = some ⟨⟨"alice.near", 30, .native "bob.near"⟩, false⟩ := by
    show (step K S (.nearWithdrawFails 0)).ready[0]? = _
    rw [a4]; decide
  obtain ⟨b1, _, _, _, _, b6⟩ := N4_callback_fails K S1 0 _ hk rfl true
  have hR : Reach K S2 := Reach.step _ (Reach.step _ (reach0 _))
  exact ⟨a1, a2, a5, b1, b6 (by simp), W1_kept K S2 hR⟩

/-! ### Who can lower a balance (W4) -/

/-- `bob.near` cannot start a withdrawal from `alice.near`'s balance with `ft_withdraw`, and a
    holder of `UnrestrictedWithdrawer` can (`ft_force_withdraw`), also from a locked account. -/
example :
    let S := run K S0 (deposit ++
      [ .ftWithdraw (.method "bob.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40 },
        .admin (.acl [("dao.near", .DAO), ("ops.near", .UnrestrictedWithdrawer)]),
        .admin (.lock "dao.near" "alice.near"),
        .ftWithdraw (.method "alice.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40 },
        .ftWithdraw (.force "ops.near")
          { owner := "alice.near", receiver := "bob.near", amount := 40 } ])
    S.L.ctl.locked = ["alice.near"] ∧ S.L.bals = [("alice.near", 60)] ∧
    S.outbox.map Wd.amount = [40] := by
  decide

/-- The unwrap intent is the fourth case of `W4_who_can_lower`. -/
example :
    let S := run K S0 deposit
    ∃ x f, Step.unwrap "alice.near" 30 (.native "bob.near") = .unwrap "alice.near" x f ∧
      S.L.ctl.isPaused "intents" = false ∧ S.L.ctl.locked.contains "alice.near" = false := by
  intro S
  have hlt : bal (step K S (.unwrap "alice.near" 30 (.native "bob.near"))).L.bals "alice.near" <
      bal S.L.bals "alice.near" := by decide
  rcases W4_who_can_lower K S "alice.near" _ hlt with ⟨w, h, _⟩ | ⟨w, h, _⟩ | ⟨who, w, h, _⟩ |
      h | ⟨d, a, h, _⟩ | ⟨d, a, h⟩ | ⟨who, d, a, h, _⟩
  · exact Step.noConfusion h
  · exact Step.noConfusion h
  · exact Step.noConfusion h
  · exact h
  · exact Step.noConfusion h
  · exact Step.noConfusion h
  · exact Step.noConfusion h

/-- An internal move (an `mt_transfer` by `alice.near`) keeps the total; `W4_switches`: it
    changes no switch. -/
example :
    let S := run K S0 (deposit ++ [ .move .owner "alice.near" "bob.near" 30 ])
    S.L.bals = [("alice.near", 70), ("bob.near", 30)] ∧ S.L.supply = 100 := by
  decide

/-! ### The remaining statements, applied -/

/-- `W1_backing`, `W1_supply` and `held_le_max` on every state of every run. -/
example (l : List Step) :
    total (run K S0 l).L.bals + debitedInFlight (run K S0 l) + uncredited (run K S0 l) +
        (run K S0 l).uKept ≤ WNear.bal (run K S0 l).c.accts K.me + movedOut (run K S0 l) ∧
    (run K S0 l).L.supply = total (run K S0 l).L.bals ∧
    WNear.bal (run K S0 l).c.accts K.me ≤ ProvedFT.U128_MAX :=
  ⟨W1_backing K _ (reach0 l), W1_supply K _ (reach0 l), held_le_max (reach0 l)⟩

/-- `W1_quiet`: the state after the deposit is quiet, and nothing is in flight in it. -/
example :
    let S := run K S0 deposit
    debitedInFlight S = 0 ∧ uncredited S = 0 ∧ movedOut S = 0 := by
  intro S
  have hq : Quiet K S := by
    refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · have : S.resolves.length = 0 := by decide
      exact List.eq_nil_of_length_eq_zero this
    · have : S.pend.length = 0 := by decide
      rw [List.eq_nil_of_length_eq_zero this]
      intro e he; simp at he
  obtain ⟨h1, h2, h3, _⟩ := W1_quiet K S (reach0 _) hq
  exact ⟨h1, h2, h3⟩

/-- `W2_debit` on the intent with a storage deposit: 40 + 10 leave `alice.near`'s balance. -/
example :
    let S := run K S0 deposit
    ∃ L', startWithdrawW S.L .intent wsd = some L' ∧
      bal L'.bals "alice.near" + (40 + 10) = bal S.L.bals "alice.near" := by
  intro S
  cases h : startWithdrawW S.L .intent wsd with
  | none =>
    have hne : (startWithdrawW S.L .intent wsd).isSome = true := by decide
    rw [h] at hne; exact absurd hne (by simp)
  | some L' => exact ⟨L', rfl, (W2_debit S.L L' .intent wsd h).1⟩

/-- `W3_credit_only_on_arrival` applied to the credit step of the deposit. -/
example :
    let S := run K S0 (deposit.take 1)
    ∃ i recv e, Step.onTransfer 0 "alice.near" true = .onTransfer i recv true ∧
      S.pend[i]? = some e ∧ e.receiver = K.me := by
  intro S
  have hgt : S.L.supply < (step K S (.onTransfer 0 "alice.near" true)).L.supply := by decide
  rcases W3_credit_only_on_arrival K S _ hgt with ⟨i, recv, e, h1, h2, h3, _⟩ | ⟨k, r, h1, _⟩
  · exact ⟨i, recv, e, h1, h2, h3⟩
  · exact Step.noConfusion h1

/-- `W4_switches` and `N4_no_refund`: an unwrap changes no switch; the `near_withdraw` step
    does not touch the ledger. -/
example (S : World) :
    (step K S (.unwrap "alice.near" 5 (.native "bob.near"))).L.ctl = S.L.ctl ∧
    (step K S (.nearWithdraw 0)).L = S.L :=
  ⟨W4_switches K S _ (fun _ h => Step.noConfusion h), N4_no_refund K S _ (Or.inl ⟨0, rfl⟩)⟩

/-- `N4_withdrawal_refund` on `wsd` (a plain `ft_transfer`): after a failed unwrap or callback
    the resolve gives back the 40, not the storage deposit. -/
example : (Rs.mk wsd.owner wsd.amount wsd.msg.isSome .failed 0).refund = 40 := by
  rw [(N4_withdrawal_refund wsd).2]; decide

/-- `inv_step` and `books_step` from the start state. -/
example (st : Step) : Inv K (step K S0 st) ∧ Books (step K S0 st) :=
  ⟨inv_step K (inv_init init0) st, books_step K (books_init init0) st⟩

/-- `tok_reach` on every run. -/
example (l : List Step) :
    ∃ S1 : World, Init K S1 ∧
      (WNear.Reach K.tok (toSys S1) → WNear.Reach K.tok (toSys (run K S0 l))) :=
  tok_reach me_ne (reach0 l)

/-! ### The token side (`tok_inv`, `tok_step`, `tok_run`) -/

/-- On every run the token keeps the invariant of the wNEAR model, and its side of the world is
    a run of that model from the start state. -/
example (l : List Step) :
    WNear.Inv K.tok (toSys (run K S0 l)) ∧
    ∃ (S1 : World) (l' : List WNear.Step), Init K S1 ∧
      toSys (run K S0 l) = l'.foldl (WNear.sysStep K.tok) (toSys S1) :=
  ⟨tok_inv (reach0 l), tok_run me_ne (reach0 l)⟩

end IntentsW.Examples
