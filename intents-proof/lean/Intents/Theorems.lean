/-
  The statements about the NEP-141 deposit and withdrawal paths of the Intents ledger, composed
  with the proved token model.

  * T1 backing            `T1_backing`, `T1_ledger_covered`, `T1_supply`, `T1_quiet`,
                          `T1_can_pay`
                          (with equality: `T1_exact`, `T1_equality` in `Intents/Exact.lean`)
  * the token part        `tok_reach` (the token in this world is a reachable state of the proved
                          token model, so its properties P1–P5 hold here)
  * T2 settlement         `T2_debit`, `T2_settles`, `T2_no_callback`
  * T3 deposits           `T3_credit_only_on_arrival`, `T3_arrival`, `T3_covered`
  * T4 who can lower      `ledger_step`, `T4_who_can_lower`, `T4_switches`, `T4_pause_power`,
                          `T4_lock_power`

  Reachable states (`Reach`) start from an initial token state and an empty ledger and take any
  sequence of steps of `Intents/World.lean`. What a step is, and what the model leaves out, is in
  NOTES.md.
-/
import Intents.Backing

namespace Intents
open ProvedFT

/-! ## T1 Backing -/

/-- The amount of an `ft_transfer_call` the contract sent whose settlement on the token is
    still in flight. -/
def wdAmt (e : Pend) : Nat :=
  match e.ann with
  | .wd _ => e.amount
  | _ => 0

/-- Withdrawals debited from the ledger whose `ft_resolve_withdraw` has not run yet, each
    counted at its full amount. -/
def debitedInFlight (S : World) : Nat :=
  sumBy Wd.amount S.unwrap + sumBy Wd.amount S.outbox + sumBy wdAmt S.pend +
    sumBy Rs.amount S.resolves

/-- What those withdrawals have already moved out of the contract's token balance. -/
def movedOut (S : World) : Nat := sumBy wdAmt S.pend + sumBy Rs.left S.resolves

/-- Transfers to the contract that the token may still take back: `ft_on_transfer` has not
    credited them. -/
def uncredited (S : World) : Nat := sumBy depW S.pend

theorem sumBy_split {α : Type} (f g : α → Nat) {l : List α} (h : ∀ a ∈ l, g a ≤ f a) :
    sumBy f l = sumBy (fun a => f a - g a) l + sumBy g l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [sumBy]; omega

/-- **T1 Backing.** In every reachable state, for the token: the sum of the ledger balances,
    plus the withdrawals already debited whose resolve callback has not run (at their full
    amount), plus the incoming transfers not credited yet, is at most the contract's token
    balance plus what those withdrawals have already moved out. -/
theorem T1_backing (K : Cfg) (S : World) (h : Reach K S) :
    total S.L.bals + debitedInFlight S + uncredited S ≤ bal S.c.accts K.me + movedOut S := by
  have hI := inv_reach h
  have hb := hI.backed
  have hs : sumBy Rs.amount S.resolves = sumBy Rs.unsettled S.resolves + sumBy Rs.left S.resolves :=
    sumBy_split Rs.amount Rs.left (fun r hr => (hI.rs r hr).1)
  rw [hI.cons] at hb
  unfold owed at hb
  unfold debitedInFlight movedOut uncredited
  omega

/-- **T1, the plain reading.** In every reachable state the sum of the ledger balances is at
    most the token balance of the contract — with anything in flight, at any point of any
    interleaving. -/
theorem T1_ledger_covered (K : Cfg) (S : World) (h : Reach K S) :
    total S.L.bals ≤ bal S.c.accts K.me := by
  have hI := inv_reach h
  have hb := hI.backed
  rw [hI.cons] at hb
  omega

/-- **T1, the ledger's own books.** `total_supplies` for the token is the sum of the account
    balances. -/
theorem T1_supply (K : Cfg) (S : World) (h : Reach K S) : S.L.supply = total S.L.bals :=
  (inv_reach h).cons

/-- Nothing of the contract is in flight: no withdrawal between debit and resolve, and no
    token settlement callback with the contract as sender or receiver. -/
def Quiet (K : Cfg) (S : World) : Prop :=
  S.unwrap = [] ∧ S.outbox = [] ∧ S.resolves = [] ∧
  ∀ e ∈ S.pend, e.sender ≠ K.me ∧ e.receiver ≠ K.me

/-- In a quiet state both in-flight terms of `T1_backing` vanish. -/
theorem T1_quiet (K : Cfg) (S : World) (h : Reach K S) (hq : Quiet K S) :
    debitedInFlight S = 0 ∧ uncredited S = 0 ∧ movedOut S = 0 ∧
    total S.L.bals ≤ bal S.c.accts K.me := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hI := inv_reach h
  have hw : sumBy wdAmt S.pend = 0 := by
    apply sumBy_eq_zero
    intro e he
    have hok := hI.pend e he
    unfold PendOK at hok
    unfold wdAmt
    cases hann : e.ann with
    | other => rfl
    | dep s => rfl
    | wd o => rw [hann] at hok; exact absurd hok.1 (h4 e he).1
  have hd : sumBy depW S.pend = 0 := by
    apply sumBy_eq_zero
    intro e he
    have hok := hI.pend e he
    unfold PendOK at hok
    cases hann : e.ann with
    | other => exact depW_other hann
    | dep s => rw [hann] at hok; exact absurd hok (h4 e he).2
    | wd o => exact depW_wd hann
  refine ⟨?_, hd, ?_, T1_ledger_covered K S h⟩
  · unfold debitedInFlight; rw [h1, h2, h3, hw]; rfl
  · unfold movedOut; rw [h3, hw]; rfl

/-! ## The token part is the proved token model -/

/-- The token's side of the world, as a state of the proved token model. -/
def toSys (S : World) : Sys := ⟨S.c, S.pend.map Pend.raw, S.paid⟩

theorem reach_foldl {E : Env} {X : Sys} (h : ProvedFT.Reach E X) (l : List ProvedFT.Step) :
    ProvedFT.Reach E (l.foldl (sysStep E) X) := by
  induction l generalizing X with
  | nil => exact h
  | cons st t ih => exact ih (ProvedFT.Reach.step st h)

theorem resultsFor_nil (E : Env) (p : Acct) : resultsFor E p [] = [] := by
  unfold resultsFor; split <;> rfl

/-- A call by anyone, in the token model and in the world, when it adds callbacks `anns` with
    the right raw content. -/
theorem toSys_call {K : Cfg} {S : World} {p : Acct} {d : Nat} {m : Method} {rs : List PR} {o : Out}
    (he : exec K.tok S.c ⟨p, d, m, resultsFor K.tok p rs⟩ = some o) (anns : List Pend)
    (hraw : anns.map Pend.raw = o.calls) :
    (⟨o.st, S.pend.map Pend.raw ++ anns.map Pend.raw, S.paid ++ o.transfers⟩ : Sys) =
      sysStep K.tok (toSys S) (.call p d m rs) := by
  simp only [sysStep, toSys, he, hraw]

/-- Every step of the world is zero, one or two steps of the proved token model on the token's
    side. -/
theorem tok_step (K : Cfg) (S : World) (st : Step) :
    ∃ l : List ProvedFT.Step, toSys (stdStep K S st) = l.foldl (sysStep K.tok) (toSys S) := by
  cases st with
  | tokCall p d m rs =>
    simp only [stdStep, step]
    by_cases hpm : p = K.me
    · rw [ifP hpm]; exact ⟨[], rfl⟩
    · rw [ifN hpm]
      cases he : exec K.tok S.c ⟨p, d, m, resultsFor K.tok p rs⟩ with
      | none => exact ⟨[], rfl⟩
      | some o =>
        refine ⟨[.call p d m rs], ?_⟩
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← toSys_call he (annThird K.me o.calls) (raw_annThird _ _)]
        simp only [toSys, List.map_append]
  | tokResolve i res =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact ⟨[], rfl⟩
    | some e =>
      dsimp only
      cases hro : resOf e res with
      | none => exact ⟨[], rfl⟩
      | some r =>
        dsimp only
        refine ⟨[.resolve i r], ?_⟩
        have hraw : (S.pend.map Pend.raw)[i]? = some (e.sender, e.receiver, e.amount) := by
          rw [List.getElem?_map, hpi]; rfl
        simp only [List.foldl_cons, List.foldl_nil, sysStep, toSys, hraw]
        cases he : exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [r]⟩ with
        | none => simp only [map_eraseIdx]
        | some o => simp only [List.map_append, map_eraseIdx, raw_annThird]
  | tokResolveFails i =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact ⟨[], rfl⟩
    | some e =>
      dsimp only
      cases hro : resOf e .failed with
      | none => exact ⟨[], rfl⟩
      | some r =>
        refine ⟨[.resolveFails i], ?_⟩
        simp only [List.foldl_cons, List.foldl_nil, sysStep, toSys, map_eraseIdx]
  | tokNearIn x =>
    refine ⟨[.nearIn x], ?_⟩
    simp only [stdStep, step, List.foldl_cons, List.foldl_nil, sysStep, toSys]
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx, ifP hx]
    · rw [ifN hx, ifN hx]
  | onTransfer i recv ok =>
    refine ⟨[], ?_⟩
    simp only [stdStep, step, List.foldl_nil]
    cases hpi : S.pend[i]? with
    | none => rfl
    | some e =>
      dsimp only
      by_cases hg : e.receiver = K.me ∧ e.ann = .dep none
      · rw [ifP hg]
        split
        · simp only [toSys]
          rw [map_set_same Pend.raw hpi { e with ann := .dep (some true) } rfl]
        · simp only [toSys]
          rw [map_set_same Pend.raw hpi { e with ann := .dep (some false) } rfl]
      · rw [ifN hg]
  | ftWithdraw via w =>
    refine ⟨[], ?_⟩
    simp only [stdStep, step, List.foldl_nil]
    split
    · rfl
    · split <;> rfl
  | doFtWithdraw j ok =>
    refine ⟨[], ?_⟩
    simp only [stdStep, step, List.foldl_nil]
    split
    · rfl
    · split <;> rfl
  | tokXfer j =>
    simp only [stdStep, step]
    cases hj : S.outbox[j]? with
    | none => exact ⟨[], rfl⟩
    | some w =>
      dsimp only
      cases hsd : w.sd with
      | none =>
        have hb : xferBatch (exec K.tok) K.me S.c w = exec K.tok S.c ⟨K.me, 1, xferMethod w, []⟩ := by
          simp only [xferBatch, hsd]
        rw [hb]
        cases he : exec K.tok S.c ⟨K.me, 1, xferMethod w, []⟩ with
        | none => exact ⟨[], rfl⟩
        | some o =>
          refine ⟨[.call K.me 1 (xferMethod w) []], ?_⟩
          simp only [List.foldl_cons, List.foldl_nil]
          rw [← toSys_call (by rw [resultsFor_nil]; exact he) (annWd w.owner o.calls)
            (raw_annWd _ _)]
          simp only [toSys, List.map_append]
      | some d =>
        cases h1 : exec K.tok S.c ⟨K.me, d, .storage_deposit (some w.receiver) none, []⟩ with
        | none =>
          have hb : xferBatch (exec K.tok) K.me S.c w = none := by
            simp only [xferBatch, hsd, h1]
          rw [hb]; exact ⟨[], rfl⟩
        | some o1 =>
          cases h2 : exec K.tok o1.st ⟨K.me, 1, xferMethod w, []⟩ with
          | none =>
            have hb : xferBatch (exec K.tok) K.me S.c w = none := by
              simp only [xferBatch, hsd, h1, h2]
            rw [hb]; exact ⟨[], rfl⟩
          | some o2 =>
            have hb : xferBatch (exec K.tok) K.me S.c w =
                some ⟨o2.st, o1.transfers ++ o2.transfers, o1.calls ++ o2.calls,
                  o1.events ++ o2.events, o2.ret⟩ := by
              simp only [xferBatch, hsd, h1, h2]
            rw [hb]
            refine ⟨[.call K.me d (.storage_deposit (some w.receiver) none) [],
              .call K.me 1 (xferMethod w) []], ?_⟩
            simp only [List.foldl_cons, List.foldl_nil, sysStep, toSys, resultsFor_nil, h1, h2,
              List.map_append, raw_annWd, List.append_assoc]
  | tokXferFails j =>
    refine ⟨[], ?_⟩
    simp only [stdStep, step, List.foldl_nil]
    split <;> rfl
  | meStorageDeposit acc d =>
    simp only [stdStep, step]
    cases he : exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc) none, []⟩ with
    | none => exact ⟨[], rfl⟩
    | some o =>
      refine ⟨[.call K.me d (.storage_deposit (some acc) none) []], ?_⟩
      simp only [List.foldl_cons, List.foldl_nil]
      rw [← toSys_call (by rw [resultsFor_nil]; exact he) (annThird K.me o.calls)
        (raw_annThird _ _)]
      simp only [toSys, List.map_append]
  | resolveWd k =>
    refine ⟨[], ?_⟩
    simp only [stdStep, step, List.foldl_nil]
    split
    · rfl
    · split <;> rfl
  | resolveWdFails k => exact ⟨[], rfl⟩
  | move auth src dst amt =>
    refine ⟨[], ?_⟩
    simp only [stdStep, step, List.foldl_nil]
    split <;> rfl
  | admin a => exact ⟨[], rfl⟩

/-- **The token in the two-contract world is the proved token.** Its state, with its callbacks
    in flight, is a reachable state of `ProvedFT`, so P1–P5 of the token standard hold for it
    at every point of every interleaving with the Intents contract. -/
theorem tok_reach {K : Cfg} {S : World} (h : Reach K S) : ProvedFT.Reach K.tok (toSys S) := by
  induction h with
  | init S h =>
    have : toSys S = ⟨S.c, [], []⟩ := by simp only [toSys, h.pend, h.paid, List.map_nil]
    rw [this]
    exact ProvedFT.Reach.init S.c h.tok
  | step st _ ih =>
    obtain ⟨l, hl⟩ := tok_step K _ st
    rw [hl]
    exact reach_foldl ih l

/-- The contract's token balance fits `u128` (from the token's conservation, P1). -/
theorem held_le_max {K : Cfg} {S : World} (h : Reach K S) : bal S.c.accts K.me ≤ U128_MAX := by
  have hT := ProvedFT.inv_reach (tok_reach h)
  have h1 := hT.pre.cons
  have h2 := hT.pre.bound
  have h3 := bal_le_total S.c.accts K.me
  simp only [toSys] at h1 h2
  omega

/-! ## How the ledger can change -/

/-- **Every change of the ledger is one of five.** A step leaves the ledger as it is, or it is:
    a credit in `ft_on_transfer` for a transfer to the contract whose settlement is in flight and
    not yet answered; the debit that starts a withdrawal; a refund in `ft_resolve_withdraw`; an
    internal move; or a change of the switches. -/
theorem ledger_step (K : Cfg) (S : World) (st : Step) :
    (stdStep K S st).L = S.L ∨
    (∃ i recv e L', st = .onTransfer i recv true ∧ S.pend[i]? = some e ∧ e.receiver = K.me ∧
      e.ann = .dep none ∧ S.L.ctl.isPaused "ft_on_transfer" = false ∧
      credit S.L recv e.amount = some L' ∧ (stdStep K S st).L = L') ∨
    (∃ via w L', st = .ftWithdraw via w ∧ startWithdraw S.L via w = some L' ∧
      (stdStep K S st).L = L') ∨
    (∃ k r L', st = .resolveWd k ∧ S.resolves[k]? = some r ∧ r.refund ≠ 0 ∧
      credit S.L r.owner r.refund = some L' ∧ (stdStep K S st).L = L') ∨
    (∃ auth src dst amt L', st = .move auth src dst amt ∧
      moveBal S.L auth src dst amt = some L' ∧ (stdStep K S st).L = L') ∨
    (∃ a, st = .admin a ∧ (stdStep K S st).L = { S.L with ctl := adminStep S.L.ctl a }) := by
  cases st with
  | tokCall p d m rs =>
    left; simp only [stdStep, step]
    split
    · rfl
    · split <;> rfl
  | tokResolve i res =>
    left; simp only [stdStep, step]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | tokResolveFails i =>
    left; simp only [stdStep, step]
    split
    · rfl
    · split <;> rfl
  | tokNearIn x =>
    left; simp only [stdStep, step]
    split <;> rfl
  | onTransfer i recv ok =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => left; rfl
    | some e =>
      dsimp only
      by_cases hg : e.receiver = K.me ∧ e.ann = .dep none
      · rw [ifP hg]
        by_cases hcond : ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false
        · rw [ifP hcond]
          cases hcr : credit S.L recv e.amount with
          | none => left; rfl
          | some L' =>
            right; left
            obtain ⟨rfl, hpz⟩ := hcond
            exact ⟨i, recv, e, L', rfl, hpi, hg.1, hg.2, hpz, hcr, rfl⟩
        · rw [ifN hcond]; left; rfl
      · rw [ifN hg]; left; rfl
  | ftWithdraw via w =>
    simp only [stdStep, step]
    cases hs : startWithdraw S.L via w with
    | none => left; rfl
    | some L' =>
      right; right; left
      refine ⟨via, w, L', rfl, hs, ?_⟩
      dsimp only
      split <;> rfl
  | doFtWithdraw j ok =>
    left; simp only [stdStep, step]
    split
    · rfl
    · split <;> rfl
  | tokXfer j =>
    left; simp only [stdStep, step]
    split
    · rfl
    · split <;> rfl
  | tokXferFails j =>
    left; simp only [stdStep, step]
    split <;> rfl
  | meStorageDeposit acc d =>
    left; simp only [stdStep, step]
    split <;> rfl
  | resolveWd k =>
    simp only [stdStep, step]
    cases hk : S.resolves[k]? with
    | none => left; rfl
    | some r =>
      dsimp only
      cases hres : resolveWithdraw S.L r with
      | none => left; rfl
      | some L' =>
        unfold resolveWithdraw at hres
        by_cases h0 : r.refund = 0
        · rw [ifP h0] at hres
          obtain rfl := Option.some.inj hres
          left; rfl
        · rw [ifN h0] at hres
          right; right; right; left
          exact ⟨k, r, L', rfl, hk, h0, hres, rfl⟩
  | resolveWdFails k => left; rfl
  | move auth src dst amt =>
    simp only [stdStep, step]
    cases hm : moveBal S.L auth src dst amt with
    | none => left; rfl
    | some L' => right; right; right; right; left; exact ⟨auth, src, dst, amt, L', rfl, hm, rfl⟩
  | admin a => right; right; right; right; right; exact ⟨a, rfl, rfl⟩

/-! ## T2 Withdrawal settles exactly -/

/-- **T2, the debit.** Starting a withdrawal of `w.amount` takes exactly that amount from the
    owner's ledger balance and from the ledger total, and touches no other balance. -/
theorem T2_debit (L L' : Ledger) (via : Via) (w : Wd) (h : startWithdraw L via w = some L') :
    bal L'.bals w.owner + w.amount = bal L.bals w.owner ∧
    (∀ a, a ≠ w.owner → bal L'.bals a = bal L.bals a) ∧
    L'.supply + w.amount = L.supply ∧ L'.ctl = L.ctl := by
  obtain ⟨_, _, hd⟩ := startWithdraw_some h
  obtain ⟨_, _, hle, hles, rfl⟩ := debit_some hd
  refine ⟨?_, fun a ha => ?_, ?_, rfl⟩
  · simp only; rw [bal_set_self]; omega
  · simp only; rw [bal_set_ne _ _ (Ne.symm ha)]
  · simp only; omega

/-- **T2. Withdrawal settles exactly.** In a reachable state, when a ready
    `ft_resolve_withdraw` of a withdrawal of `r.amount` runs — whatever happened to the token
    transfer before — it cannot fail, it credits the owner exactly `r.refund` and nobody else,
    and the amount that stays debited, `r.amount - r.refund`, is exactly what left the
    contract's token balance (`r.left`). The single exception: the `ft_transfer_call` receipt
    itself failed on the token (or `do_ft_withdraw` before it), so nothing left, and still nothing
    is refunded. -/
theorem T2_settles (K : Cfg) (S : World) (h : Reach K S) (k : Nat) (r : Rs)
    (hk : S.resolves[k]? = some r) :
    let S' := stdStep K S (.resolveWd k)
    S'.resolves = S.resolves.eraseIdx k ∧
    bal S'.L.bals r.owner = bal S.L.bals r.owner + r.refund ∧
    (∀ a, a ≠ r.owner → bal S'.L.bals a = bal S.L.bals a) ∧
    S'.L.supply = S.L.supply + r.refund ∧
    (r.amount - r.refund = r.left ∨
      (r.isCall = true ∧ r.res = PR.failed ∧ r.left = 0 ∧ r.refund = 0)) := by
  intro S'
  have hI := inv_reach h
  have hmem := List.mem_of_getElem? hk
  have hok := hI.rs r hmem
  have hmax := held_le_max h
  have hb := hI.backed
  have hun := le_sumBy Rs.unsettled hmem
  have hcons := hI.cons
  have hbt := bal_le_total S.L.bals r.owner
  have hle : r.refund ≤ r.unsettled := by
    unfold Rs.unsettled
    rcases hok.2 with h' | h'
    · omega
    · omega
  have hexc : r.amount - r.refund = r.left ∨
      (r.isCall = true ∧ r.res = PR.failed ∧ r.left = 0 ∧ r.refund = 0) := by
    rcases hok.2 with h' | h'
    · left; omega
    · right; exact h'
  unfold owed at hb
  by_cases h0 : r.refund = 0
  · have hS' : S' = { S with resolves := S.resolves.eraseIdx k } := by
      simp only [S', step, hk, resolveWithdraw, ifP h0]
    rw [hS']
    exact ⟨rfl, by simp only; omega, fun _ _ => rfl, by simp only; omega, hexc⟩
  · have hcr := credit_of (L := S.L) (a := r.owner) (x := r.refund) (by omega) (by omega) (by omega)
    have hS' : S' = { S with
        L := { S.L with bals := set S.L.bals r.owner (bal S.L.bals r.owner + r.refund),
                        supply := S.L.supply + r.refund },
        resolves := S.resolves.eraseIdx k } := by
      simp only [S', step, hk, resolveWithdraw, ifN h0, hcr]
    rw [hS']
    refine ⟨rfl, ?_, fun a ha => ?_, rfl, hexc⟩
    · simp only; rw [bal_set_self]
    · simp only; rw [bal_set_ne _ _ (Ne.symm ha)]

/-- **T2, when the resolve callback itself does not run** (out of gas, log too long): the
    ledger is left as it is. The owner stays debited the full amount, also the part that never
    left; those tokens remain in the contract's token balance, assigned to nobody. -/
theorem T2_no_callback (K : Cfg) (S : World) (k : Nat) :
    let S' := stdStep K S (.resolveWdFails k)
    S'.L = S.L ∧ S'.c = S.c ∧ S'.resolves = S.resolves.eraseIdx k :=
  ⟨rfl, rfl, rfl⟩

/-! ## T3 Deposits credit what arrived -/

/-- **T3. A credit happens only for what arrived.** If a step raises the ledger total, it is
    one of two:
    * the contract's `ft_on_transfer` for a transfer to the contract whose settlement callback
      is in flight on the token and not yet answered; the credit is exactly the amount of that
      transfer;
    * `ft_resolve_withdraw` giving back `r.refund` of a withdrawal debited before. -/
theorem T3_credit_only_on_arrival (K : Cfg) (S : World) (st : Step)
    (hgt : S.L.supply < (stdStep K S st).L.supply) :
    (∃ i recv e, st = .onTransfer i recv true ∧ S.pend[i]? = some e ∧ e.receiver = K.me ∧
      e.ann = .dep none ∧ S.L.ctl.isPaused "ft_on_transfer" = false ∧
      (stdStep K S st).L.supply = S.L.supply + e.amount ∧
      bal (stdStep K S st).L.bals recv = bal S.L.bals recv + e.amount ∧
      ∀ a, a ≠ recv → bal (stdStep K S st).L.bals a = bal S.L.bals a) ∨
    (∃ k r, st = .resolveWd k ∧ S.resolves[k]? = some r ∧
      (stdStep K S st).L.supply = S.L.supply + r.refund ∧
      bal (stdStep K S st).L.bals r.owner = bal S.L.bals r.owner + r.refund) := by
  rcases ledger_step K S st with h | ⟨i, recv, e, L', rfl, hpi, h1, h2, h3, hcr, hL⟩ |
      ⟨via, w, L', rfl, hs, hL⟩ | ⟨k, r, L', rfl, hk, _, hcr, hL⟩ |
      ⟨auth, src, dst, amt, L', rfl, hm, hL⟩ | ⟨a, rfl, hL⟩
  · rw [h] at hgt; omega
  · left
    obtain ⟨_, _, _, rfl⟩ := credit_some hcr
    rw [hL]
    refine ⟨i, recv, e, rfl, hpi, h1, h2, h3, rfl, ?_, fun a ha => ?_⟩
    · simp only; rw [bal_set_self]
    · simp only; rw [bal_set_ne _ _ (Ne.symm ha)]
  · rw [hL] at hgt
    obtain ⟨_, _, h3, _⟩ := T2_debit S.L L' via w hs
    omega
  · right
    obtain ⟨_, _, _, rfl⟩ := credit_some hcr
    rw [hL]
    exact ⟨k, r, rfl, hk, rfl, by simp only; rw [bal_set_self]⟩
  · rw [hL] at hgt
    obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm
    simp only at hgt; omega
  · rw [hL] at hgt; simp only at hgt; omega

/-- **T3, where such a transfer comes from.** A settlement callback of a transfer to the
    contract appears only when some other account's `ft_transfer_call` to the contract succeeds
    on the token, and at that moment the contract's token balance has grown by exactly the
    amount the callback carries. -/
theorem T3_arrival (K : Cfg) (S : World) (st : Step) (e : Pend)
    (he : e ∈ (stdStep K S st).pend) (hfresh : e.ann = .dep none) (hnew : e ∉ S.pend) :
    ∃ p d x memo msg rs, st = .tokCall p d (.ft_transfer_call K.me x memo msg) rs ∧
      p ≠ K.me ∧ e = ⟨p, K.me, x, .dep none⟩ ∧ 0 < x ∧
      bal (stdStep K S st).c.accts K.me = bal S.c.accts K.me + x := by
  cases st with
  | tokCall p d m rs =>
    simp only [stdStep, step] at he ⊢
    by_cases hpm : p = K.me
    · rw [ifP hpm] at he; exact absurd he hnew
    · rw [ifN hpm] at he ⊢
      cases hx : exec K.tok S.c ⟨p, d, m, resultsFor K.tok p rs⟩ with
      | none => rw [hx] at he; exact absurd he hnew
      | some o =>
        rw [hx] at he
        dsimp only at he ⊢
        obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some hx
        rcases List.mem_append.mp he with h | h
        · exact absurd h hnew
        · rcases calls_origin hm with h0 | ⟨rc, x, memo, msg, rfl, h1, hne, hxp, hb1, _⟩
          · rw [hc, h0] at h; simp [annThird] at h
          · rw [hc, h1] at h
            simp only [annThird, List.map_cons, List.map_nil, List.mem_singleton] at h
            by_cases hrc : rc = K.me
            · subst hrc
              rw [ifP rfl] at h
              refine ⟨p, d, x, memo, msg, rs, rfl, hpm, h, hxp, ?_⟩
              rw [ha]; exact hb1
            · rw [ifN hrc] at h
              subst h
              exact absurd hfresh (by simp)
  | tokResolve i res =>
    exfalso
    simp only [stdStep, step] at he
    cases hpi : S.pend[i]? with
    | none => rw [hpi] at he; exact hnew he
    | some e' =>
      rw [hpi] at he
      dsimp only at he
      cases hro : resOf e' res with
      | none => rw [hro] at he; exact hnew he
      | some r =>
        rw [hro] at he
        dsimp only at he
        cases hx : exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e'.sender e'.receiver e'.amount, [r]⟩ with
        | none => rw [hx] at he; exact hnew (List.mem_of_mem_eraseIdx he)
        | some o =>
          rw [hx] at he
          dsimp only at he
          obtain ⟨hcalls, _⟩ := resolve_exec hx
          rw [hcalls] at he
          simp only [annThird, List.map_nil, List.append_nil] at he
          exact hnew (List.mem_of_mem_eraseIdx he)
  | tokResolveFails i =>
    exfalso
    simp only [stdStep, step] at he
    cases hpi : S.pend[i]? with
    | none => rw [hpi] at he; exact hnew he
    | some e' =>
      rw [hpi] at he
      dsimp only at he
      cases hro : resOf e' .failed with
      | none => rw [hro] at he; exact hnew he
      | some r => rw [hro] at he; exact hnew (List.mem_of_mem_eraseIdx he)
  | tokNearIn x =>
    exfalso
    simp only [stdStep, step] at he
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx] at he; exact hnew he
    · rw [ifN hx] at he; exact hnew he
  | onTransfer i recv ok =>
    exfalso
    simp only [stdStep, step] at he
    cases hpi : S.pend[i]? with
    | none => rw [hpi] at he; exact hnew he
    | some e' =>
      rw [hpi] at he
      dsimp only at he
      by_cases hg : e'.receiver = K.me ∧ e'.ann = .dep none
      · rw [ifP hg] at he
        split at he
        · rcases List.mem_or_eq_of_mem_set he with h | h
          · exact hnew h
          · subst h; simp at hfresh
        · rcases List.mem_or_eq_of_mem_set he with h | h
          · exact hnew h
          · subst h; simp at hfresh
      · rw [ifN hg] at he; exact hnew he
  | ftWithdraw via w =>
    exfalso
    simp only [stdStep, step] at he
    split at he
    · exact hnew he
    · split at he <;> exact hnew he
  | doFtWithdraw j ok =>
    exfalso
    simp only [stdStep, step] at he
    split at he
    · exact hnew he
    · split at he <;> exact hnew he
  | tokXfer j =>
    exfalso
    simp only [stdStep, step] at he
    split at he
    · exact hnew he
    · split at he
      · exact hnew he
      · rcases List.mem_append.mp he with h | h
        · exact hnew h
        · simp only [annWd, List.mem_map] at h
          obtain ⟨q, _, rfl⟩ := h
          simp at hfresh
  | tokXferFails j =>
    exfalso
    simp only [stdStep, step] at he
    split at he <;> exact hnew he
  | meStorageDeposit acc d =>
    exfalso
    simp only [stdStep, step] at he
    cases hx : exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc) none, []⟩ with
    | none => rw [hx] at he; exact hnew he
    | some o =>
      rw [hx] at he
      dsimp only at he
      obtain ⟨_, hcalls⟩ := sd_exec hx
      rw [hcalls] at he
      simp only [annThird, List.map_nil, List.append_nil] at he
      exact hnew he
  | resolveWd k =>
    exfalso
    simp only [stdStep, step] at he
    split at he
    · exact hnew he
    · split at he <;> exact hnew he
  | resolveWdFails k => exact absurd he hnew
  | move auth src dst amt =>
    exfalso
    simp only [stdStep, step] at he
    split at he <;> exact hnew he
  | admin a => exact absurd he hnew

/-- **T3, the tokens are there before the credit.** In a reachable state, for every transfer
    to the contract that is not credited yet, the contract's token balance already covers the
    whole ledger plus that amount, and the credit itself cannot fail (no overflow is possible).
    So after the credit the ledger is still covered. -/
theorem T3_covered (K : Cfg) (S : World) (h : Reach K S) (i : Nat) (e : Pend)
    (hpi : S.pend[i]? = some e) (hfresh : e.ann = .dep none) (recv : Acct) :
    total S.L.bals + e.amount ≤ bal S.c.accts K.me ∧
    ∃ L', credit S.L recv e.amount = some L' := by
  have hI := inv_reach h
  have hT := ProvedFT.inv_reach (tok_reach h)
  have hb := hI.backed
  have hmem := List.mem_of_getElem? hpi
  have hw := le_sumBy depW hmem
  rw [depW_fresh hfresh] at hw
  have hmax := held_le_max h
  have hcons := hI.cons
  have hbt := bal_le_total S.L.bals recv
  have hpos : 0 < e.amount :=
    (hT.pend e.raw (by simp only [toSys]; exact List.mem_map_of_mem hmem)).2
  unfold owed at hb
  exact ⟨by omega, _, credit_of hpos (by omega) (by omega)⟩

/-- **T1, the contract can always pay.** In a reachable state the contract's token balance
    covers every withdrawal whose token receipt has not executed yet, on top of the whole
    ledger: the token transfer of a withdrawal never fails for lack of the contract's tokens. -/
theorem T1_can_pay (K : Cfg) (S : World) (h : Reach K S) (j : Nat) (w : Wd)
    (hj : S.outbox[j]? = some w) : total S.L.bals + w.amount ≤ bal S.c.accts K.me := by
  have hI := inv_reach h
  have hb := hI.backed
  have hw := le_sumBy Wd.amount (List.mem_of_getElem? hj)
  rw [hI.cons] at hb
  unfold owed at hb
  omega

/-! ## T4 Who can lower a ledger balance -/

/-- **T4. Who can lower a ledger balance.** If a step lowers `u`'s ledger balance for the
    token, it is one of six, each with the condition the contract checks:
    1. `ft_withdraw` called by `u` itself — not paused, `u` not locked, auth by predecessor on;
    2. an `FtWithdraw` intent for `u` (signed with a key of `u`; the signature check is outside
       the model) — intents not paused, `u` not locked;
    3. `ft_force_withdraw` by a holder of `DAO` or `UnrestrictedWithdrawer` — no pause or lock
       stops it;
    4. an internal transfer authorised by `u` (its own `mt_transfer*` call or signed intent;
       outside the model) — `u` not locked;
    5. the refund of an `mt_transfer_call` made to `u` (`mt_resolve_transfer`);
    6. `mt_force_transfer*` by a holder of `DAO` or `UnrestrictedWithdrawer`. -/
theorem T4_who_can_lower (K : Cfg) (S : World) (u : Acct) (st : Step)
    (hlt : bal (stdStep K S st).L.bals u < bal S.L.bals u) :
    (∃ w, st = .ftWithdraw (.method u) w ∧ w.owner = u ∧
      S.L.ctl.isPaused "ft_withdraw" = false ∧ S.L.ctl.authOff.contains u = false ∧
      S.L.ctl.locked.contains u = false) ∨
    (∃ w, st = .ftWithdraw .intent w ∧ w.owner = u ∧ S.L.ctl.isPaused "intents" = false ∧
      S.L.ctl.locked.contains u = false) ∨
    (∃ who w, st = .ftWithdraw (.force who) w ∧ w.owner = u ∧
      S.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) ∨
    (∃ dst amt, st = .move .owner u dst amt ∧ S.L.ctl.locked.contains u = false) ∨
    (∃ dst amt, st = .move .refund u dst amt) ∨
    (∃ who dst amt, st = .move (.force who) u dst amt ∧
      S.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) := by
  rcases ledger_step K S st with h | ⟨i, recv, e, L', rfl, hpi, h1, h2, h3, hcr, hL⟩ |
      ⟨via, w, L', rfl, hs, hL⟩ | ⟨k, r, L', rfl, hk, _, hcr, hL⟩ |
      ⟨auth, src, dst, amt, L', rfl, hm, hL⟩ | ⟨a, rfl, hL⟩
  · rw [h] at hlt; omega
  · exfalso
    obtain ⟨_, _, _, rfl⟩ := credit_some hcr
    rw [hL] at hlt
    simp only at hlt
    by_cases hu : recv = u
    · subst hu; rw [bal_set_self] at hlt; omega
    · rw [bal_set_ne _ _ hu] at hlt; omega
  · rw [hL] at hlt
    obtain ⟨hown, hoth, _, _⟩ := T2_debit S.L L' via w hs
    have hwu : w.owner = u := by
      by_cases hwu : u = w.owner
      · exact hwu.symm
      · rw [hoth u hwu] at hlt; omega
    obtain ⟨hvia, _, hd⟩ := startWithdraw_some hs
    obtain ⟨_, hlock, _, _, _⟩ := debit_some hd
    cases via with
    | method p =>
      left
      simp only [Via.ok, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        Option.isNone_iff_eq_none] at hvia
      obtain ⟨⟨⟨hp, _⟩, hpa⟩, hau⟩ := hvia
      rw [hwu] at hp
      subst hp
      refine ⟨w, rfl, hwu, hpa, hau, ?_⟩
      rw [hwu] at hlock
      simpa [Via.forced] using hlock
    | intent =>
      right; left
      simp only [Via.ok, Bool.not_eq_true'] at hvia
      refine ⟨w, rfl, hwu, hvia, ?_⟩
      rw [hwu] at hlock
      simpa [Via.forced] using hlock
    | force who =>
      right; right; left
      simp only [Via.ok, Bool.and_eq_true] at hvia
      exact ⟨who, w, rfl, hwu, hvia.1⟩
  · exfalso
    obtain ⟨_, _, _, rfl⟩ := credit_some hcr
    rw [hL] at hlt
    simp only at hlt
    by_cases hu : r.owner = u
    · rw [← hu, bal_set_self] at hlt; omega
    · rw [bal_set_ne _ _ hu] at hlt; omega
  · obtain ⟨hne, _, hauth, hle, _, rfl⟩ := moveBal_some hm
    rw [hL] at hlt
    simp only at hlt
    have hsu : src = u := by
      by_cases hsu : src = u
      · exact hsu
      · exfalso
        by_cases hdu : dst = u
        · subst hdu; rw [bal_set_self] at hlt; omega
        · rw [bal_set_ne _ _ hdu, bal_set_ne _ _ hsu] at hlt; omega
    subst hsu
    right; right; right
    cases auth with
    | owner =>
      left
      refine ⟨dst, amt, rfl, ?_⟩
      simpa [MoveAuth.ok] using hauth
    | refund => right; left; exact ⟨dst, amt, rfl⟩
    | force who => right; right; exact ⟨who, dst, amt, rfl, by simpa [MoveAuth.ok] using hauth⟩
  · rw [hL] at hlt; simp only at hlt; omega

/-- **T4, the switches.** Only an `admin` step changes pauses, locks, the auth flags or the
    roles. -/
theorem T4_switches (K : Cfg) (S : World) (st : Step) (hne : ∀ a, st ≠ .admin a) :
    (stdStep K S st).L.ctl = S.L.ctl := by
  rcases ledger_step K S st with h | ⟨i, recv, e, L', rfl, hpi, h1, h2, h3, hcr, hL⟩ |
      ⟨via, w, L', rfl, hs, hL⟩ | ⟨k, r, L', rfl, hk, _, hcr, hL⟩ |
      ⟨auth, src, dst, amt, L', rfl, hm, hL⟩ | ⟨a, rfl, hL⟩
  · rw [h]
  · obtain ⟨_, _, _, rfl⟩ := credit_some hcr; rw [hL]
  · rw [hL]; exact (T2_debit S.L L' via w hs).2.2.2
  · obtain ⟨_, _, _, rfl⟩ := credit_some hcr; rw [hL]
  · obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm; rw [hL]
  · exact absurd rfl (hne a)

/-- **T4, who may pause.** The set of paused features changes only through `pa_pause_feature`
    by a holder of `DAO` or `PauseManager`, or `pa_unpause_feature` by a holder of `DAO` or
    `UnpauseManager`. -/
theorem T4_pause_power (c : Ctl) (a : Admin) (h : (adminStep c a).paused ≠ c.paused) :
    (∃ who key, a = .pause who key ∧ c.any who [.DAO, .PauseManager] = true) ∨
    (∃ who key, a = .unpause who key ∧ c.any who [.DAO, .UnpauseManager] = true) := by
  cases a with
  | pause who key =>
    left
    by_cases hr : c.any who [.DAO, .PauseManager] = true
    · exact ⟨who, key, rfl, hr⟩
    · simp [adminStep, hr] at h
  | unpause who key =>
    right
    by_cases hr : c.any who [.DAO, .UnpauseManager] = true
    · exact ⟨who, key, rfl, hr⟩
    · simp [adminStep, hr] at h
  | lock who x => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | unlock who x => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | authOffSelf x =>
    exfalso; simp only [adminStep, setAuth] at h; split at h <;> first | exact h rfl | (split at h <;> exact h rfl)
  | authIntent x en =>
    exfalso; simp only [adminStep, setAuth] at h; split at h <;> first | exact h rfl | (split at h <;> exact h rfl)
  | authForce who x en =>
    exfalso; simp only [adminStep, setAuth] at h; split at h <;> first | exact h rfl | (split at h <;> exact h rfl)
  | acl roles => exact absurd rfl h

/-- **T4, who may lock.** The set of locked accounts changes only through
    `force_lock_account` / `force_unlock_account` by a holder of the listed roles. -/
theorem T4_lock_power (c : Ctl) (a : Admin) (h : (adminStep c a).locked ≠ c.locked) :
    (∃ who x, a = .lock who x ∧
      c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager] = true) ∨
    (∃ who x, a = .unlock who x ∧
      c.any who [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager] = true) := by
  cases a with
  | lock who x =>
    left
    by_cases hr : c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager] = true
    · exact ⟨who, x, rfl, hr⟩
    · simp [adminStep, hr] at h
  | unlock who x =>
    right
    by_cases hr : c.any who [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager] = true
    · exact ⟨who, x, rfl, hr⟩
    · simp [adminStep, hr] at h
  | pause who key => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | unpause who key => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | authOffSelf x =>
    exfalso; simp only [adminStep, setAuth] at h; split at h <;> first | exact h rfl | (split at h <;> exact h rfl)
  | authIntent x en =>
    exfalso; simp only [adminStep, setAuth] at h; split at h <;> first | exact h rfl | (split at h <;> exact h rfl)
  | authForce who x en =>
    exfalso; simp only [adminStep, setAuth] at h; split at h <;> first | exact h rfl | (split at h <;> exact h rfl)
  | acl roles => exact absurd rfl h

end Intents
