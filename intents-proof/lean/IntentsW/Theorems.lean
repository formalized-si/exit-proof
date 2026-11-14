/-
  The statements about the ledger of the token id `nep141:<wNEAR>`, composed with the proved
  wNEAR model.

  * W1 backing            `W1_backing`, `W1_ledger_covered`, `W1_kept`, `W1_supply`,
                          `W1_quiet`, `W1_can_pay`, `W1_can_unwrap`
  * the token part        `tok_inv` (the invariant of the proved wNEAR model holds for the token
                          in every reachable state of this world), `held_le_max`
  * W2 settlement         `W2_debit`, `W2_settles`, `W2_no_callback`
  * W3 deposits           `W3_credit_only_on_arrival`, `W3_arrival`, `W3_covered`
  * W4 who can lower      `ledger_step`, `W4_who_can_lower`, `W4_switches`
                          (who may pause and lock: `Intents.T4_pause_power`,
                          `Intents.T4_lock_power`, statements about `adminStep` alone)

  The unwrap paths (`near_withdraw` and the NEAR sent on) are in `IntentsW/Native.lean`.
  Reachable states (`Reach`) start from `Init` and take any sequence of steps of
  `IntentsW/World.lean`.
-/
import IntentsW.Backing

namespace IntentsW
open ProvedFT (Acct Accts bal set total U128_MAX bal_set_self bal_set_ne bal_le_total)
open Intents

/-! ## W1 Backing -/

/-- wNEAR debited from the ledger whose settlement is not over, each at its full amount:
    unwraps not burned yet, withdrawals of wNEAR between the debit and `ft_resolve_withdraw`. -/
def debitedInFlight (S : World) : Nat :=
  sumBy Job.owedTok S.jobs + sumBy Ready.owedTok S.ready + sumBy Wd.amount S.outbox +
    sumBy wdAmt S.pend + sumBy Rs.amount S.resolves

/-- What those withdrawals have already moved out of the contract's wNEAR balance. -/
def movedOut (S : World) : Nat := sumBy wdAmt S.pend + sumBy Rs.left S.resolves

/-- Transfers to the contract that wNEAR may still take back: `ft_on_transfer` has not credited
    them. -/
def uncredited (S : World) : Nat := sumBy depW S.pend

/-- **W1 Backing.** In every reachable state, for the token id `nep141:<wNEAR>`: the sum of the
    ledger balances, plus what is debited and still in flight (at full amounts), plus the
    incoming transfers not credited yet, plus the wNEAR debited for unwraps whose
    `near_withdraw` failed, is at most the contract's wNEAR balance plus what the withdrawals in
    flight have already moved out. -/
theorem W1_backing (K : Cfg) (S : World) (h : Reach K S) :
    total S.L.bals + debitedInFlight S + uncredited S + S.uKept ≤
      WNear.bal S.c.accts K.me + movedOut S := by
  have hI := inv_reach h
  have hb := hI.backed
  have hs : sumBy Rs.amount S.resolves = sumBy Rs.unsettled S.resolves + sumBy Rs.left S.resolves :=
    sumBy_split Rs.amount Rs.left (fun r hr => (hI.rs r hr).1)
  rw [hI.cons] at hb
  unfold owed at hb
  unfold debitedInFlight movedOut uncredited
  omega

/-- **W1, the plain reading.** In every reachable state the sum of the ledger balances of
    `nep141:<wNEAR>` is at most the wNEAR balance of the contract — with anything in flight, at
    any point of any interleaving, whichever receipts failed. -/
theorem W1_ledger_covered (K : Cfg) (S : World) (h : Reach K S) :
    total S.L.bals ≤ WNear.bal S.c.accts K.me := by
  have hI := inv_reach h
  have hb := hI.backed
  rw [hI.cons] at hb
  omega

/-- **W1, what a failed unwrap leaves.** The wNEAR debited for unwraps whose `near_withdraw`
    receipt failed is still in the contract's wNEAR balance, on top of the whole ledger: held,
    and assigned to nobody. -/
theorem W1_kept (K : Cfg) (S : World) (h : Reach K S) :
    total S.L.bals + S.uKept ≤ WNear.bal S.c.accts K.me := by
  have hI := inv_reach h
  have hb := hI.backed
  rw [hI.cons] at hb
  omega

/-- **W1, the ledger's own books.** `total_supplies` for the id is the sum of the account
    balances. -/
theorem W1_supply (K : Cfg) (S : World) (h : Reach K S) : S.L.supply = total S.L.bals :=
  (inv_reach h).cons

/-- Nothing of the contract is in flight. -/
def Quiet (K : Cfg) (S : World) : Prop :=
  S.jobs = [] ∧ S.ready = [] ∧ S.outbox = [] ∧ S.resolves = [] ∧
  ∀ e ∈ S.pend, e.sender ≠ K.me ∧ e.receiver ≠ K.me

/-- In a quiet state the in-flight terms of `W1_backing` vanish. -/
theorem W1_quiet (K : Cfg) (S : World) (h : Reach K S) (hq : Quiet K S) :
    debitedInFlight S = 0 ∧ uncredited S = 0 ∧ movedOut S = 0 ∧
    total S.L.bals ≤ WNear.bal S.c.accts K.me := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hq
  have hI := inv_reach h
  have hw : sumBy wdAmt S.pend = 0 := by
    apply sumBy_eq_zero
    intro e he
    have hok := (hI.pend e he).1
    unfold PendOK at hok
    unfold wdAmt
    cases hann : e.ann with
    | other => rfl
    | dep s => rfl
    | wd o => rw [hann] at hok; exact absurd hok.1 (h4 e he).1
  have hd : sumBy depW S.pend = 0 := by
    apply sumBy_eq_zero
    intro e he
    have hok := (hI.pend e he).1
    unfold PendOK at hok
    cases hann : e.ann with
    | other => exact depW_other hann
    | dep s => rw [hann] at hok; exact absurd hok (h4 e he).2
    | wd o => exact depW_wd hann
  refine ⟨?_, hd, ?_, W1_ledger_covered K S h⟩
  · unfold debitedInFlight; rw [h0, h1, h2, h3, hw]; rfl
  · unfold movedOut; rw [h3, hw]; rfl

/-- **W1, the contract can always pay.** The contract's wNEAR balance covers every withdrawal
    whose token receipt has not executed yet, on top of the whole ledger. -/
theorem W1_can_pay (K : Cfg) (S : World) (h : Reach K S) (j : Nat) (w : Wd)
    (hj : S.outbox[j]? = some w) : total S.L.bals + w.amount ≤ WNear.bal S.c.accts K.me := by
  have hI := inv_reach h
  have hb := hI.backed
  have hw := le_sumBy Wd.amount (List.mem_of_getElem? hj)
  rw [hI.cons] at hb
  unfold owed at hb
  omega

/-- **W1, the contract can always burn.** The contract's wNEAR balance covers every unwrap
    whose `near_withdraw` has not executed yet, on top of the whole ledger; the amount is
    positive. -/
theorem W1_can_unwrap (K : Cfg) (S : World) (h : Reach K S) (j : Nat) (u : Job)
    (hj : S.jobs[j]? = some u) :
    total S.L.bals + u.amount ≤ WNear.bal S.c.accts K.me ∧ 0 < u.amount := by
  have hI := inv_reach h
  have hb := hI.backed
  have hmem := List.mem_of_getElem? hj
  have hw := le_sumBy Job.owedTok hmem
  have e1 : Job.owedTok u = u.amount + u.fwd.wdAmount := rfl
  rw [hI.cons] at hb
  unfold owed at hb
  exact ⟨by omega, (hI.jobs u hmem).1⟩

/-! ## The token part keeps the invariant of the proved wNEAR model -/

theorem batch_inv {E : WNear.Env} {c : WNear.St} {me : Acct} {w : Wd} {o : WNear.Out}
    (hs : WNear.Pre c) (hsol : c.supply + c.accts.length * E.minBal + E.base ≤ c.near)
    (h : xferBatchW E me c w = some o) :
    WNear.Pre o.st ∧ o.st.supply + o.st.accts.length * E.minBal + E.base ≤ o.st.near ∧
      o.st.near ≤ E.cap := by
  unfold xferBatchW at h
  cases hsd : w.sd with
  | none =>
    simp only [hsd] at h
    exact WNear.exec_inv hs hsol h
  | some d =>
    simp only [hsd] at h
    cases h1 : WNear.exec E c ⟨me, d, .storage_deposit (some w.receiver), []⟩ with
    | none => simp [h1] at h
    | some o1 =>
      simp only [h1] at h
      cases h2 : WNear.exec E o1.st ⟨me, 1, xferMethodW w, []⟩ with
      | none => simp [h2] at h
      | some o2 =>
        simp only [h2, Option.some.injEq] at h
        subst h
        obtain ⟨a1, a2, _⟩ := WNear.exec_inv hs hsol h1
        have h3 := WNear.exec_inv a1 a2 h2
        exact h3

/-- Every step of the world keeps the invariant of the wNEAR model on the token's side: the
    token state changes only through `WNear.exec` (one receipt, or the two actions of one
    receipt) or by NEAR arriving. -/
theorem tok_inv_step (K : Cfg) {S : World} (hT : WNear.Inv K.tok (toSys S)) (st : Step) :
    WNear.Inv K.tok (toSys (step K S st)) := by
  have hpre : WNear.Pre S.c := hT.pre
  have hsol : S.c.supply + S.c.accts.length * K.tok.minBal + K.tok.base ≤ S.c.near := hT.solvent
  have hcap : S.c.near ≤ K.tok.cap := hT.cap
  cases st with
  | tokCall p d m rs =>
    simp only [step]
    by_cases hpm : p = K.me ∨ p = K.tok.self
    · rw [ifP hpm]; exact hT
    · rw [ifN hpm]
      cases he : WNear.exec K.tok S.c ⟨p, d, m, rs⟩ with
      | none => exact hT
      | some o =>
        obtain ⟨a, b, c⟩ := WNear.exec_inv hpre hsol he
        exact ⟨a, b, c⟩
  | tokResolve i res =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact hT
    | some e =>
      dsimp only
      cases hro : resOfW e res with
      | none => exact hT
      | some r =>
        dsimp only
        cases he : WNear.exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [r]⟩ with
        | none => exact ⟨hpre, hsol, hcap⟩
        | some o =>
          obtain ⟨a, b, c⟩ := WNear.exec_inv hpre hsol he
          exact ⟨a, b, c⟩
  | tokResolveFails i =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact hT
    | some e =>
      dsimp only
      cases hro : resOfW e .failed with
      | none => exact hT
      | some r => exact ⟨hpre, hsol, hcap⟩
  | tokNearIn x =>
    simp only [step]
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx]
      exact ⟨⟨hpre.nodup, hpre.cons, hpre.bound⟩, by simp only [toSys]; omega,
        by simp only [toSys]; omega⟩
    · rw [ifN hx]; exact hT
  | onTransfer i recv ok =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact hT
    | some e =>
      dsimp only
      by_cases hg : e.receiver = K.me ∧ e.ann = .dep none
      · rw [ifP hg]
        split <;> exact ⟨hpre, hsol, hcap⟩
      · rw [ifN hg]; exact hT
  | ftWithdraw via w =>
    simp only [step]
    cases hs : startWithdrawW S.L via w with
    | none => exact hT
    | some L' =>
      dsimp only
      split <;> exact ⟨hpre, hsol, hcap⟩
  | unwrap owner x f =>
    simp only [step]
    by_cases hf : f.isWd = true
    · rw [ifP hf]; exact hT
    · rw [ifN hf]
      cases hs : startUnwrap S.L owner x with
      | none => exact hT
      | some L' => exact ⟨hpre, hsol, hcap⟩
  | nearWithdraw j =>
    simp only [step]
    cases hjj : S.jobs[j]? with
    | none => exact hT
    | some u =>
      dsimp only
      cases he : WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ with
      | none => exact ⟨hpre, hsol, hcap⟩
      | some o =>
        obtain ⟨a, b, c⟩ := WNear.exec_inv hpre hsol he
        exact ⟨a, b, c⟩
  | nearWithdrawFails j =>
    simp only [step]
    cases hjj : S.jobs[j]? with
    | none => exact hT
    | some u => exact ⟨hpre, hsol, hcap⟩
  | doJob k ok =>
    simp only [step]
    cases hk : S.ready[k]? with
    | none => exact hT
    | some r =>
      dsimp only
      split <;> exact ⟨hpre, hsol, hcap⟩
  | tokXfer j =>
    simp only [step]
    cases hjj : S.outbox[j]? with
    | none => exact hT
    | some w =>
      dsimp only
      cases hx : xferBatchW K.tok K.me S.c w with
      | none => exact ⟨hpre, hsol, hcap⟩
      | some o =>
        obtain ⟨a, b, c⟩ := batch_inv hpre hsol hx
        exact ⟨a, b, c⟩
  | tokXferFails j =>
    simp only [step]
    cases hjj : S.outbox[j]? with
    | none => exact hT
    | some w => exact ⟨hpre, hsol, hcap⟩
  | meStorageDeposit acc d =>
    simp only [step]
    cases he : WNear.exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc), []⟩ with
    | none => exact hT
    | some o =>
      obtain ⟨a, b, c⟩ := WNear.exec_inv hpre hsol he
      exact ⟨a, b, c⟩
  | resolveWd k =>
    simp only [step]
    cases hk : S.resolves[k]? with
    | none => exact hT
    | some r =>
      dsimp only
      split <;> exact ⟨hpre, hsol, hcap⟩
  | resolveWdFails k => exact ⟨hpre, hsol, hcap⟩
  | move auth src dst amt =>
    simp only [step]
    split
    · exact hT
    · exact ⟨hpre, hsol, hcap⟩
  | admin a => exact ⟨hpre, hsol, hcap⟩

/-- **The token in the two-contract world satisfies the invariant of the proved wNEAR model**
    (no repeated keys, `total_supply` = sum of balances, solvency) at every point of every
    interleaving with the Intents contract. -/
theorem tok_inv {K : Cfg} {S : World} (h : Reach K S) : WNear.Inv K.tok (toSys S) := by
  induction h with
  | init S h => exact h.tok
  | step st _ ih => exact tok_inv_step K ih st

/-- The contract's wNEAR balance fits `u128` (from wNEAR's conservation). -/
theorem held_le_max {K : Cfg} {S : World} (h : Reach K S) :
    WNear.bal S.c.accts K.me ≤ U128_MAX := by
  have hT := tok_inv h
  have h1 : S.c.supply = WNear.total S.c.accts := hT.pre.cons
  have h2 : S.c.supply ≤ WNear.U128_MAX := hT.pre.bound
  have h3 := WNear.bal_le_total S.c.accts K.me
  have h4 : WNear.U128_MAX = U128_MAX := rfl
  omega

/-! ## How the ledger can change -/

/-- **Every change of the ledger is one of six.** A step leaves the ledger as it is, or it is:
    a credit in `ft_on_transfer` for a transfer to the contract whose settlement is in flight
    and not yet answered; the debit that starts a withdrawal of wNEAR; the debit that starts an
    unwrap; a refund in `ft_resolve_withdraw`; an internal move; or a change of the switches. -/
theorem ledger_step (K : Cfg) (S : World) (st : Step) :
    (step K S st).L = S.L ∨
    (∃ i recv e L', st = .onTransfer i recv true ∧ S.pend[i]? = some e ∧ e.receiver = K.me ∧
      e.ann = .dep none ∧ S.L.ctl.isPaused "ft_on_transfer" = false ∧
      credit S.L recv e.amount = some L' ∧ (step K S st).L = L') ∨
    (∃ via w L', st = .ftWithdraw via w ∧ startWithdrawW S.L via w = some L' ∧
      (step K S st).L = L') ∨
    (∃ owner x f L', st = .unwrap owner x f ∧ startUnwrap S.L owner x = some L' ∧
      (step K S st).L = L') ∨
    (∃ k r L', st = .resolveWd k ∧ S.resolves[k]? = some r ∧ r.refund ≠ 0 ∧
      credit S.L r.owner r.refund = some L' ∧ (step K S st).L = L') ∨
    (∃ auth src dst amt L', st = .move auth src dst amt ∧
      moveBal S.L auth src dst amt = some L' ∧ (step K S st).L = L') ∨
    (∃ a, st = .admin a ∧ (step K S st).L = { S.L with ctl := adminStep S.L.ctl a }) := by
  cases st with
  | tokCall p d m rs =>
    left; simp only [step]
    split
    · rfl
    · split <;> rfl
  | tokResolve i res =>
    left; simp only [step]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | tokResolveFails i =>
    left; simp only [step]
    split
    · rfl
    · split <;> rfl
  | tokNearIn x =>
    left; simp only [step]
    split <;> rfl
  | onTransfer i recv ok =>
    simp only [step]
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
    simp only [step]
    cases hs : startWithdrawW S.L via w with
    | none => left; rfl
    | some L' =>
      right; right; left
      refine ⟨via, w, L', rfl, hs, ?_⟩
      dsimp only
      split <;> rfl
  | unwrap owner x f =>
    simp only [step]
    by_cases hf : f.isWd = true
    · rw [ifP hf]; left; rfl
    · rw [ifN hf]
      cases hs : startUnwrap S.L owner x with
      | none => left; rfl
      | some L' => right; right; right; left; exact ⟨owner, x, f, L', rfl, hs, rfl⟩
  | nearWithdraw j =>
    left; simp only [step]
    split
    · rfl
    · split <;> rfl
  | nearWithdrawFails j =>
    left; simp only [step]
    split <;> rfl
  | doJob k ok =>
    left; simp only [step]
    split
    · rfl
    · split <;> rfl
  | tokXfer j =>
    left; simp only [step]
    split
    · rfl
    · split <;> rfl
  | tokXferFails j =>
    left; simp only [step]
    split <;> rfl
  | meStorageDeposit acc d =>
    left; simp only [step]
    split <;> rfl
  | resolveWd k =>
    simp only [step]
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
          right; right; right; right; left
          exact ⟨k, r, L', rfl, hk, h0, hres, rfl⟩
  | resolveWdFails k => left; rfl
  | move auth src dst amt =>
    simp only [step]
    cases hm : moveBal S.L auth src dst amt with
    | none => left; rfl
    | some L' =>
      right; right; right; right; right; left; exact ⟨auth, src, dst, amt, L', rfl, hm, rfl⟩
  | admin a => right; right; right; right; right; right; exact ⟨a, rfl, rfl⟩

/-! ## W2 Withdrawal settles exactly -/

/-- **W2, the debit.** Starting a withdrawal of `w.amount` wNEAR takes exactly that amount —
    plus the storage deposit when the intent carries one (the same token id) — from the owner's
    ledger balance and from the ledger total, and touches no other balance. -/
theorem W2_debit (L L' : Ledger) (via : Via) (w : Wd) (h : startWithdrawW L via w = some L') :
    bal L'.bals w.owner + (w.amount + w.sd.getD 0) = bal L.bals w.owner ∧
    (∀ a, a ≠ w.owner → bal L'.bals a = bal L.bals a) ∧
    L'.supply + (w.amount + w.sd.getD 0) = L.supply ∧ L'.ctl = L.ctl := by
  obtain ⟨_, _, _, h4, h5, h6, _, h8⟩ := startWithdrawW_spec h
  exact ⟨h5, h6, h4, h8⟩

/-- **W2. Withdrawal settles exactly.** In a reachable state, when a ready
    `ft_resolve_withdraw` of a withdrawal of `r.amount` wNEAR runs — whatever happened to the
    token transfer before — it cannot fail, it credits the owner exactly `r.refund` and nobody
    else, and the amount that stays debited, `r.amount - r.refund`, is exactly what left the
    contract's wNEAR balance (`r.left`). The single exception, as for any token: the
    `ft_transfer_call` receipt itself failed (or `do_ft_withdraw` before it), so nothing left,
    and still nothing is refunded. -/
theorem W2_settles (K : Cfg) (S : World) (h : Reach K S) (k : Nat) (r : Rs)
    (hk : S.resolves[k]? = some r) :
    let S' := step K S (.resolveWd k)
    S'.resolves = S.resolves.eraseIdx k ∧
    bal S'.L.bals r.owner = bal S.L.bals r.owner + r.refund ∧
    (∀ a, a ≠ r.owner → bal S'.L.bals a = bal S.L.bals a) ∧
    S'.L.supply = S.L.supply + r.refund ∧
    (r.amount - r.refund = r.left ∨
      (r.isCall = true ∧ r.res = ProvedFT.PR.failed ∧ r.left = 0 ∧ r.refund = 0)) := by
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
      (r.isCall = true ∧ r.res = ProvedFT.PR.failed ∧ r.left = 0 ∧ r.refund = 0) := by
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

/-- **W2, when the resolve callback itself does not run** (out of gas, log too long): the
    ledger is left as it is. The owner stays debited the full amount, also the part that never
    left; that wNEAR remains in the contract's balance, assigned to nobody. -/
theorem W2_no_callback (K : Cfg) (S : World) (k : Nat) :
    let S' := step K S (.resolveWdFails k)
    S'.L = S.L ∧ S'.c = S.c ∧ S'.resolves = S.resolves.eraseIdx k :=
  ⟨rfl, rfl, rfl⟩

/-! ## W3 Deposits credit what arrived -/

/-- **W3. A credit happens only for what arrived.** If a step raises the ledger total of
    `nep141:<wNEAR>`, it is one of two:
    * the contract's `ft_on_transfer` for a wNEAR transfer to the contract whose settlement
      callback is in flight on wNEAR and not yet answered; the credit is exactly the amount of
      that transfer;
    * `ft_resolve_withdraw` giving back `r.refund` of a withdrawal of wNEAR debited before.
    In particular no step gives back wNEAR debited for an unwrap. -/
theorem W3_credit_only_on_arrival (K : Cfg) (S : World) (st : Step)
    (hgt : S.L.supply < (step K S st).L.supply) :
    (∃ i recv e, st = .onTransfer i recv true ∧ S.pend[i]? = some e ∧ e.receiver = K.me ∧
      e.ann = .dep none ∧ S.L.ctl.isPaused "ft_on_transfer" = false ∧
      (step K S st).L.supply = S.L.supply + e.amount ∧
      bal (step K S st).L.bals recv = bal S.L.bals recv + e.amount ∧
      ∀ a, a ≠ recv → bal (step K S st).L.bals a = bal S.L.bals a) ∨
    (∃ k r, st = .resolveWd k ∧ S.resolves[k]? = some r ∧
      (step K S st).L.supply = S.L.supply + r.refund ∧
      bal (step K S st).L.bals r.owner = bal S.L.bals r.owner + r.refund) := by
  rcases ledger_step K S st with h | ⟨i, recv, e, L', rfl, hpi, h1, h2, h3, hcr, hL⟩ |
      ⟨via, w, L', rfl, hs, hL⟩ | ⟨owner, x, f, L', rfl, hs, hL⟩ | ⟨k, r, L', rfl, hk, _, hcr, hL⟩ |
      ⟨auth, src, dst, amt, L', rfl, hm, hL⟩ | ⟨a, rfl, hL⟩
  · rw [h] at hgt; omega
  · left
    obtain ⟨_, _, _, rfl⟩ := credit_some hcr
    rw [hL]
    refine ⟨i, recv, e, rfl, hpi, h1, h2, h3, rfl, ?_, fun a ha => ?_⟩
    · simp only; rw [bal_set_self]
    · simp only; rw [bal_set_ne _ _ (Ne.symm ha)]
  · rw [hL] at hgt
    obtain ⟨_, _, h3, _⟩ := W2_debit S.L L' via w hs
    omega
  · rw [hL] at hgt
    obtain ⟨_, _, hd⟩ := startUnwrap_some hs
    obtain ⟨_, _, _, _, rfl⟩ := debit_some hd
    simp only at hgt; omega
  · right
    obtain ⟨_, _, _, rfl⟩ := credit_some hcr
    rw [hL]
    exact ⟨k, r, rfl, hk, rfl, by simp only; rw [bal_set_self]⟩
  · rw [hL] at hgt
    obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm
    simp only at hgt; omega
  · rw [hL] at hgt; simp only at hgt; omega

/-- **W3, where such a transfer comes from.** A settlement callback of a transfer to the
    contract appears only when some other account's `ft_transfer_call` to the contract succeeds
    on wNEAR, and at that moment the contract's wNEAR balance has grown by exactly the amount
    the callback carries. -/
theorem W3_arrival (K : Cfg) (S : World) (st : Step) (e : Pend)
    (he : e ∈ (step K S st).pend) (hfresh : e.ann = .dep none) (hnew : e ∉ S.pend) :
    ∃ p d x rs, st = .tokCall p d (.ft_transfer_call K.me x) rs ∧
      p ≠ K.me ∧ e = ⟨p, K.me, x, .dep none⟩ ∧ 0 < x ∧
      WNear.bal (step K S st).c.accts K.me = WNear.bal S.c.accts K.me + x := by
  cases st with
  | tokCall p d m rs =>
    simp only [step] at he ⊢
    by_cases hpm : p = K.me ∨ p = K.tok.self
    · rw [ifP hpm] at he; exact absurd he hnew
    · rw [ifN hpm] at he ⊢
      have hp1 : p ≠ K.me := fun h => hpm (Or.inl h)
      cases hx : WNear.exec K.tok S.c ⟨p, d, m, rs⟩ with
      | none => rw [hx] at he; exact absurd he hnew
      | some o =>
        rw [hx] at he
        dsimp only at he ⊢
        obtain ⟨o0, hm, ha, _, _, hc, _⟩ := WNear.exec_some hx
        rcases List.mem_append.mp he with h | h
        · exact absurd h hnew
        · rcases WNear.calls_origin hm with h0 | ⟨rc, x, rfl, h1, hne, hb1, _⟩
          · rw [hc, h0] at h; simp [annThird] at h
          · rw [hc, h1] at h
            simp only [annThird, List.map_cons, List.map_nil, List.mem_singleton] at h
            by_cases hrc : rc = K.me
            · subst hrc
              rw [ifP rfl] at h
              refine ⟨p, d, x, rs, rfl, hp1, h, ftc_pos hm, ?_⟩
              rw [ha]; exact hb1
            · rw [ifN hrc] at h
              subst h
              exact absurd hfresh (by simp)
  | tokResolve i res =>
    exfalso
    simp only [step] at he
    cases hpi : S.pend[i]? with
    | none => rw [hpi] at he; exact hnew he
    | some e' =>
      rw [hpi] at he
      dsimp only at he
      cases hro : resOfW e' res with
      | none => rw [hro] at he; exact hnew he
      | some r =>
        rw [hro] at he
        dsimp only at he
        cases hx : WNear.exec K.tok S.c
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
    simp only [step] at he
    cases hpi : S.pend[i]? with
    | none => rw [hpi] at he; exact hnew he
    | some e' =>
      rw [hpi] at he
      dsimp only at he
      cases hro : resOfW e' .failed with
      | none => rw [hro] at he; exact hnew he
      | some r => rw [hro] at he; exact hnew (List.mem_of_mem_eraseIdx he)
  | tokNearIn x =>
    exfalso
    simp only [step] at he
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx] at he; exact hnew he
    · rw [ifN hx] at he; exact hnew he
  | onTransfer i recv ok =>
    exfalso
    simp only [step] at he
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
    simp only [step] at he
    split at he
    · exact hnew he
    · split at he <;> exact hnew he
  | unwrap owner x f =>
    exfalso
    simp only [step] at he
    split at he
    · exact hnew he
    · split at he <;> exact hnew he
  | nearWithdraw j =>
    exfalso
    simp only [step] at he
    cases hjj : S.jobs[j]? with
    | none => rw [hjj] at he; exact hnew he
    | some u =>
      rw [hjj] at he
      dsimp only at he
      cases hx : WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ with
      | none => rw [hx] at he; exact hnew he
      | some o =>
        rw [hx] at he
        dsimp only at he
        obtain ⟨_, _, _, hcalls, _⟩ := nw_exec hx
        rw [hcalls] at he
        simp only [annThird, List.map_nil, List.append_nil] at he
        exact hnew he
  | nearWithdrawFails j =>
    exfalso
    simp only [step] at he
    split at he <;> exact hnew he
  | doJob k ok =>
    exfalso
    simp only [step] at he
    split at he
    · exact hnew he
    · split at he <;> exact hnew he
  | tokXfer j =>
    exfalso
    simp only [step] at he
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
    simp only [step] at he
    split at he <;> exact hnew he
  | meStorageDeposit acc d =>
    exfalso
    simp only [step] at he
    cases hx : WNear.exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc), []⟩ with
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
    simp only [step] at he
    split at he
    · exact hnew he
    · split at he <;> exact hnew he
  | resolveWdFails k => exact absurd he hnew
  | move auth src dst amt =>
    exfalso
    simp only [step] at he
    split at he <;> exact hnew he
  | admin a => exact absurd he hnew

/-- **W3, the tokens are there before the credit.** In a reachable state, for every transfer
    to the contract that is not credited yet, the contract's wNEAR balance already covers the
    whole ledger plus that amount, and the credit itself cannot fail (no overflow is possible).
    So after the credit the ledger is still covered. -/
theorem W3_covered (K : Cfg) (S : World) (h : Reach K S) (i : Nat) (e : Pend)
    (hpi : S.pend[i]? = some e) (hfresh : e.ann = .dep none) (recv : Acct) :
    total S.L.bals + e.amount ≤ WNear.bal S.c.accts K.me ∧
    ∃ L', credit S.L recv e.amount = some L' := by
  have hI := inv_reach h
  have hb := hI.backed
  have hmem := List.mem_of_getElem? hpi
  have hw := le_sumBy depW hmem
  rw [depW_fresh hfresh] at hw
  have hmax := held_le_max h
  have hcons := hI.cons
  have hbt := bal_le_total S.L.bals recv
  have hpos : 0 < e.amount := (hI.pend e hmem).2 (by rw [hfresh]; simp)
  unfold owed at hb
  exact ⟨by omega, _, credit_of hpos (by omega) (by omega)⟩

/-! ## W4 Who can lower a ledger balance -/

/-- **W4. Who can lower a ledger balance of `nep141:<wNEAR>`.** If a step lowers `u`'s
    balance, it is one of seven, each with the condition the contract checks:
    1. `ft_withdraw` called by `u` itself — not paused, `u` not locked, auth by predecessor on;
    2. an `FtWithdraw` intent of wNEAR for `u` (signed with a key of `u`; the signature check
       is outside the model) — intents not paused, `u` not locked;
    3. `ft_force_withdraw` by a holder of `DAO` or `UnrestrictedWithdrawer` — no pause or lock
       stops it;
    4. an intent of `u` that unwraps (`NativeWithdraw`, `StorageDeposit`, `AuthCall` with a
       deposit, a withdrawal of another token id with `storage_deposit`; signed with a key of
       `u`, outside the model) — intents not paused, `u` not locked;
    5. an internal transfer authorised by `u` — `u` not locked;
    6. the refund of an `mt_transfer_call` made to `u` (`mt_resolve_transfer`);
    7. `mt_force_transfer*` by a holder of `DAO` or `UnrestrictedWithdrawer`. -/
theorem W4_who_can_lower (K : Cfg) (S : World) (u : Acct) (st : Step)
    (hlt : bal (step K S st).L.bals u < bal S.L.bals u) :
    (∃ w, st = .ftWithdraw (.method u) w ∧ w.owner = u ∧
      S.L.ctl.isPaused "ft_withdraw" = false ∧ S.L.ctl.authOff.contains u = false ∧
      S.L.ctl.locked.contains u = false) ∨
    (∃ w, st = .ftWithdraw .intent w ∧ w.owner = u ∧ S.L.ctl.isPaused "intents" = false ∧
      S.L.ctl.locked.contains u = false) ∨
    (∃ who w, st = .ftWithdraw (.force who) w ∧ w.owner = u ∧
      S.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) ∨
    (∃ x f, st = .unwrap u x f ∧ S.L.ctl.isPaused "intents" = false ∧
      S.L.ctl.locked.contains u = false) ∨
    (∃ dst amt, st = .move .owner u dst amt ∧ S.L.ctl.locked.contains u = false) ∨
    (∃ dst amt, st = .move .refund u dst amt) ∨
    (∃ who dst amt, st = .move (.force who) u dst amt ∧
      S.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) := by
  rcases ledger_step K S st with h | ⟨i, recv, e, L', rfl, hpi, h1, h2, h3, hcr, hL⟩ |
      ⟨via, w, L', rfl, hs, hL⟩ | ⟨owner, x, f, L', rfl, hs, hL⟩ | ⟨k, r, L', rfl, hk, _, hcr, hL⟩ |
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
    obtain ⟨hown, hoth, _, _⟩ := W2_debit S.L L' via w hs
    have hwu : w.owner = u := by
      by_cases hwu : u = w.owner
      · exact hwu.symm
      · rw [hoth u hwu] at hlt; omega
    obtain ⟨L1, hs1, _⟩ := startWithdrawW_some hs
    obtain ⟨hvia, _, hd⟩ := startWithdraw_some hs1
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
  · rw [hL] at hlt
    obtain ⟨hpz, _, hd⟩ := startUnwrap_some hs
    obtain ⟨_, hlock, _, _, rfl⟩ := debit_some hd
    simp only at hlt
    have hou : owner = u := by
      by_cases hou : owner = u
      · exact hou
      · rw [bal_set_ne _ _ hou] at hlt; omega
    subst hou
    right; right; right; left
    exact ⟨x, f, rfl, hpz, by simpa using hlock⟩
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
    right; right; right; right
    cases auth with
    | owner =>
      left
      refine ⟨dst, amt, rfl, ?_⟩
      simpa [MoveAuth.ok] using hauth
    | refund => right; left; exact ⟨dst, amt, rfl⟩
    | force who => right; right; exact ⟨who, dst, amt, rfl, by simpa [MoveAuth.ok] using hauth⟩
  · rw [hL] at hlt; simp only at hlt; omega

/-- **W4, the switches.** Only an `admin` step changes pauses, locks, the auth flags or the
    roles. -/
theorem W4_switches (K : Cfg) (S : World) (st : Step) (hne : ∀ a, st ≠ .admin a) :
    (step K S st).L.ctl = S.L.ctl := by
  rcases ledger_step K S st with h | ⟨i, recv, e, L', rfl, hpi, h1, h2, h3, hcr, hL⟩ |
      ⟨via, w, L', rfl, hs, hL⟩ | ⟨owner, x, f, L', rfl, hs, hL⟩ | ⟨k, r, L', rfl, hk, _, hcr, hL⟩ |
      ⟨auth, src, dst, amt, L', rfl, hm, hL⟩ | ⟨a, rfl, hL⟩
  · rw [h]
  · obtain ⟨_, _, _, rfl⟩ := credit_some hcr; rw [hL]
  · rw [hL]; exact (W2_debit S.L L' via w hs).2.2.2
  · obtain ⟨_, _, hd⟩ := startUnwrap_some hs
    obtain ⟨_, _, _, _, rfl⟩ := debit_some hd; rw [hL]
  · obtain ⟨_, _, _, rfl⟩ := credit_some hcr; rw [hL]
  · obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm; rw [hL]
  · exact absurd rfl (hne a)

end IntentsW
