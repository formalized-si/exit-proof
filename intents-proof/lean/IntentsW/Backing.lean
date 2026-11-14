/-
  Backing for the token id `nep141:<wNEAR>`: in every reachable state of the two-contract world
  the ledger never holds more than the contract's wNEAR balance, counting what is in flight.

  `Inv` is the inductive invariant, `inv_step` shows every step keeps it (any call by anyone,
  any callback with any outcome, any receipt failing before it runs). `Books` is the invariant
  of the unwrap bookkeeping. The statements for readers are in `IntentsW/Theorems.lean` and
  `IntentsW/Native.lean`.
-/
import IntentsW.TokenFacts

namespace IntentsW
open ProvedFT (Acct Accts bal set total U128_MAX bal_set_self bal_set_ne)
open Intents

/-! ### Specifications of the two new ledger functions -/

theorem startUnwrap_some {L L' : Ledger} {owner : Acct} {x : Nat}
    (h : startUnwrap L owner x = some L') :
    L.ctl.isPaused "intents" = false ∧ x ≤ U128_MAX ∧ debit L owner x false = some L' := by
  unfold startUnwrap at h
  by_cases hc : L.ctl.isPaused "intents" = false ∧ x ≤ U128_MAX
  · rw [ifP hc] at h; exact ⟨hc.1, hc.2, h⟩
  · rw [ifN hc] at h; exact absurd h (by simp)

theorem startWithdrawW_some {L L' : Ledger} {via : Via} {w : Wd}
    (h : startWithdrawW L via w = some L') :
    ∃ L1, startWithdraw L via w = some L1 ∧
      ((w.sd = none ∧ L' = L1) ∨
       (∃ d, w.sd = some d ∧ d ≤ U128_MAX ∧ debit L1 w.owner d via.forced = some L')) := by
  unfold startWithdrawW at h
  cases hs : startWithdraw L via w with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some L1 =>
    rw [hs] at h
    refine ⟨L1, rfl, ?_⟩
    cases hsd : w.sd with
    | none =>
      rw [hsd] at h
      exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
    | some d =>
      rw [hsd] at h
      dsimp only at h
      by_cases hd : d ≤ U128_MAX
      · rw [ifP hd] at h; exact Or.inr ⟨d, rfl, hd, h⟩
      · rw [ifN hd] at h; exact absurd h (by simp)

/-- A job in flight: a positive amount (a zero amount is rejected by `Contract::withdraw`), and
    the withdrawal it belongs to, if any, has a `u128` amount. -/
def JobOK (u : Job) : Prop := 0 < u.amount ∧ u.fwd.wdAmount ≤ U128_MAX

/-- A settlement callback that involves the contract carries a positive amount. -/
def PendPos (e : Pend) : Prop := e.ann ≠ .other → 0 < e.amount

/-- The invariant of every reachable state. -/
structure Inv (K : Cfg) (S : World) : Prop where
  /-- Ledger total, plus everything owed in flight, plus the wNEAR debited for unwraps whose
      `near_withdraw` failed, is covered by the wNEAR held. -/
  backed : S.L.supply + owed S + S.uKept ≤ WNear.bal S.c.accts K.me
  /-- `total_supplies[nep141:<wNEAR>]` is the sum of the ledger balances. -/
  cons : S.L.supply = total S.L.bals
  pend : ∀ e ∈ S.pend, PendOK K.me e ∧ PendPos e
  outbox : ∀ w ∈ S.outbox, w.amount ≤ U128_MAX
  jobs : ∀ u ∈ S.jobs, JobOK u
  ready : ∀ r ∈ S.ready, r.job.fwd.wdAmount ≤ U128_MAX
  rs : ∀ r ∈ S.resolves, RsOK r

theorem Inv.mk' {K : Cfg} {c : WNear.St} {pend : List Pend} {paid : List (Acct × Nat)}
    {L : Ledger} {jobs : List Job} {ready : List Ready} {outbox : List Wd} {resolves : List Rs}
    {uD uB uK nG nF : Nat}
    (h1 : L.supply + (sumBy Job.owedTok jobs + sumBy Ready.owedTok ready + sumBy Wd.amount outbox +
      sumBy Rs.unsettled resolves + sumBy depW pend) + uK ≤ WNear.bal c.accts K.me)
    (h2 : L.supply = total L.bals) (h3 : ∀ e ∈ pend, PendOK K.me e ∧ PendPos e)
    (h4 : ∀ w ∈ outbox, w.amount ≤ U128_MAX) (h5 : ∀ u ∈ jobs, JobOK u)
    (h6 : ∀ r ∈ ready, r.job.fwd.wdAmount ≤ U128_MAX) (h7 : ∀ r ∈ resolves, RsOK r) :
    Inv K ⟨c, pend, paid, L, jobs, ready, outbox, resolves, uD, uB, uK, nG, nF⟩ :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem sent_sum (f : Fwd) : sumBy Wd.amount f.sent = f.wdAmount := by
  cases f <;> simp [Fwd.sent, Fwd.wdAmount, sumBy]

theorem failedRs_sum (f : Fwd) : sumBy Rs.unsettled f.failedRs = f.wdAmount := by
  cases f <;> simp [Fwd.failedRs, Fwd.wdAmount, sumBy, Rs.unsettled]

theorem sent_le {f : Fwd} (h : f.wdAmount ≤ U128_MAX) : ∀ w ∈ f.sent, w.amount ≤ U128_MAX := by
  intro w hw
  cases f with
  | ftw w' =>
    simp only [Fwd.sent, List.mem_singleton] at hw
    subst hw; exact h
  | native r => simp [Fwd.sent] at hw
  | storage c a => simp [Fwd.sent] at hw
  | auth c => simp [Fwd.sent] at hw
  | other t r => simp [Fwd.sent] at hw

theorem failedRs_ok (f : Fwd) : ∀ r ∈ f.failedRs, RsOK r := by
  intro r hr
  cases f with
  | ftw w =>
    simp only [Fwd.failedRs, List.mem_singleton] at hr
    subst hr; exact rsOK_failed_none w.owner w.amount w.msg.isSome
  | native r => simp [Fwd.failedRs] at hr
  | storage c a => simp [Fwd.failedRs] at hr
  | auth c => simp [Fwd.failedRs] at hr
  | other t r => simp [Fwd.failedRs] at hr

theorem wdAmount_of_not_wd {f : Fwd} (h : ¬ f.isWd = true) : f.wdAmount = 0 := by
  cases f with
  | ftw w => exact absurd rfl h
  | native r => rfl
  | storage c a => rfl
  | auth c => rfl
  | other t r => rfl

/-- The arithmetic of the debit that starts a withdrawal of wNEAR: the amount and the storage
    deposit (0 when there is none) leave the owner's balance and the total, nothing else moves. -/
theorem startWithdrawW_spec {L L' : Ledger} {via : Via} {w : Wd}
    (h : startWithdrawW L via w = some L') :
    w.amount ≤ U128_MAX ∧ 0 < w.amount ∧ (∀ d, w.sd = some d → 0 < d) ∧
    L'.supply + (w.amount + w.sd.getD 0) = L.supply ∧
    bal L'.bals w.owner + (w.amount + w.sd.getD 0) = bal L.bals w.owner ∧
    (∀ a, a ≠ w.owner → bal L'.bals a = bal L.bals a) ∧
    total L'.bals + (w.amount + w.sd.getD 0) = total L.bals ∧ L'.ctl = L.ctl := by
  obtain ⟨L1, hs, hcase⟩ := startWithdrawW_some h
  obtain ⟨_, hmax, hd⟩ := startWithdraw_some hs
  obtain ⟨hpos, _, hle, hles, rfl⟩ := debit_some hd
  have ht1 := total_debit L.bals w.owner w.amount hle
  rcases hcase with ⟨hsd, rfl⟩ | ⟨d, hsd, _, hd2⟩
  · refine ⟨hmax, hpos, fun d hd' => ?_, ?_, ?_, fun a ha => ?_, ?_, rfl⟩
    · rw [hsd] at hd'; exact absurd hd' (by simp)
    · rw [hsd]; simp only [Option.getD_none]; omega
    · rw [hsd]; simp only [Option.getD_none]; rw [bal_set_self]; omega
    · simp only; rw [bal_set_ne _ _ (Ne.symm ha)]
    · rw [hsd]; simp only [Option.getD_none]; omega
  · obtain ⟨hpos2, _, hle2, hles2, rfl⟩ := debit_some hd2
    simp only at hle2 hles2
    have ht2 := total_debit (set L.bals w.owner (bal L.bals w.owner - w.amount)) w.owner d hle2
    rw [bal_set_self] at hle2 ht2
    refine ⟨hmax, hpos, fun d' hd' => ?_, ?_, ?_, fun a ha => ?_, ?_, rfl⟩
    · rw [hsd] at hd'; obtain rfl := Option.some.inj hd'; exact hpos2
    · rw [hsd]; simp only [Option.getD_some]; omega
    · rw [hsd]; simp only [Option.getD_some]; rw [bal_set_self, bal_set_self]; omega
    · simp only; rw [bal_set_ne _ _ (Ne.symm ha), bal_set_ne _ _ (Ne.symm ha)]
    · rw [hsd]; simp only [Option.getD_some]; rw [bal_set_self]; omega

/-- **Every step keeps the invariant.** -/
theorem inv_step (K : Cfg) {S : World} (hI : Inv K S) (st : Step) : Inv K (step K S st) := by
  obtain ⟨hb, hc, hp, ho, hj, hrd, hr⟩ := hI
  have hI : Inv K S := ⟨hb, hc, hp, ho, hj, hrd, hr⟩
  unfold owed at hb
  cases st with
  | tokCall p d m rs =>
    simp only [step]
    by_cases hpm : p = K.me ∨ p = K.tok.self
    · rw [ifP hpm]; exact hI
    · rw [ifN hpm]
      have hp1 : p ≠ K.me := fun h => hpm (Or.inl h)
      have hp2 : p ≠ K.tok.self := fun h => hpm (Or.inr h)
      cases he : WNear.exec K.tok S.c ⟨p, d, m, rs⟩ with
      | none => exact hI
      | some o =>
        obtain ⟨hle, hcalls⟩ := third_call (u := K.me) hp1 hp2 he
        rcases hcalls with h0 | ⟨rc, x, h1, hne, hx, hbal⟩
        · refine Inv.mk' ?_ hc ?_ ho hj hrd hr
          · rw [h0]; simp only [annThird, List.map_nil, List.append_nil]; omega
          · rw [h0]; simpa [annThird] using hp
        · refine Inv.mk' ?_ hc ?_ ho hj hrd hr
          · rw [h1]
            simp only [annThird, List.map_cons, List.map_nil, sumBy_append, sumBy_one]
            by_cases hrc : rc = K.me
            · subst hrc
              simp only [depW, ifP]
              omega
            · simp only [depW, ifN hrc]; omega
          · rw [h1]
            refine mem_snoc hp ?_
            by_cases hrc : rc = K.me
            · simp [PendOK, PendPos, hrc, hx]
            · simp [PendOK, PendPos, hrc, hp1]
  | tokResolve i res =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact hI
    | some e =>
      dsimp only
      have hpe := (hp e (List.mem_of_getElem? hpi)).1
      have hsum := sumBy_eraseIdx depW hpi
      have hp' := mem_erase hp i
      unfold PendOK at hpe
      cases hann : e.ann with
      | other =>
        rw [hann] at hpe
        simp only [resOfW_other res hann, wdDone_other _ _ hann, List.append_nil]
        have hw := depW_other hann
        cases he : WNear.exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [res]⟩ with
        | none => exact Inv.mk' (by omega) hc hp' ho hj hrd hr
        | some o =>
          obtain ⟨hcalls, hlow⟩ := resolve_exec he
          have := (hlow K.me).1 (Ne.symm hpe.2)
          refine Inv.mk' ?_ hc ?_ ho hj hrd hr
          · rw [hcalls]; simp only [annThird, List.map_nil, List.append_nil]; omega
          · rw [hcalls]; simpa [annThird] using hp'
      | dep s =>
        rw [hann] at hpe
        cases s with
        | none =>
          simp only [resOfW_dep_none res hann]
          exact hI
        | some b =>
          simp only [resOfW_dep_some res hann, wdDone_dep _ _ hann, List.append_nil]
          cases he : WNear.exec K.tok S.c
              ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [depResW b]⟩ with
          | none => exact Inv.mk' (by omega) hc hp' ho hj hrd hr
          | some o =>
            cases b with
            | true =>
              obtain ⟨hacc, hcalls⟩ := resolve_credited he
              refine Inv.mk' ?_ hc ?_ ho hj hrd hr
              · rw [hcalls, hacc]; simp only [annThird, List.map_nil, List.append_nil]; omega
              · rw [hcalls]; simpa [annThird] using hp'
            | false =>
              obtain ⟨hcalls, hlow⟩ := resolve_exec he
              have := (hlow K.me).2
              have hw := depW_failed hann
              refine Inv.mk' ?_ hc ?_ ho hj hrd hr
              · rw [hcalls]; simp only [annThird, List.map_nil, List.append_nil]; omega
              · rw [hcalls]; simpa [annThird] using hp'
      | wd owner =>
        rw [hann] at hpe
        obtain ⟨hsn, hrc, hmax⟩ := hpe
        have hw := depW_wd hann
        simp only [resOfW_wd res hann]
        cases he : WNear.exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [res]⟩ with
        | none =>
          simp only [wdDone_wd _ _ hann]
          refine Inv.mk' ?_ hc hp' ho hj hrd (mem_snoc hr (rsOK_call_failed_all owner e.amount))
          simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
        | some o =>
          have hne : e.sender ≠ e.receiver := by rw [hsn]; exact Ne.symm hrc
          obtain ⟨hcalls, f, hf, hcase⟩ := resolve_sender hne he
          rw [hsn] at hcase
          simp only [wdDone_wd _ _ hann]
          rcases hcase with ⟨hbal, hret⟩ | ⟨hbal, hret⟩
          · have hleft : e.amount - (WNear.bal o.st.accts K.me - WNear.bal S.c.accts K.me) =
                e.amount - f := by omega
            have hrf := refund_call_num owner e.amount (e.amount - f) (e.amount - f)
              (Nat.sub_le _ _) hmax
            refine Inv.mk' ?_ hc ?_ ho hj hrd (mem_snoc hr ?_)
            · rw [hcalls, hleft]
              simp only [annThird, List.map_nil, List.append_nil, sumBy_append, sumBy_one,
                Rs.unsettled]
              omega
            · rw [hcalls]; simpa [annThird] using hp'
            · rw [hleft, hret]
              exact ⟨Nat.sub_le _ _, Or.inl (by simp only [retPRW]; rw [hrf]; omega)⟩
          · have hleft : e.amount - (WNear.bal o.st.accts K.me - WNear.bal S.c.accts K.me) =
                e.amount := by omega
            have hrf := refund_call_num owner e.amount e.amount e.amount (Nat.le_refl _) hmax
            refine Inv.mk' ?_ hc ?_ ho hj hrd (mem_snoc hr ?_)
            · rw [hcalls, hleft]
              simp only [annThird, List.map_nil, List.append_nil, sumBy_append, sumBy_one,
                Rs.unsettled]
              omega
            · rw [hcalls]; simpa [annThird] using hp'
            · rw [hleft, hret]
              exact ⟨Nat.le_refl _, Or.inl (by simp only [retPRW]; rw [hrf]; omega)⟩
  | tokResolveFails i =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact hI
    | some e =>
      dsimp only
      have hsum := sumBy_eraseIdx depW hpi
      have hp' := mem_erase hp i
      cases hann : e.ann with
      | other =>
        simp only [resOfW_other _ hann, wdDone_other _ _ hann, List.append_nil]
        exact Inv.mk' (by omega) hc hp' ho hj hrd hr
      | dep s =>
        cases s with
        | none => simp only [resOfW_dep_none _ hann]; exact hI
        | some b =>
          simp only [resOfW_dep_some _ hann, wdDone_dep _ _ hann, List.append_nil]
          exact Inv.mk' (by omega) hc hp' ho hj hrd hr
      | wd owner =>
        simp only [resOfW_wd _ hann, wdDone_wd _ _ hann]
        refine Inv.mk' ?_ hc hp' ho hj hrd (mem_snoc hr (rsOK_call_failed_all owner e.amount))
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | tokNearIn x =>
    simp only [step]
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx]; exact Inv.mk' hb hc hp ho hj hrd hr
    · rw [ifN hx]; exact hI
  | onTransfer i recv ok =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact hI
    | some e =>
      dsimp only
      by_cases hg : e.receiver = K.me ∧ e.ann = .dep none
      · rw [ifP hg]
        have hw := depW_fresh hg.2
        have hpos : 0 < e.amount :=
          (hp e (List.mem_of_getElem? hpi)).2 (by rw [hg.2]; simp)
        have hpset : ∀ (b : Bool), ∀ x ∈ S.pend.set i { e with ann := .dep (some b) },
            PendOK K.me x ∧ PendPos x := by
          intro b x hx
          rcases List.mem_or_eq_of_mem_set hx with h | h
          · exact hp x h
          · subst h; exact ⟨hg.1, fun _ => hpos⟩
        cases hcr : (if ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false then
            credit S.L recv e.amount else none) with
        | none =>
          have hsum := sumBy_set depW hpi { e with ann := .dep (some false) }
          have hw' : depW { e with ann := .dep (some false) } = e.amount := rfl
          exact Inv.mk' (by omega) hc (hpset false) ho hj hrd hr
        | some L' =>
          have hcr' : credit S.L recv e.amount = some L' := by
            by_cases hcond : ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false
            · rw [ifP hcond] at hcr; exact hcr
            · rw [ifN hcond] at hcr; exact absurd hcr (by simp)
          obtain ⟨_, _, _, rfl⟩ := credit_some hcr'
          have hsum := sumBy_set depW hpi { e with ann := .dep (some true) }
          have hw' : depW { e with ann := .dep (some true) } = 0 := rfl
          refine Inv.mk' (by simp only; omega) ?_ (hpset true) ho hj hrd hr
          simp only; rw [total_credit]; omega
      · rw [ifN hg]; exact hI
  | ftWithdraw via w =>
    simp only [step]
    cases hs : startWithdrawW S.L via w with
    | none => exact hI
    | some L' =>
      dsimp only
      obtain ⟨hmax, hpos, hsdpos, hsup, _, _, htot, _⟩ := startWithdrawW_spec hs
      cases hsd : w.sd with
      | some d =>
        rw [hsd] at hsup htot
        simp only [Option.getD_some] at hsup htot
        have e1 : Job.owedTok ⟨w.owner, d, .ftw w⟩ = d + w.amount := rfl
        refine Inv.mk' ?_ (by omega) hp ho (mem_snoc hj ⟨hsdpos d hsd, hmax⟩) hrd hr
        simp only [sumBy_append, sumBy_one]; omega
      | none =>
        rw [hsd] at hsup htot
        simp only [Option.getD_none] at hsup htot
        refine Inv.mk' ?_ (by omega) hp (mem_snoc ho hmax) hj hrd hr
        simp only [sumBy_append, sumBy_one]; omega
  | unwrap owner x f =>
    simp only [step]
    by_cases hf : f.isWd = true
    · rw [ifP hf]; exact hI
    · rw [ifN hf]
      cases hs : startUnwrap S.L owner x with
      | none => exact hI
      | some L' =>
        obtain ⟨_, _, hd⟩ := startUnwrap_some hs
        obtain ⟨hpos, _, hle, hles, rfl⟩ := debit_some hd
        have hcons : S.L.supply - x = total (set S.L.bals owner (bal S.L.bals owner - x)) := by
          have := total_debit S.L.bals owner x hle; omega
        have hw0 := wdAmount_of_not_wd hf
        have e1 : Job.owedTok ⟨owner, x, f⟩ = x + f.wdAmount := rfl
        refine Inv.mk' ?_ hcons hp ho (mem_snoc hj ⟨hpos, by rw [hw0]; exact Nat.zero_le _⟩) hrd hr
        simp only [sumBy_append, sumBy_one]; omega
  | nearWithdraw j =>
    simp only [step]
    cases hjj : S.jobs[j]? with
    | none => exact hI
    | some u =>
      dsimp only
      have hsum := sumBy_eraseIdx Job.owedTok hjj
      have hok := hj u (List.mem_of_getElem? hjj)
      have e1 : Job.owedTok u = u.amount + u.fwd.wdAmount := rfl
      cases he : WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ with
      | none =>
        have e2 : Ready.owedTok ⟨u, false⟩ = u.fwd.wdAmount := rfl
        refine Inv.mk' ?_ hc hp ho (mem_erase hj j) (mem_snoc hrd hok.2) hr
        simp only [sumBy_append, sumBy_one]; omega
      | some o =>
        have e2 : Ready.owedTok ⟨u, true⟩ = u.fwd.wdAmount := rfl
        obtain ⟨hb1, _, _, hcalls, _⟩ := nw_exec he
        refine Inv.mk' ?_ hc ?_ ho (mem_erase hj j) (mem_snoc hrd hok.2) hr
        · rw [hcalls]
          simp only [annThird, List.map_nil, List.append_nil, sumBy_append, sumBy_one]
          omega
        · rw [hcalls]; simpa [annThird] using hp
  | nearWithdrawFails j =>
    simp only [step]
    cases hjj : S.jobs[j]? with
    | none => exact hI
    | some u =>
      dsimp only
      have hsum := sumBy_eraseIdx Job.owedTok hjj
      have hok := hj u (List.mem_of_getElem? hjj)
      have e1 : Job.owedTok u = u.amount + u.fwd.wdAmount := rfl
      have e2 : Ready.owedTok ⟨u, false⟩ = u.fwd.wdAmount := rfl
      refine Inv.mk' ?_ hc hp ho (mem_erase hj j) (mem_snoc hrd hok.2) hr
      simp only [sumBy_append, sumBy_one]; omega
  | doJob k ok =>
    simp only [step]
    cases hk : S.ready[k]? with
    | none => exact hI
    | some r =>
      dsimp only
      have hsum := sumBy_eraseIdx Ready.owedTok hk
      have hrk := hrd r (List.mem_of_getElem? hk)
      have e1 : Ready.owedTok r = r.job.fwd.wdAmount := rfl
      by_cases hgo : r.ok = true ∧ ok = true
      · rw [ifP hgo]
        have hs := sent_sum r.job.fwd
        refine Inv.mk' ?_ hc hp ?_ hj (mem_erase hrd k) hr
        · simp only [sumBy_append]; omega
        · intro w hw
          rcases List.mem_append.mp hw with h | h
          · exact ho w h
          · exact sent_le hrk w h
      · rw [ifN hgo]
        have hs := failedRs_sum r.job.fwd
        refine Inv.mk' ?_ hc hp ho hj (mem_erase hrd k) ?_
        · simp only [sumBy_append]; omega
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hr x h
          · exact failedRs_ok _ x h
  | tokXfer j =>
    simp only [step]
    cases hjj : S.outbox[j]? with
    | none => exact hI
    | some w =>
      dsimp only
      have hsum := sumBy_eraseIdx Wd.amount hjj
      have hmax := ho w (List.mem_of_getElem? hjj)
      cases hx : xferBatchW K.tok K.me S.c w with
      | none =>
        refine Inv.mk' ?_ hc hp (mem_erase ho j) hj hrd
          (mem_snoc hr (rsOK_failed_none w.owner w.amount w.msg.isSome))
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
      | some o =>
        obtain ⟨hne, hpos, hbal, hplain, hcall⟩ := batch_exec hx
        cases hmsg : w.msg with
        | none =>
          obtain ⟨hcalls, hret⟩ := hplain hmsg
          have hleft : WNear.bal S.c.accts K.me - WNear.bal o.st.accts K.me = w.amount := by omega
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
          rw [hcalls, hret, hleft]
          refine Inv.mk' ?_ hc ?_ (mem_erase ho j) hj hrd
            (mem_snoc hr (rsOK_plain_ok w.owner w.amount))
          · simp only [annWd, List.map_nil, List.append_nil, sumBy_append, sumBy_one, Rs.unsettled,
              retPRW]
            omega
          · simpa [annWd] using hp
        | some msg =>
          have hcalls := hcall (by rw [hmsg]; rfl)
          simp only [Option.isSome_some, ite_true, List.append_nil]
          rw [hcalls]
          refine Inv.mk' ?_ hc ?_ (mem_erase ho j) hj hrd hr
          · simp only [annWd, List.map_cons, List.map_nil, sumBy_append, sumBy_one, depW]
            omega
          · exact mem_snoc hp ⟨⟨rfl, Ne.symm hne, hmax⟩, fun _ => hpos⟩
  | tokXferFails j =>
    simp only [step]
    cases hjj : S.outbox[j]? with
    | none => exact hI
    | some w =>
      have hsum := sumBy_eraseIdx Wd.amount hjj
      refine Inv.mk' ?_ hc hp (mem_erase ho j) hj hrd
        (mem_snoc hr (rsOK_failed_none w.owner w.amount w.msg.isSome))
      simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | meStorageDeposit acc d =>
    simp only [step]
    cases he : WNear.exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc), []⟩ with
    | none => exact hI
    | some o =>
      obtain ⟨hbal, hcalls⟩ := sd_exec he
      refine Inv.mk' ?_ hc ?_ ho hj hrd hr
      · rw [hcalls, hbal]; simp only [annThird, List.map_nil, List.append_nil]; omega
      · rw [hcalls]; simpa [annThird] using hp
  | resolveWd k =>
    simp only [step]
    cases hk : S.resolves[k]? with
    | none => exact hI
    | some r =>
      dsimp only
      have hsum := sumBy_eraseIdx Rs.unsettled hk
      have hok := hr r (List.mem_of_getElem? hk)
      have hrs' := mem_erase hr k
      cases hres : resolveWithdraw S.L r with
      | none => exact Inv.mk' (by omega) hc hp ho hj hrd hrs'
      | some L' =>
        unfold resolveWithdraw at hres
        by_cases h0 : r.refund = 0
        · rw [ifP h0] at hres
          obtain rfl := Option.some.inj hres
          exact Inv.mk' (by omega) hc hp ho hj hrd hrs'
        · rw [ifN h0] at hres
          obtain ⟨_, _, _, rfl⟩ := credit_some hres
          have hle : r.refund ≤ r.unsettled := by
            unfold RsOK at hok; unfold Rs.unsettled
            rcases hok.2 with h | h
            · omega
            · omega
          refine Inv.mk' (by simp only; omega) ?_ hp ho hj hrd hrs'
          simp only; rw [total_credit]; omega
  | resolveWdFails k =>
    simp only [step]
    by_cases hk : ∃ r, S.resolves[k]? = some r
    · obtain ⟨r, hk⟩ := hk
      have hsum := sumBy_eraseIdx Rs.unsettled hk
      exact Inv.mk' (by omega) hc hp ho hj hrd (mem_erase hr k)
    · have hnone : S.resolves[k]? = none := by
        cases h : S.resolves[k]? with
        | none => rfl
        | some r => exact absurd ⟨r, h⟩ hk
      have hlen : S.resolves.length ≤ k := by
        rcases Nat.lt_or_ge k S.resolves.length with h | h
        · rw [List.getElem?_eq_getElem h] at hnone; exact absurd hnone (by simp)
        · exact h
      rw [List.eraseIdx_of_length_le hlen]
      exact hI
  | move auth src dst amt =>
    simp only [step]
    cases hm : moveBal S.L auth src dst amt with
    | none => exact hI
    | some L' =>
      obtain ⟨hne, _, _, hle, _, rfl⟩ := moveBal_some hm
      refine Inv.mk' hb ?_ hp ho hj hrd hr
      simp only; rw [total_move _ _ _ _ hne hle]; exact hc
  | admin a =>
    simp only [step]
    exact Inv.mk' hb hc hp ho hj hrd hr

theorem inv_init {K : Cfg} {S : World} (h : Init K S) : Inv K S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd : sumBy depW S.pend = 0 :=
      sumBy_eq_zero depW (fun e he => depW_other (h.pend e he).1)
    unfold owed; rw [h.supply, h.jobs, h.ready, h.outbox, h.resolves, h.uKept, hd]; simp [sumBy]
  · rw [h.supply, h.bals]; rfl
  · intro e he
    obtain ⟨h1, h2, h3⟩ := h.pend e he
    refine ⟨?_, fun hne => absurd h1 hne⟩
    unfold PendOK; rw [h1]; exact ⟨h2, h3⟩
  · rw [h.outbox]; simp
  · rw [h.jobs]; simp
  · rw [h.ready]; simp
  · rw [h.resolves]; simp

theorem inv_reach {K : Cfg} {S : World} (h : Reach K S) : Inv K S := by
  induction h with
  | init S h => exact inv_init h
  | step st _ ih => exact inv_step K ih st

/-! ## The unwrap bookkeeping -/

/-- The books of the unwrap paths.
    * `burn`: every wNEAR debited from a ledger balance for unwrapping is burned, or kept
      because its `near_withdraw` receipt failed, or its `near_withdraw` is still in flight;
    * `near`: the NEAR the callbacks sent on, plus what the ready callbacks may still send, is
      at most the wNEAR burned;
    * `got`: the wNEAR burned is at most the NEAR wNEAR sent to the contract for it. -/
structure Books (S : World) : Prop where
  burn : S.uDebited = S.uBurned + S.uKept + sumBy Job.amount S.jobs
  near : S.nFwd + sumBy Ready.live S.ready ≤ S.uBurned
  got : S.uBurned ≤ S.nGot

theorem Books.mk' {c : WNear.St} {pend : List Pend} {paid : List (Acct × Nat)}
    {L : Ledger} {jobs : List Job} {ready : List Ready} {outbox : List Wd} {resolves : List Rs}
    {uD uB uK nG nF : Nat}
    (h1 : uD = uB + uK + sumBy Job.amount jobs) (h2 : nF + sumBy Ready.live ready ≤ uB)
    (h3 : uB ≤ nG) :
    Books ⟨c, pend, paid, L, jobs, ready, outbox, resolves, uD, uB, uK, nG, nF⟩ :=
  ⟨h1, h2, h3⟩

/-- **Every step keeps the books.** -/
theorem books_step (K : Cfg) {S : World} (hB : Books S) (st : Step) : Books (step K S st) := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hB : Books S := ⟨h1, h2, h3⟩
  cases st with
  | tokCall p d m rs =>
    simp only [step]
    split
    · exact hB
    · split
      · exact hB
      · exact Books.mk' h1 h2 h3
  | tokResolve i res =>
    simp only [step]
    split
    · exact hB
    · split
      · exact hB
      · split <;> exact Books.mk' h1 h2 h3
  | tokResolveFails i =>
    simp only [step]
    split
    · exact hB
    · split
      · exact hB
      · exact Books.mk' h1 h2 h3
  | tokNearIn x =>
    simp only [step]
    split
    · exact Books.mk' h1 h2 h3
    · exact hB
  | onTransfer i recv ok =>
    simp only [step]
    split
    · exact hB
    · split
      · split <;> exact Books.mk' h1 h2 h3
      · exact hB
  | ftWithdraw via w =>
    simp only [step]
    cases hs : startWithdrawW S.L via w with
    | none => exact hB
    | some L' =>
      dsimp only
      cases hsd : w.sd with
      | some d =>
        have e1 : Job.amount ⟨w.owner, d, .ftw w⟩ = d := rfl
        refine Books.mk' ?_ h2 h3
        simp only [sumBy_append, sumBy_one]; omega
      | none => exact Books.mk' h1 h2 h3
  | unwrap owner x f =>
    simp only [step]
    by_cases hf : f.isWd = true
    · rw [ifP hf]; exact hB
    · rw [ifN hf]
      cases hs : startUnwrap S.L owner x with
      | none => exact hB
      | some L' =>
        have e1 : Job.amount ⟨owner, x, f⟩ = x := rfl
        refine Books.mk' ?_ h2 h3
        simp only [sumBy_append, sumBy_one]; omega
  | nearWithdraw j =>
    simp only [step]
    cases hjj : S.jobs[j]? with
    | none => exact hB
    | some u =>
      dsimp only
      have hsum := sumBy_eraseIdx Job.amount hjj
      cases he : WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ with
      | none =>
        have e2 : Ready.live ⟨u, false⟩ = 0 := rfl
        refine Books.mk' ?_ ?_ h3
        · omega
        · simp only [sumBy_append, sumBy_one]; omega
      | some o =>
        have e2 : Ready.live ⟨u, true⟩ = u.amount := rfl
        obtain ⟨hb1, _, _, _, htr, _⟩ := nw_exec he
        have hleft : WNear.bal S.c.accts K.me - WNear.bal o.st.accts K.me = u.amount := by omega
        dsimp only
        rw [hleft, htr, WNear.sumT_one]
        refine Books.mk' ?_ ?_ ?_
        · omega
        · simp only [sumBy_append, sumBy_one]; omega
        · omega
  | nearWithdrawFails j =>
    simp only [step]
    cases hjj : S.jobs[j]? with
    | none => exact hB
    | some u =>
      dsimp only
      have hsum := sumBy_eraseIdx Job.amount hjj
      have e2 : Ready.live ⟨u, false⟩ = 0 := rfl
      refine Books.mk' ?_ ?_ h3
      · omega
      · simp only [sumBy_append, sumBy_one]; omega
  | doJob k ok =>
    simp only [step]
    cases hk : S.ready[k]? with
    | none => exact hB
    | some r =>
      dsimp only
      have hsum := sumBy_eraseIdx Ready.live hk
      by_cases hgo : r.ok = true ∧ ok = true
      · rw [ifP hgo]
        have e2 : Ready.live r = r.job.amount := by simp [Ready.live, hgo.1]
        exact Books.mk' h1 (by omega) h3
      · rw [ifN hgo]
        exact Books.mk' h1 (by omega) h3
  | tokXfer j =>
    simp only [step]
    split
    · exact hB
    · split <;> exact Books.mk' h1 h2 h3
  | tokXferFails j =>
    simp only [step]
    split
    · exact hB
    · exact Books.mk' h1 h2 h3
  | meStorageDeposit acc d =>
    simp only [step]
    split
    · exact hB
    · exact Books.mk' h1 h2 h3
  | resolveWd k =>
    simp only [step]
    split
    · exact hB
    · split <;> exact Books.mk' h1 h2 h3
  | resolveWdFails k => exact Books.mk' h1 h2 h3
  | move auth src dst amt =>
    simp only [step]
    split
    · exact hB
    · exact Books.mk' h1 h2 h3
  | admin a => exact Books.mk' h1 h2 h3

theorem books_init {K : Cfg} {S : World} (h : Init K S) : Books S := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.uDebited, h.uBurned, h.uKept, h.jobs]; rfl
  · rw [h.nFwd, h.uBurned, h.ready]; exact Nat.le_refl _
  · rw [h.uBurned]; exact Nat.zero_le _

theorem books_reach {K : Cfg} {S : World} (h : Reach K S) : Books S := by
  induction h with
  | init S h => exact books_init h
  | step st _ ih => exact books_step K ih st

end IntentsW
