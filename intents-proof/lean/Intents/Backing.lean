/-
  T1 Backing: in every reachable state of the two-contract world the ledger never holds more
  than the contract's token balance, counting what is in flight.

  `Inv` is the inductive invariant; `inv_step` shows every step keeps it (any call by anyone,
  any callback with any outcome, any callback dropped); the statements for readers are in
  `Intents/Theorems.lean`.
-/
import Intents.TokenFacts

namespace Intents
open ProvedFT

/-- Shape of a callback in flight on the token, by its annotation. -/
def PendOK (me : Acct) (e : Pend) : Prop :=
  match e.ann with
  | .other => e.sender ≠ me ∧ e.receiver ≠ me
  | .dep _ => e.receiver = me
  | .wd _ => e.sender = me ∧ e.receiver ≠ me ∧ e.amount ≤ U128_MAX

/-- A ready `ft_resolve_withdraw` and the tokens that actually left: the callback will keep
    debited exactly what left (`amount = left + refund`), with one exception — the
    `ft_transfer_call` receipt itself failed, so nothing left, and nothing is refunded. -/
def RsOK (r : Rs) : Prop :=
  r.left ≤ r.amount ∧
  (r.amount = r.left + r.refund ∨
    (r.isCall = true ∧ r.res = PR.failed ∧ r.left = 0 ∧ r.refund = 0))

/-- The invariant of every reachable state. -/
structure Inv (K : Cfg) (S : World) : Prop where
  /-- Ledger total plus everything owed in flight is covered by the tokens held. -/
  backed : S.L.supply + owed S ≤ bal S.c.accts K.me
  /-- `total_supplies[nep141:T]` is the sum of the ledger balances. -/
  cons : S.L.supply = total S.L.bals
  pend : ∀ e ∈ S.pend, PendOK K.me e
  outbox : ∀ w ∈ S.outbox, w.amount ≤ U128_MAX
  unwrap : ∀ w ∈ S.unwrap, w.amount ≤ U128_MAX
  rs : ∀ r ∈ S.resolves, RsOK r

theorem Inv.mk' {K : Cfg} {c : St} {pend : List Pend} {paid : List (Acct × Nat)} {L : Ledger}
    {unwrap outbox : List Wd} {resolves : List Rs}
    (h1 : L.supply + (sumBy Wd.amount unwrap + sumBy Wd.amount outbox +
      sumBy Rs.unsettled resolves + sumBy depW pend) ≤ bal c.accts K.me)
    (h2 : L.supply = total L.bals) (h3 : ∀ e ∈ pend, PendOK K.me e)
    (h4 : ∀ w ∈ outbox, w.amount ≤ U128_MAX) (h5 : ∀ w ∈ unwrap, w.amount ≤ U128_MAX)
    (h6 : ∀ r ∈ resolves, RsOK r) : Inv K ⟨c, pend, paid, L, unwrap, outbox, resolves⟩ :=
  ⟨h1, h2, h3, h4, h5, h6⟩

theorem mem_snoc {α : Type} {P : α → Prop} {l : List α} {a : α} (hl : ∀ x ∈ l, P x) (ha : P a) :
    ∀ x ∈ l ++ [a], P x := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hl x h
  · simp only [List.mem_singleton] at h; subst h; exact ha

theorem mem_erase {α : Type} {P : α → Prop} {l : List α} (hl : ∀ x ∈ l, P x) (i : Nat) :
    ∀ x ∈ l.eraseIdx i, P x := fun x hx => hl x (List.mem_of_mem_eraseIdx hx)

theorem rsOK_call_failed_none (o : Acct) (a : Nat) : RsOK ⟨o, a, true, .failed, 0⟩ :=
  ⟨Nat.zero_le _, Or.inr ⟨rfl, rfl, rfl, refund_call_failed o a 0⟩⟩

theorem rsOK_call_failed_all (o : Acct) (a : Nat) : RsOK ⟨o, a, true, .failed, a⟩ :=
  ⟨Nat.le_refl _, Or.inl (by simp [refund_call_failed])⟩

theorem rsOK_plain_failed (o : Acct) (a : Nat) : RsOK ⟨o, a, false, .failed, 0⟩ :=
  ⟨Nat.zero_le _, Or.inl (by simp [refund_plain_failed])⟩

theorem rsOK_plain_ok (o : Acct) (a : Nat) : RsOK ⟨o, a, false, .ok [], a⟩ :=
  ⟨Nat.le_refl _, Or.inl (by simp [refund_plain_ok])⟩

theorem rsOK_failed_none (o : Acct) (a : Nat) (b : Bool) : RsOK ⟨o, a, b, .failed, 0⟩ := by
  cases b
  · exact rsOK_plain_failed o a
  · exact rsOK_call_failed_none o a

theorem total_credit (l : Accts) (a : Acct) (x : Nat) :
    total (set l a (bal l a + x)) = total l + x := by
  have := total_set l a (bal l a + x); omega

theorem total_debit (l : Accts) (a : Acct) (x : Nat) (h : x ≤ bal l a) :
    total (set l a (bal l a - x)) + x = total l := by
  have := total_set l a (bal l a - x); omega

theorem total_move (l : Accts) (s d : Acct) (x : Nat) (hne : s ≠ d) (h : x ≤ bal l s) :
    total (set (set l s (bal l s - x)) d (bal l d + x)) = total l := by
  have h1 := total_set l s (bal l s - x)
  have h2 := total_set (set l s (bal l s - x)) d (bal l d + x)
  rw [bal_set_ne _ _ hne] at h2
  omega

/-- **Every step keeps the invariant.** -/
theorem inv_step (K : Cfg) {S : World} (hI : Inv K S) (st : Step) : Inv K (stdStep K S st) := by
  obtain ⟨hb, hc, hp, ho, hu, hr⟩ := hI
  have hI : Inv K S := ⟨hb, hc, hp, ho, hu, hr⟩
  unfold owed at hb
  cases st with
  | tokCall p d m rs =>
    simp only [stdStep, step]
    by_cases hpm : p = K.me
    · rw [ifP hpm]; exact hI
    · rw [ifN hpm]
      cases he : exec K.tok S.c ⟨p, d, m, resultsFor K.tok p rs⟩ with
      | none => exact hI
      | some o =>
        obtain ⟨hle, hcalls⟩ := third_call (u := K.me) hpm he
        rcases hcalls with h0 | ⟨rc, x, h1, hne, hx, hbal⟩
        · refine Inv.mk' ?_ hc ?_ ho hu hr
          · rw [h0]; simp only [annThird, List.map_nil, List.append_nil]; omega
          · rw [h0]; simpa [annThird] using hp
        · refine Inv.mk' ?_ hc ?_ ho hu hr
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
            · simp [PendOK, hrc]
            · simp [PendOK, hrc, hpm]
  | tokResolve i res =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact hI
    | some e =>
      dsimp only
      have hpe := hp e (List.mem_of_getElem? hpi)
      have hsum := sumBy_eraseIdx depW hpi
      have hp' := mem_erase hp i
      unfold PendOK at hpe
      cases hann : e.ann with
      | other =>
        rw [hann] at hpe
        simp only [resOf_other res hann, wdDone_other _ _ hann, List.append_nil]
        have hw := depW_other hann
        cases he : exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [res]⟩ with
        | none => exact Inv.mk' (by omega) hc hp' ho hu hr
        | some o =>
          obtain ⟨hcalls, hlow⟩ := resolve_exec he
          have := (hlow K.me).1 (Ne.symm hpe.2)
          refine Inv.mk' ?_ hc ?_ ho hu hr
          · rw [hcalls]; simp only [annThird, List.map_nil, List.append_nil]; omega
          · rw [hcalls]; simpa [annThird] using hp'
      | dep s =>
        rw [hann] at hpe
        cases s with
        | none =>
          simp only [resOf_dep_none res hann]
          exact hI
        | some b =>
          simp only [resOf_dep_some res hann, wdDone_dep _ _ hann, List.append_nil]
          cases he : exec K.tok S.c
              ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [depRes b]⟩ with
          | none => exact Inv.mk' (by omega) hc hp' ho hu hr
          | some o =>
            cases b with
            | true =>
              obtain ⟨hacc, hcalls⟩ := resolve_credited he
              refine Inv.mk' ?_ hc ?_ ho hu hr
              · rw [hcalls, hacc]; simp only [annThird, List.map_nil, List.append_nil]; omega
              · rw [hcalls]; simpa [annThird] using hp'
            | false =>
              obtain ⟨hcalls, hlow⟩ := resolve_exec he
              have := (hlow K.me).2
              have hw := depW_failed hann
              refine Inv.mk' ?_ hc ?_ ho hu hr
              · rw [hcalls]; simp only [annThird, List.map_nil, List.append_nil]; omega
              · rw [hcalls]; simpa [annThird] using hp'
      | wd owner =>
        rw [hann] at hpe
        obtain ⟨hsn, hrc, hmax⟩ := hpe
        have hw := depW_wd hann
        simp only [resOf_wd res hann]
        cases he : exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [res]⟩ with
        | none =>
          simp only [wdDone_wd _ _ hann]
          refine Inv.mk' ?_ hc hp' ho hu (mem_snoc hr (rsOK_call_failed_all owner e.amount))
          simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
        | some o =>
          have hne : e.sender ≠ e.receiver := by rw [hsn]; exact Ne.symm hrc
          obtain ⟨hcalls, f, hf, hcase⟩ := resolve_sender hne he
          rw [hsn] at hcase
          simp only [wdDone_wd _ _ hann]
          rcases hcase with ⟨hbal, hret⟩ | ⟨hbal, hret⟩
          · have hleft : e.amount - (bal o.st.accts K.me - bal S.c.accts K.me) = e.amount - f := by
              omega
            have hrf := refund_call_num owner e.amount (e.amount - f) (e.amount - f)
              (Nat.sub_le _ _) hmax
            refine Inv.mk' ?_ hc ?_ ho hu (mem_snoc hr ?_)
            · rw [hcalls, hleft]
              simp only [annThird, List.map_nil, List.append_nil, sumBy_append, sumBy_one,
                Rs.unsettled]
              omega
            · rw [hcalls]; simpa [annThird] using hp'
            · rw [hleft, hret]
              exact ⟨Nat.sub_le _ _, Or.inl (by simp only [retPR]; rw [hrf]; omega)⟩
          · have hleft : e.amount - (bal o.st.accts K.me - bal S.c.accts K.me) = e.amount := by
              omega
            have hrf := refund_call_num owner e.amount e.amount e.amount (Nat.le_refl _) hmax
            refine Inv.mk' ?_ hc ?_ ho hu (mem_snoc hr ?_)
            · rw [hcalls, hleft]
              simp only [annThird, List.map_nil, List.append_nil, sumBy_append, sumBy_one,
                Rs.unsettled]
              omega
            · rw [hcalls]; simpa [annThird] using hp'
            · rw [hleft, hret]
              exact ⟨Nat.le_refl _, Or.inl (by simp only [retPR]; rw [hrf]; omega)⟩
  | tokResolveFails i =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact hI
    | some e =>
      dsimp only
      have hsum := sumBy_eraseIdx depW hpi
      have hp' := mem_erase hp i
      cases hann : e.ann with
      | other =>
        simp only [resOf_other _ hann, wdDone_other _ _ hann, List.append_nil]
        exact Inv.mk' (by omega) hc hp' ho hu hr
      | dep s =>
        cases s with
        | none => simp only [resOf_dep_none _ hann]; exact hI
        | some b =>
          simp only [resOf_dep_some _ hann, wdDone_dep _ _ hann, List.append_nil]
          exact Inv.mk' (by omega) hc hp' ho hu hr
      | wd owner =>
        simp only [resOf_wd _ hann, wdDone_wd _ _ hann]
        refine Inv.mk' ?_ hc hp' ho hu (mem_snoc hr (rsOK_call_failed_all owner e.amount))
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | tokNearIn x =>
    simp only [stdStep, step]
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx]; exact Inv.mk' hb hc hp ho hu hr
    · rw [ifN hx]; exact hI
  | onTransfer i recv ok =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact hI
    | some e =>
      dsimp only
      by_cases hg : e.receiver = K.me ∧ e.ann = .dep none
      · rw [ifP hg]
        have hw := depW_fresh hg.2
        have hpset : ∀ (b : Bool), ∀ x ∈ S.pend.set i { e with ann := .dep (some b) },
            PendOK K.me x := by
          intro b x hx
          rcases List.mem_or_eq_of_mem_set hx with h | h
          · exact hp x h
          · subst h; exact hg.1
        cases hcr : (if ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false then
            credit S.L recv e.amount else none) with
        | none =>
          have hsum := sumBy_set depW hpi { e with ann := .dep (some false) }
          have hw' : depW { e with ann := .dep (some false) } = e.amount := rfl
          exact Inv.mk' (by omega) hc (hpset false) ho hu hr
        | some L' =>
          have hcr' : credit S.L recv e.amount = some L' := by
            by_cases hcond : ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false
            · rw [ifP hcond] at hcr; exact hcr
            · rw [ifN hcond] at hcr; exact absurd hcr (by simp)
          obtain ⟨_, _, _, rfl⟩ := credit_some hcr'
          have hsum := sumBy_set depW hpi { e with ann := .dep (some true) }
          have hw' : depW { e with ann := .dep (some true) } = 0 := rfl
          refine Inv.mk' (by simp only; omega) ?_ (hpset true) ho hu hr
          simp only; rw [total_credit]; omega
      · rw [ifN hg]; exact hI
  | ftWithdraw via w =>
    simp only [stdStep, step]
    cases hs : startWithdraw S.L via w with
    | none => exact hI
    | some L' =>
      obtain ⟨_, hmax, hd⟩ := startWithdraw_some hs
      obtain ⟨_, _, hle, hles, rfl⟩ := debit_some hd
      have hcons : S.L.supply - w.amount = total (set S.L.bals w.owner (bal S.L.bals w.owner - w.amount)) := by
        have := total_debit S.L.bals w.owner w.amount hle; omega
      by_cases hsd : w.sd.isSome = true
      · simp only [hsd, ite_true]
        refine Inv.mk' ?_ hcons hp ho (mem_snoc hu hmax) hr
        simp only [sumBy_append, sumBy_one]; omega
      · simp only [hsd]
        refine Inv.mk' ?_ hcons hp (mem_snoc ho hmax) hu hr
        simp only [sumBy_append, sumBy_one]; omega
  | doFtWithdraw j ok =>
    simp only [stdStep, step]
    cases hj : S.unwrap[j]? with
    | none => exact hI
    | some w =>
      dsimp only
      have hsum := sumBy_eraseIdx Wd.amount hj
      have hmax := hu w (List.mem_of_getElem? hj)
      cases ok with
      | true =>
        simp only [ite_true]
        refine Inv.mk' ?_ hc hp (mem_snoc ho hmax) (mem_erase hu j) hr
        simp only [sumBy_append, sumBy_one]; omega
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        refine Inv.mk' ?_ hc hp ho (mem_erase hu j)
          (mem_snoc hr (rsOK_failed_none w.owner w.amount w.msg.isSome))
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | tokXfer j =>
    simp only [stdStep, step]
    cases hj : S.outbox[j]? with
    | none => exact hI
    | some w =>
      dsimp only
      have hsum := sumBy_eraseIdx Wd.amount hj
      have hmax := ho w (List.mem_of_getElem? hj)
      cases hx : xferBatch (exec K.tok) K.me S.c w with
      | none =>
        refine Inv.mk' ?_ hc hp (mem_erase ho j) hu
          (mem_snoc hr (rsOK_failed_none w.owner w.amount w.msg.isSome))
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
      | some o =>
        obtain ⟨hne, hbal, hplain, hcall⟩ := batch_exec hx
        cases hmsg : w.msg with
        | none =>
          obtain ⟨hcalls, hret⟩ := hplain hmsg
          have hleft : bal S.c.accts K.me - bal o.st.accts K.me = w.amount := by omega
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
          rw [hcalls, hret, hleft]
          refine Inv.mk' ?_ hc ?_ (mem_erase ho j) hu (mem_snoc hr (rsOK_plain_ok w.owner w.amount))
          · simp only [annWd, List.map_nil, List.append_nil, sumBy_append, sumBy_one, Rs.unsettled,
              retPR]
            omega
          · simpa [annWd] using hp
        | some msg =>
          have hcalls := hcall (by rw [hmsg]; rfl)
          simp only [Option.isSome_some, ite_true, List.append_nil]
          rw [hcalls]
          refine Inv.mk' ?_ hc ?_ (mem_erase ho j) hu hr
          · simp only [annWd, List.map_cons, List.map_nil, sumBy_append, sumBy_one, depW]
            omega
          · exact mem_snoc hp ⟨rfl, Ne.symm hne, hmax⟩
  | tokXferFails j =>
    simp only [stdStep, step]
    cases hj : S.outbox[j]? with
    | none => exact hI
    | some w =>
      have hsum := sumBy_eraseIdx Wd.amount hj
      refine Inv.mk' ?_ hc hp (mem_erase ho j) hu
        (mem_snoc hr (rsOK_failed_none w.owner w.amount w.msg.isSome))
      simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | meStorageDeposit acc d =>
    simp only [stdStep, step]
    cases he : exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc) none, []⟩ with
    | none => exact hI
    | some o =>
      obtain ⟨hbal, hcalls⟩ := sd_exec he
      refine Inv.mk' ?_ hc ?_ ho hu hr
      · rw [hcalls, hbal]; simp only [annThird, List.map_nil, List.append_nil]; omega
      · rw [hcalls]; simpa [annThird] using hp
  | resolveWd k =>
    simp only [stdStep, step]
    cases hk : S.resolves[k]? with
    | none => exact hI
    | some r =>
      dsimp only
      have hsum := sumBy_eraseIdx Rs.unsettled hk
      have hok := hr r (List.mem_of_getElem? hk)
      have hrs' := mem_erase hr k
      cases hres : resolveWithdraw S.L r with
      | none => exact Inv.mk' (by omega) hc hp ho hu hrs'
      | some L' =>
        unfold resolveWithdraw at hres
        by_cases h0 : r.refund = 0
        · rw [ifP h0] at hres
          obtain rfl := Option.some.inj hres
          exact Inv.mk' (by omega) hc hp ho hu hrs'
        · rw [ifN h0] at hres
          obtain ⟨_, _, _, rfl⟩ := credit_some hres
          have hle : r.refund ≤ r.unsettled := by
            unfold RsOK at hok; unfold Rs.unsettled
            rcases hok.2 with h | h
            · omega
            · omega
          refine Inv.mk' (by simp only; omega) ?_ hp ho hu hrs'
          simp only; rw [total_credit]; omega
  | resolveWdFails k =>
    simp only [stdStep, step]
    by_cases hk : ∃ r, S.resolves[k]? = some r
    · obtain ⟨r, hk⟩ := hk
      have hsum := sumBy_eraseIdx Rs.unsettled hk
      exact Inv.mk' (by omega) hc hp ho hu (mem_erase hr k)
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
    simp only [stdStep, step]
    cases hm : moveBal S.L auth src dst amt with
    | none => exact hI
    | some L' =>
      obtain ⟨hne, _, _, hle, _, rfl⟩ := moveBal_some hm
      refine Inv.mk' hb ?_ hp ho hu hr
      simp only; rw [total_move _ _ _ _ hne hle]; exact hc
  | admin a =>
    simp only [stdStep, step]
    exact Inv.mk' hb hc hp ho hu hr

theorem inv_init {K : Cfg} {S : World} (h : Init K S) : Inv K S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold owed; rw [h.supply, h.unwrap, h.outbox, h.resolves, h.pend]; simp [sumBy]
  · rw [h.supply, h.bals]; rfl
  · rw [h.pend]; simp
  · rw [h.outbox]; simp
  · rw [h.unwrap]; simp
  · rw [h.resolves]; simp

theorem inv_reach {K : Cfg} {S : World} (h : Reach K S) : Inv K S := by
  induction h with
  | init S h => exact inv_init h
  | step st _ ih => exact inv_step K ih st

end Intents
