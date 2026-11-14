/-
  Facts about the proved wNEAR model, in the form the two-contract proofs use them: what one
  receipt on wNEAR does to the balance of one account (the Intents contract).
  Everything here is derived from `WNear.Lemmas` / `WNear.Theorems`.
-/
import IntentsW.World

namespace IntentsW
open WNear
open Intents (Wd Pend Ann depRes encU128)

/-- A successful `ft_transfer_call` moves a positive amount. -/
theorem ftc_pos {E : Env} {s : St} {p rc : Acct} {d x : Nat} {rs : List PR} {o : Out}
    (h : method E s ⟨p, d, .ft_transfer_call rc x, rs⟩ = some o) : 0 < x := by
  simp only [method] at h
  by_cases hd : d ≠ 1
  · simp [hd] at h
  · simp only [hd, ite_false] at h
    cases hq : iTransfer s.accts s.supply p rc x with
    | none => simp [hq] at h
    | some q =>
      obtain ⟨l', sup'⟩ := q
      exact (iTransfer_some hq).2.1

/-- A receipt from `p ≠ u` (and not from wNEAR itself) never lowers `u`'s balance, and starts
    at most one settlement callback, for a transfer that credited its receiver in full. -/
theorem third_call {E : Env} {c : St} {p u : Acct} {d : Nat} {m : Method} {rs : List PR} {o : Out}
    (hpu : p ≠ u) (hps : p ≠ E.self) (h : exec E c ⟨p, d, m, rs⟩ = some o) :
    bal c.accts u ≤ bal o.st.accts u ∧
    (o.calls = [] ∨ ∃ rc x, o.calls = [(p, rc, x)] ∧ p ≠ rc ∧ 0 < x ∧
        bal o.st.accts rc = bal c.accts rc + x) := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  refine ⟨by rw [ha]; exact method_no_lower u hpu hps hm, ?_⟩
  rcases calls_origin hm with h0 | ⟨rc, x, rfl, h1, hne, hb, _⟩
  · left; rw [hc]; exact h0
  · right; exact ⟨rc, x, by rw [hc]; exact h1, hne, ftc_pos hm, by rw [ha]; exact hb⟩

/-- The settlement callback: no new callback; nobody but the receiver loses, and the receiver
    loses at most the amount. -/
theorem resolve_exec {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {res : PR} {o : Out}
    (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o) :
    o.calls = [] ∧
    ∀ u, (u ≠ rc → bal c.accts u ≤ bal o.st.accts u) ∧ bal c.accts u ≤ bal o.st.accts u + amt := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  obtain ⟨_, _, res', l', sup', used, hrs, hq, rfl⟩ := method_resolve_some hm
  refine ⟨by rw [hc], fun u => ?_⟩
  rw [ha]
  exact resolve_lower hq u

/-- The contract's `ft_on_transfer` returned `"0"`: nothing is unused. -/
theorem unused_credited (amt : Nat) : unusedOf amt (depResW true) = 0 := by
  have h : depResW true = .ok (some 0) := by
    simp only [depResW, prW, depRes, Intents.parse_zero]
  rw [h]
  simp [unusedOf]

/-- After a credited deposit the settlement callback changes no balance. -/
theorem resolve_credited {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {o : Out}
    (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [depResW true]⟩ = some o) :
    o.st.accts = c.accts ∧ o.calls = [] := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  obtain ⟨_, _, res', l', sup', used, hrs, hq, rfl⟩ := method_resolve_some hm
  simp only [List.cons.injEq] at hrs
  obtain ⟨rfl, _⟩ := hrs
  have hf : refundOf c.accts rc amt (depResW true) = 0 := by
    have := refundOf_le_unused c.accts rc amt (depResW true)
    rw [unused_credited] at this; omega
  refine ⟨?_, by rw [hc]⟩
  rw [ha]
  rcases iResolve_cases hq with ⟨_, hl, _, _⟩ | ⟨hpos, _⟩ | ⟨hpos, _⟩
  · exact hl
  · rw [hf] at hpos; omega
  · rw [hf] at hpos; omega

/-- The settlement callback seen from the sender (`sn ≠ rc`): either the sender gets a refund
    `f ≤ amt` and the callback returns `amt - f`, or the sender is no longer registered, its
    balance stays 0 and the callback returns `amt`. -/
theorem resolve_sender {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {res : PR} {o : Out}
    (hne : sn ≠ rc) (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o) :
    o.calls = [] ∧ ∃ f, f ≤ amt ∧
      ((bal o.st.accts sn = bal c.accts sn + f ∧ o.ret = some (amt - f)) ∨
       (bal o.st.accts sn = bal c.accts sn ∧ o.ret = some amt)) := by
  obtain ⟨o0, hm, ha, _, _, hc, hret, _⟩ := exec_some h
  obtain ⟨h1, _, _, _, _, _, h7, h8, h9⟩ := T_resolve E c sn rc amt res o0 hne hm
  refine ⟨by rw [hc]; exact h7, refundOf c.accts rc amt res, h1, ?_⟩
  rw [ha, hret]
  cases hg : get c.accts sn with
  | some v =>
    obtain ⟨a, _, b⟩ := h8 ⟨v, hg⟩
    exact Or.inl ⟨a, b⟩
  | none =>
    obtain ⟨a, _, b⟩ := h9 hg
    right
    exact ⟨by rw [bal_of_none a, bal_of_none hg], b⟩

/-- The contract's `ft_transfer` / `ft_transfer_call` for a withdrawal: when it succeeds the
    contract's balance drops by exactly the amount; `ft_transfer` returns nothing and starts no
    callback, `ft_transfer_call` starts exactly the callback of this transfer. -/
theorem xfer_exec {E : Env} {c : St} {me : Acct} {w : Wd} {o : Out}
    (h : exec E c ⟨me, 1, xferMethodW w, []⟩ = some o) :
    me ≠ w.receiver ∧ 0 < w.amount ∧ bal o.st.accts me + w.amount = bal c.accts me ∧
    (w.msg = none → o.calls = [] ∧ o.ret = none) ∧
    (w.msg.isSome = true → o.calls = [(me, w.receiver, w.amount)]) := by
  obtain ⟨o0, hm, ha, _, _, hc, hret, _⟩ := exec_some h
  rw [ha, hc, hret]
  have key : ∀ {l' : Accts} {sup' : Nat},
      iTransfer c.accts c.supply me w.receiver w.amount = some (l', sup') →
      me ≠ w.receiver ∧ 0 < w.amount ∧ bal l' me + w.amount = bal c.accts me := by
    intro l' sup' hq
    obtain ⟨hne, hpos, bs, br, hgs, _, hle, _, _, rfl, _⟩ := iTransfer_some hq
    refine ⟨hne, hpos, ?_⟩
    rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self, bal_of_some hgs]; omega
  cases hmsg : w.msg with
  | none =>
    simp only [xferMethodW, hmsg, method] at hm
    cases hq : iTransfer c.accts c.supply me w.receiver w.amount with
    | none => simp [hq] at hm
    | some q =>
      obtain ⟨l', sup'⟩ := q
      simp [hq] at hm
      subst hm
      obtain ⟨k1, k2, k3⟩ := key hq
      exact ⟨k1, k2, k3, fun _ => ⟨rfl, rfl⟩, fun hs => by simp at hs⟩
  | some msg =>
    simp only [xferMethodW, hmsg, method] at hm
    cases hq : iTransfer c.accts c.supply me w.receiver w.amount with
    | none => simp [hq] at hm
    | some q =>
      obtain ⟨l', sup'⟩ := q
      simp [hq] at hm
      subst hm
      obtain ⟨k1, k2, k3⟩ := key hq
      exact ⟨k1, k2, k3, fun hn => by simp at hn, fun _ => rfl⟩

/-- `storage_deposit` changes no token balance and starts no callback. -/
theorem sd_exec {E : Env} {c : St} {p a : Acct} {d : Nat} {o : Out}
    (h : exec E c ⟨p, d, .storage_deposit (some a), []⟩ = some o) :
    (∀ x, bal o.st.accts x = bal c.accts x) ∧ o.calls = [] := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  rw [ha, hc]
  simp only [method, Option.getD_some] at hm
  cases hg : get c.accts a with
  | some v =>
    simp only [hg, Option.some.injEq] at hm
    subst hm
    exact ⟨fun _ => rfl, rfl⟩
  | none =>
    simp only [hg] at hm
    by_cases hd : d < E.minBal
    · simp [hd] at hm
    · simp only [hd, ite_false, Option.some.injEq] at hm
      subst hm
      refine ⟨fun x => ?_, rfl⟩
      by_cases hax : a = x
      · subst hax; rw [bal_set_self, bal_of_none hg]
      · rw [bal_set_ne _ _ hax]

/-- The token receipt of a withdrawal (with or without the storage deposit before it). -/
theorem batch_exec {E : Env} {c : St} {me : Acct} {w : Wd} {o : Out}
    (h : xferBatchW E me c w = some o) :
    me ≠ w.receiver ∧ 0 < w.amount ∧ bal o.st.accts me + w.amount = bal c.accts me ∧
    (w.msg = none → o.calls = [] ∧ o.ret = none) ∧
    (w.msg.isSome = true → o.calls = [(me, w.receiver, w.amount)]) := by
  unfold xferBatchW at h
  cases hsd : w.sd with
  | none =>
    simp only [hsd] at h
    exact xfer_exec h
  | some d =>
    simp only [hsd] at h
    cases h1 : exec E c ⟨me, d, .storage_deposit (some w.receiver), []⟩ with
    | none => simp [h1] at h
    | some o1 =>
      simp only [h1] at h
      cases h2 : exec E o1.st ⟨me, 1, xferMethodW w, []⟩ with
      | none => simp [h2] at h
      | some o2 =>
        simp only [h2, Option.some.injEq] at h
        subst h
        obtain ⟨hb, hc1⟩ := sd_exec h1
        obtain ⟨k1, kp, k2, k3, k4⟩ := xfer_exec h2
        refine ⟨k1, kp, by rw [← hb me]; exact k2, fun hn => ?_, fun hs => ?_⟩
        · obtain ⟨a, b⟩ := k3 hn
          exact ⟨by simp [hc1, a], b⟩
        · simp [hc1, k4 hs]

/-- The contract's `near_withdraw(x)`: when it succeeds, exactly `x` wNEAR is burned from the
    contract's balance and from the supply, nobody else's balance changes, no callback starts,
    and wNEAR sends the contract one NEAR transfer of `x + 1` (the amount and the attached
    yocto); wNEAR's own NEAR balance drops by `x`. -/
theorem nw_exec {E : Env} {c : St} {me : Acct} {x : Nat} {o : Out}
    (h : exec E c ⟨me, 1, .near_withdraw x, []⟩ = some o) :
    bal o.st.accts me + x = bal c.accts me ∧ o.st.supply + x = c.supply ∧
    (∀ a, a ≠ me → bal o.st.accts a = bal c.accts a) ∧
    o.calls = [] ∧ o.transfers = [(me, x + 1)] ∧ o.ret = none ∧ o.st.near + x = c.near := by
  obtain ⟨o0, hm, ha, hsu, htr, hc, hret, _, hpaid, hn⟩ := exec_some h
  rw [ha, hsu, htr, hc, hret, hn]
  simp only [method] at hm
  cases hq : iWithdraw c.accts c.supply me x with
  | none => simp [hq] at hm
  | some q =>
    obtain ⟨l', sup'⟩ := q
    by_cases hx : x + 1 ≤ U128_MAX
    · simp [hq, hx] at hm
      subst hm
      obtain ⟨b, hb, h1, h2, rfl, rfl⟩ := iWithdraw_some hq
      simp only [sumT_one] at hpaid ⊢
      refine ⟨?_, by omega, fun a ha' => ?_, trivial, trivial, trivial, by omega⟩
      · rw [bal_set_self, bal_of_some hb]; omega
      · rw [bal_set_ne _ _ (Ne.symm ha')]
    · simp [hq, hx] at hm

/-- With the invariant of the wNEAR model, `near_withdraw(x)` by a registered holder of at
    least `x` succeeds (the argument of `WNear.T_exit`, for one receipt). `hcap`: wNEAR's NEAR
    balance is below the bound on any NEAR balance. -/
theorem nw_succeeds {E : Env} (hE : E.Sane) {c : St} (hp : Pre c)
    (hsol : c.supply + c.accts.length * E.minBal + E.base ≤ c.near) (hcap : c.near < E.cap)
    {me : Acct} {b x : Nat} (hb : get c.accts me = some b) (hx : x ≤ b) :
    ∃ o, exec E c ⟨me, 1, .near_withdraw x, []⟩ = some o := by
  have hbs : b ≤ c.supply := by rw [hp.cons]; exact get_le_total hb
  have hx1 : x + 1 ≤ U128_MAX := by have := hE.cap_lt; omega
  have hw : iWithdraw c.accts c.supply me x = some (set c.accts me (b - x), c.supply - x) := by
    simp [iWithdraw, hb, hx, Nat.le_trans hx hbs]
  have hm : method E c ⟨me, 1, .near_withdraw x, []⟩ =
      some ⟨⟨set c.accts me (b - x), c.supply - x, c.near⟩, [(me, x + 1)], [], none⟩ := by
    simp [method, hw, hx1]
  exact ⟨_, exec_of_method hE hp hsol (by simp only; omega) hm⟩

/-! ### Annotations -/

theorem resOfW_other {e : Pend} (res : PR) (h : e.ann = .other) : resOfW e res = some res := by
  simp [resOfW, h]

theorem resOfW_wd {e : Pend} {o : Acct} (res : PR) (h : e.ann = .wd o) :
    resOfW e res = some res := by
  simp [resOfW, h]

theorem resOfW_dep_none {e : Pend} (res : PR) (h : e.ann = .dep none) : resOfW e res = none := by
  simp [resOfW, h]

theorem resOfW_dep_some {e : Pend} {b : Bool} (res : PR) (h : e.ann = .dep (some b)) :
    resOfW e res = some (depResW b) := by
  simp [resOfW, h]

end IntentsW
