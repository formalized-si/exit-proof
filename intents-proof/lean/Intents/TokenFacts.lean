/-
  Facts about the proved token model, in the form the two-contract proofs use them:
  what one receipt on the token does to the balance of one account (the Intents contract).
  Everything here is derived from `ProvedFT.Lemmas` / `ProvedFT.Theorems`.
-/
import Intents.World

namespace Intents
open ProvedFT

/-- A receipt from `p ≠ u` never lowers `u`'s balance, and starts at most one settlement
    callback, for a transfer that credited its receiver in full. -/
theorem third_call {E : Env} {c : St} {p u : Acct} {d : Nat} {m : Method} {rs : List PR} {o : Out}
    (hpu : p ≠ u) (h : exec E c ⟨p, d, m, resultsFor E p rs⟩ = some o) :
    bal c.accts u ≤ bal o.st.accts u ∧
    (o.calls = [] ∨ ∃ rc x, o.calls = [(p, rc, x)] ∧ p ≠ rc ∧ 0 < x ∧
        bal o.st.accts rc = bal c.accts rc + x) := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  have hres : ∀ sn rc amt, m = .ft_resolve_transfer sn rc amt → False := by
    intro sn rc amt hmr
    subst hmr
    obtain ⟨hps, _, _, _, _, _, _, _, hrs, _⟩ := method_resolve_some hm
    simp [resultsFor, hps] at hrs
  refine ⟨by rw [ha]; exact method_no_lower u hpu hres hm, ?_⟩
  rcases calls_origin hm with h0 | ⟨rc, x, _, _, _, h1, hne, hx, hb, _⟩
  · left; rw [hc]; exact h0
  · right; exact ⟨rc, x, by rw [hc]; exact h1, hne, hx, by rw [ha]; exact hb⟩

/-- The settlement callback: no new callback; nobody but the receiver loses, and the receiver
    loses at most the amount. -/
theorem resolve_exec {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {res : PR} {o : Out}
    (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o) :
    o.calls = [] ∧
    ∀ u, (u ≠ rc → bal c.accts u ≤ bal o.st.accts u) ∧ bal c.accts u ≤ bal o.st.accts u + amt := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  obtain ⟨_, _, res', rest, l', sup', used, evs, hrs, hq, rfl⟩ := method_resolve_some hm
  refine ⟨by rw [hc], fun u => ?_⟩
  rw [ha]
  exact resolve_lower hq u

theorem parse_zero : parseU128Json [0x22, 0x30, 0x22] = some 0 := by decide

/-- The contract's `ft_on_transfer` returned `"0"`: nothing is unused. -/
theorem unused_credited (amt : Nat) : unusedOf amt (depRes true) = 0 := by
  simp [depRes, unusedOf, parse_zero, MAX_RESULT_LENGTH]

/-- After a credited deposit the settlement callback changes no balance. -/
theorem resolve_credited {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {o : Out}
    (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [depRes true]⟩ = some o) :
    o.st.accts = c.accts ∧ o.calls = [] := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  obtain ⟨_, _, res', rest, l', sup', used, evs, hrs, hq, rfl⟩ := method_resolve_some hm
  simp only [List.cons.injEq] at hrs
  obtain ⟨rfl, _⟩ := hrs
  have hf : refundOf c.accts rc amt (depRes true) = 0 := by
    have := refundOf_le_unused c.accts rc amt (depRes true)
    rw [unused_credited] at this; omega
  refine ⟨?_, by rw [hc]⟩
  rw [ha]
  rcases iResolve_cases hq with ⟨_, hl, _, _, _⟩ | ⟨hpos, _⟩ | ⟨hpos, _⟩
  · exact hl
  · rw [hf] at hpos; omega
  · rw [hf] at hpos; omega

/-- The settlement callback seen from the sender (`sn ≠ rc`): either the sender gets a refund
    `f ≤ amt` and the callback returns `amt - f`, or the sender is no longer registered, its
    balance stays 0 and the callback returns `amt`. -/
theorem resolve_sender {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {res : PR} {o : Out}
    (hne : sn ≠ rc) (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o) :
    o.calls = [] ∧ ∃ f, f ≤ amt ∧
      ((bal o.st.accts sn = bal c.accts sn + f ∧ o.ret = .u128 (amt - f)) ∨
       (bal o.st.accts sn = bal c.accts sn ∧ o.ret = .u128 amt)) := by
  obtain ⟨o0, hm, ha, _, _, hc, hret, _⟩ := exec_some h
  obtain ⟨h1, _, _, _, _, _, h7, h8, h9⟩ := P2_settlement_call E c sn rc amt res o0 hne hm
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
    contract's balance drops by exactly the amount; `ft_transfer` returns `()` and starts no
    callback, `ft_transfer_call` starts exactly the callback of this transfer. -/
theorem xfer_exec {E : Env} {c : St} {me : Acct} {w : Wd} {o : Out}
    (h : exec E c ⟨me, 1, xferMethod w, []⟩ = some o) :
    me ≠ w.receiver ∧ bal o.st.accts me + w.amount = bal c.accts me ∧
    (w.msg = none → o.calls = [] ∧ o.ret = .unit) ∧
    (w.msg.isSome = true → o.calls = [(me, w.receiver, w.amount)]) := by
  obtain ⟨o0, hm, ha, _, _, hc, hret, _⟩ := exec_some h
  rw [ha, hc, hret]
  have key : ∀ {l' : Accts} {sup' : Nat},
      iTransfer c.accts c.supply me w.receiver w.amount = some (l', sup') →
      me ≠ w.receiver ∧ bal l' me + w.amount = bal c.accts me := by
    intro l' sup' hq
    obtain ⟨hne, _, bs, br, hgs, _, hle, _, _, rfl, _⟩ := iTransfer_some hq
    refine ⟨hne, ?_⟩
    rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self, bal_of_some hgs]; omega
  cases hmsg : w.msg with
  | none =>
    simp only [xferMethod, hmsg, method] at hm
    cases hq : iTransfer c.accts c.supply me w.receiver w.amount with
    | none => simp [hq] at hm
    | some q =>
      obtain ⟨l', sup'⟩ := q
      simp [hq] at hm
      subst hm
      obtain ⟨k1, k2⟩ := key hq
      exact ⟨k1, k2, fun _ => ⟨rfl, rfl⟩, fun hs => by simp at hs⟩
  | some msg =>
    simp only [xferMethod, hmsg, method] at hm
    cases hq : iTransfer c.accts c.supply me w.receiver w.amount with
    | none => simp [hq] at hm
    | some q =>
      obtain ⟨l', sup'⟩ := q
      simp [hq] at hm
      subst hm
      obtain ⟨k1, k2⟩ := key hq
      exact ⟨k1, k2, fun hn => by simp at hn, fun _ => rfl⟩

/-- `storage_deposit` changes no token balance and starts no callback. -/
theorem sd_exec {E : Env} {c : St} {p a : Acct} {d : Nat} {ro : Option Bool} {o : Out}
    (h : exec E c ⟨p, d, .storage_deposit (some a) ro, []⟩ = some o) :
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
    (h : xferBatch (exec E) me c w = some o) :
    me ≠ w.receiver ∧ bal o.st.accts me + w.amount = bal c.accts me ∧
    (w.msg = none → o.calls = [] ∧ o.ret = .unit) ∧
    (w.msg.isSome = true → o.calls = [(me, w.receiver, w.amount)]) := by
  unfold xferBatch at h
  cases hsd : w.sd with
  | none =>
    simp only [hsd] at h
    exact xfer_exec h
  | some d =>
    simp only [hsd] at h
    cases h1 : exec E c ⟨me, d, .storage_deposit (some w.receiver) none, []⟩ with
    | none => simp [h1] at h
    | some o1 =>
      simp only [h1] at h
      cases h2 : exec E o1.st ⟨me, 1, xferMethod w, []⟩ with
      | none => simp [h2] at h
      | some o2 =>
        simp only [h2, Option.some.injEq] at h
        subst h
        obtain ⟨hb, hc1⟩ := sd_exec h1
        obtain ⟨k1, k2, k3, k4⟩ := xfer_exec h2
        refine ⟨k1, by rw [← hb me]; exact k2, fun hn => ?_, fun hs => ?_⟩
        · obtain ⟨a, b⟩ := k3 hn
          exact ⟨by simp [hc1, a], b⟩
        · simp [hc1, k4 hs]

/-! ### Annotations -/

theorem raw_annThird (me : Acct) (calls : List (Acct × Acct × Nat)) :
    (annThird me calls).map Pend.raw = calls := by
  induction calls with
  | nil => rfl
  | cons q t ih =>
    simp only [annThird, List.map_cons, List.map_map] at ih ⊢
    rw [ih]; rfl

theorem raw_annWd (owner : Acct) (calls : List (Acct × Acct × Nat)) :
    (annWd owner calls).map Pend.raw = calls := by
  induction calls with
  | nil => rfl
  | cons q t ih =>
    simp only [annWd, List.map_cons, List.map_map] at ih ⊢
    rw [ih]; rfl

theorem resOf_other {e : Pend} (res : PR) (h : e.ann = .other) : resOf e res = some res := by
  simp [resOf, h]

theorem resOf_wd {e : Pend} {o : Acct} (res : PR) (h : e.ann = .wd o) : resOf e res = some res := by
  simp [resOf, h]

theorem resOf_dep_none {e : Pend} (res : PR) (h : e.ann = .dep none) : resOf e res = none := by
  simp [resOf, h]

theorem resOf_dep_some {e : Pend} {b : Bool} (res : PR) (h : e.ann = .dep (some b)) :
    resOf e res = some (depRes b) := by
  simp [resOf, h]

theorem wdDone_other {e : Pend} (res : PR) (l : Nat) (h : e.ann = .other) : wdDone e res l = [] := by
  simp [wdDone, h]

theorem wdDone_dep {e : Pend} {s : Option Bool} (res : PR) (l : Nat) (h : e.ann = .dep s) :
    wdDone e res l = [] := by
  simp [wdDone, h]

theorem wdDone_wd {e : Pend} {o : Acct} (res : PR) (l : Nat) (h : e.ann = .wd o) :
    wdDone e res l = [⟨o, e.amount, true, res, l⟩] := by
  simp [wdDone, h]

theorem depW_other {e : Pend} (h : e.ann = .other) : depW e = 0 := by simp [depW, h]
theorem depW_wd {e : Pend} {o : Acct} (h : e.ann = .wd o) : depW e = 0 := by simp [depW, h]
theorem depW_credited {e : Pend} (h : e.ann = .dep (some true)) : depW e = 0 := by simp [depW, h]
theorem depW_failed {e : Pend} (h : e.ann = .dep (some false)) : depW e = e.amount := by
  simp [depW, h]
theorem depW_fresh {e : Pend} (h : e.ann = .dep none) : depW e = e.amount := by simp [depW, h]

theorem depW_le (e : Pend) : depW e ≤ e.amount := by
  unfold depW; split <;> omega

theorem sumBy_depW_annWd (owner : Acct) (calls : List (Acct × Acct × Nat)) :
    sumBy depW (annWd owner calls) = 0 := by
  apply sumBy_eq_zero
  intro e he
  simp only [annWd, List.mem_map] at he
  obtain ⟨q, _, rfl⟩ := he
  rfl

end Intents
