/-
  Specifications of the FungibleToken internals and of each method of the model.
-/
import ProvedFT.Model

namespace ProvedFT

/-! ### Internals -/

theorem iWithdraw_some {l : Accts} {sup : Nat} {a : Acct} {x : Nat} {l' : Accts} {sup' : Nat}
    (h : iWithdraw l sup a x = some (l', sup')) :
    ∃ b, get l a = some b ∧ x ≤ b ∧ x ≤ sup ∧ l' = set l a (b - x) ∧ sup' = sup - x := by
  unfold iWithdraw at h
  cases hg : get l a with
  | none => simp [hg] at h
  | some b =>
    simp only [hg] at h
    by_cases h1 : x ≤ b
    · by_cases h2 : x ≤ sup
      · simp [h1, h2] at h
        exact ⟨b, rfl, h1, h2, h.1.symm, h.2.symm⟩
      · simp [h1, h2] at h
    · simp [h1] at h

theorem iDeposit_some {l : Accts} {sup : Nat} {a : Acct} {x : Nat} {l' : Accts} {sup' : Nat}
    (h : iDeposit l sup a x = some (l', sup')) :
    ∃ b, get l a = some b ∧ b + x ≤ U128_MAX ∧ sup + x ≤ U128_MAX ∧
      l' = set l a (b + x) ∧ sup' = sup + x := by
  unfold iDeposit at h
  cases hg : get l a with
  | none => simp [hg] at h
  | some b =>
    simp only [hg] at h
    by_cases h1 : b + x ≤ U128_MAX
    · by_cases h2 : sup + x ≤ U128_MAX
      · simp [h1, h2] at h
        exact ⟨b, rfl, h1, h2, h.1.symm, h.2.symm⟩
      · simp [h1, h2] at h
    · simp [h1] at h

theorem iTransfer_some {l : Accts} {sup : Nat} {s r : Acct} {x : Nat} {l' : Accts} {sup' : Nat}
    (h : iTransfer l sup s r x = some (l', sup')) :
    s ≠ r ∧ 0 < x ∧ ∃ bs br, get l s = some bs ∧ get l r = some br ∧ x ≤ bs ∧ x ≤ sup ∧
      br + x ≤ U128_MAX ∧ l' = set (set l s (bs - x)) r (br + x) ∧ sup' = sup := by
  unfold iTransfer at h
  by_cases hsr : s = r
  · simp [hsr] at h
  · by_cases hx : x = 0
    · simp [hsr, hx] at h
    · simp only [hsr, hx, ite_false] at h
      cases hw : iWithdraw l sup s x with
      | none => simp [hw] at h
      | some q =>
        obtain ⟨l1, sup1⟩ := q
        simp only [hw] at h
        obtain ⟨bs, hgs, h1, h2, rfl, rfl⟩ := iWithdraw_some hw
        obtain ⟨br, hgr, h3, _, rfl, rfl⟩ := iDeposit_some h
        rw [get_set_ne l _ hsr] at hgr
        exact ⟨hsr, Nat.pos_of_ne_zero hx, bs, br, hgs, hgr, h1, h2, h3, rfl, by omega⟩

theorem unusedOf_le (amt : Nat) (res : PR) : unusedOf amt res ≤ amt := by
  cases res with
  | failed => simp [unusedOf]
  | ok b =>
    simp only [unusedOf]
    by_cases hl : b.length ≤ MAX_RESULT_LENGTH
    · rw [if_pos hl]
      cases parseU128Json b with
      | none => exact Nat.le_refl _
      | some v => exact Nat.min_le_right _ _
    · rw [if_neg hl]; exact Nat.le_refl _

theorem refundOf_le_bal (l : Accts) (r : Acct) (amt : Nat) (res : PR) :
    refundOf l r amt res ≤ bal l r := by
  unfold refundOf; split <;> simp [Nat.min_le_left]

theorem refundOf_le_unused (l : Accts) (r : Acct) (amt : Nat) (res : PR) :
    refundOf l r amt res ≤ unusedOf amt res := by
  unfold refundOf; split <;> simp [Nat.min_le_right]

theorem refundOf_le_amt (l : Accts) (r : Acct) (amt : Nat) (res : PR) :
    refundOf l r amt res ≤ amt :=
  Nat.le_trans (refundOf_le_unused l r amt res) (unusedOf_le amt res)

theorem get_of_bal_pos {l : Accts} {a : Acct} (h : 0 < bal l a) : ∃ v, get l a = some v := by
  cases hg : get l a with
  | none => rw [bal_of_none hg] at h; omega
  | some v => exact ⟨v, rfl⟩

/-- The three outcomes of `internal_ft_resolve_transfer`. -/
theorem iResolve_cases {l : Accts} {sup : Nat} {s r : Acct} {amt : Nat} {res : PR}
    {l' : Accts} {sup' used : Nat} {evs : List Ev}
    (h : iResolve l sup s r amt res = some (l', sup', used, evs)) :
    let f := refundOf l r amt res
    let l1 := set l r (bal l r - f)
    (f = 0 ∧ l' = l ∧ sup' = sup ∧ used = amt ∧ evs = []) ∨
    (0 < f ∧ ∃ sb, get l1 s = some sb ∧ sb + f ≤ U128_MAX ∧ l' = set l1 s (sb + f) ∧ sup' = sup ∧
      used = amt - f ∧ evs = [.transfer r s f (some "refund")]) ∨
    (0 < f ∧ get l1 s = none ∧ f ≤ sup ∧ l' = l1 ∧ sup' = sup - f ∧ used = amt ∧
      evs = [.burn r f (some "refund")]) := by
  intro f l1
  unfold iResolve at h
  by_cases hu : 0 < unusedOf amt res
  · by_cases hb : 0 < bal l r
    · have hf : f = min (bal l r) (unusedOf amt res) := by
        simp [f, refundOf, hu, hb]
      have hfpos : 0 < f := by rw [hf]; exact Nat.lt_min.mpr ⟨hb, hu⟩
      rw [if_pos hu, if_pos hb] at h
      simp only at h
      rw [← hf] at h
      cases hg : get l1 s with
      | some sb =>
        simp only [l1] at hg
        simp only [hg] at h
        by_cases ho : sb + f ≤ U128_MAX
        · rw [if_pos ho] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inl ⟨hfpos, sb, rfl, ho, rfl, rfl, rfl, rfl⟩)
        · rw [if_neg ho] at h; exact absurd h (by simp)
      | none =>
        simp only [l1] at hg
        simp only [hg] at h
        by_cases ho : f ≤ sup
        · rw [if_pos ho] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr ⟨hfpos, rfl, ho, rfl, rfl, rfl, rfl⟩)
        · rw [if_neg ho] at h; exact absurd h (by simp)
    · have hf : f = 0 := by simp [f, refundOf, hb]
      rw [if_pos hu, if_neg hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨hf, rfl, rfl, rfl, rfl⟩
  · have hf : f = 0 := by simp [f, refundOf, hu]
    rw [if_neg hu] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨hf, rfl, rfl, rfl, rfl⟩

/-! ### State facts -/

/-- What every successful call of the contract code guarantees. `obl` is the storage
    bookkeeping: one storage refund per registered account plus the NEAR paid out never
    exceed the refunds owed before plus the deposit. -/
structure Good (E : Env) (s : St) (d : Nat) (o : Out) : Prop where
  pre : Pre o.st
  obl : o.st.accts.length * E.minBal + sumT o.transfers ≤ s.accts.length * E.minBal + d
  near : o.st.near = s.near

theorem sumT_nil : sumT [] = 0 := rfl
theorem sumT_one (a : Acct) (x : Nat) : sumT [(a, x)] = x := by simp [sumT]

theorem satAdd_le (a b : Nat) : satAdd a b ≤ a + b := Nat.min_le_left _ _

theorem satAdd_eq {a b : Nat} (h : a + b ≤ U128_MAX) : satAdd a b = a + b := by
  simp [satAdd, Nat.min_eq_left h]

theorem pre_set {s : St} (hs : Pre s) (a : Acct) (v sup' n : Nat)
    (hsup : sup' + bal s.accts a = s.supply + v) (hb : sup' ≤ U128_MAX) :
    Pre ⟨set s.accts a v, sup', n⟩ := by
  refine ⟨nodup_set hs.nodup a v, ?_, hb⟩
  have := total_set s.accts a v
  have := hs.cons
  simp only; omega

theorem good_view {E : Env} {s : St} {d : Nat} (hs : Pre s) (v : Ret) :
    Good E s d ⟨s, [], [], [], v⟩ :=
  ⟨hs, by simp [sumT], rfl⟩

/-! ### One lemma per method -/

theorem good_transfer_core {s : St} {p rc : Acct} {x : Nat} {l' : Accts} {sup' : Nat}
    (hs : Pre s) (hq : iTransfer s.accts s.supply p rc x = some (l', sup')) :
    Pre ⟨l', sup', s.near⟩ ∧ l'.length = s.accts.length := by
  obtain ⟨hne, _, bs, br, hgs, hgr, h1, h2, h3, rfl, rfl⟩ := iTransfer_some hq
  have hs1 : Pre ⟨set s.accts p (bs - x), s.supply - x, s.near⟩ :=
    pre_set hs p _ _ _ (by rw [bal_of_some hgs]; omega) (by have := hs.bound; omega)
  have hgr1 : get (set s.accts p (bs - x)) rc = some br := by rw [get_set_ne _ _ hne]; exact hgr
  refine ⟨?_, ?_⟩
  · exact pre_set hs1 rc (br + x) s.supply s.near (by simp only; rw [bal_of_some hgr1]; omega)
      hs.bound
  · rw [length_set_some hgr1, length_set_some hgs]

theorem good_ft_transfer {E : Env} {s : St} {p rc : Acct} {d x : Nat} {memo : Option String}
    {rs : List PR} {o : Out} (hs : Pre s)
    (h : method E s ⟨p, d, .ft_transfer rc x memo, rs⟩ = some o) : Good E s d o := by
  simp only [method] at h
  by_cases hd : d ≠ 1
  · simp [hd] at h
  · simp only [hd, ite_false] at h
    cases hq : iTransfer s.accts s.supply p rc x with
    | none => simp [hq] at h
    | some q =>
      obtain ⟨l', sup'⟩ := q
      simp only [hq, Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := good_transfer_core hs hq
      exact ⟨h1, by simp only [sumT_nil]; rw [h2]; omega, rfl⟩

theorem good_ft_transfer_call {E : Env} {s : St} {p rc : Acct} {d x : Nat}
    {memo : Option String} {msg : String} {rs : List PR} {o : Out} (hs : Pre s)
    (h : method E s ⟨p, d, .ft_transfer_call rc x memo msg, rs⟩ = some o) : Good E s d o := by
  simp only [method] at h
  by_cases hd : d ≠ 1
  · simp [hd] at h
  · simp only [hd, ite_false] at h
    cases hq : iTransfer s.accts s.supply p rc x with
    | none => simp [hq] at h
    | some q =>
      obtain ⟨l', sup'⟩ := q
      simp only [hq, Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := good_transfer_core hs hq
      exact ⟨h1, by simp only [sumT_nil]; rw [h2]; omega, rfl⟩

/-- The resolve call, unfolded: only the contract itself, no deposit, a promise result. -/
theorem method_resolve_some {E : Env} {s : St} {p sn rc : Acct} {d amt : Nat} {rs : List PR}
    {o : Out} (h : method E s ⟨p, d, .ft_resolve_transfer sn rc amt, rs⟩ = some o) :
    p = E.self ∧ d = 0 ∧ ∃ res rest l' sup' used evs, rs = res :: rest ∧
      iResolve s.accts s.supply sn rc amt res = some (l', sup', used, evs) ∧
      o = ⟨⟨l', sup', s.near⟩, [], [], evs, .u128 used⟩ := by
  simp only [method] at h
  by_cases hp : p ≠ E.self
  · simp [hp] at h
  · simp only [hp, ite_false] at h
    by_cases hd : d ≠ 0
    · simp [hd] at h
    · simp only [hd, ite_false] at h
      refine ⟨by simpa using hp, by simpa using hd, ?_⟩
      match rs, h with
      | res :: rest, h =>
        cases hq : iResolve s.accts s.supply sn rc amt res with
        | none => simp [hq] at h
        | some q =>
          obtain ⟨l', sup', used, evs⟩ := q
          simp only [hq, Option.some.injEq] at h
          exact ⟨res, rest, l', sup', used, evs, rfl, hq, h.symm⟩

theorem good_resolve_core {s : St} {sn rc : Acct} {amt : Nat} {res : PR} {l' : Accts}
    {sup' used : Nat} {evs : List Ev} (hs : Pre s)
    (hq : iResolve s.accts s.supply sn rc amt res = some (l', sup', used, evs)) :
    Pre ⟨l', sup', s.near⟩ ∧ sup' ≤ s.supply ∧ l'.length = s.accts.length := by
  rcases iResolve_cases hq with ⟨_, rfl, rfl, _, _⟩ | ⟨hf, sb, hg, ho, rfl, rfl, _, _⟩ |
      ⟨hf, hg, ho, rfl, rfl, _, _⟩
  · exact ⟨⟨hs.nodup, hs.cons, hs.bound⟩, Nat.le_refl _, rfl⟩
  · have hb := refundOf_le_bal s.accts rc amt res
    have ht := bal_le_total s.accts rc
    have hc := hs.cons
    have hB := hs.bound
    obtain ⟨v, hv⟩ := get_of_bal_pos (Nat.lt_of_lt_of_le hf hb)
    have hs1 : Pre ⟨set s.accts rc (bal s.accts rc - refundOf s.accts rc amt res),
        s.supply - refundOf s.accts rc amt res, s.near⟩ :=
      pre_set hs rc (bal s.accts rc - refundOf s.accts rc amt res)
        (s.supply - refundOf s.accts rc amt res) s.near (by omega) (by omega)
    refine ⟨pre_set hs1 sn (sb + refundOf s.accts rc amt res) s.supply s.near
      (by simp only; rw [bal_of_some hg]; omega) hB, Nat.le_refl _, ?_⟩
    rw [length_set_some hg, length_set_some hv]
  · have hb := refundOf_le_bal s.accts rc amt res
    have ht := bal_le_total s.accts rc
    have hc := hs.cons
    have hB := hs.bound
    obtain ⟨v, hv⟩ := get_of_bal_pos (Nat.lt_of_lt_of_le hf hb)
    refine ⟨pre_set hs rc (bal s.accts rc - refundOf s.accts rc amt res)
      (s.supply - refundOf s.accts rc amt res) s.near (by omega) (by omega), by omega, ?_⟩
    rw [length_set_some hv]

theorem good_resolve {E : Env} {s : St} {p sn rc : Acct} {d amt : Nat} {rs : List PR} {o : Out}
    (hs : Pre s) (h : method E s ⟨p, d, .ft_resolve_transfer sn rc amt, rs⟩ = some o) :
    Good E s d o := by
  obtain ⟨_, rfl, res, rest, l', sup', used, evs, rfl, hq, rfl⟩ := method_resolve_some h
  obtain ⟨h1, h2, h3⟩ := good_resolve_core hs hq
  exact ⟨h1, by simp only [sumT_nil]; rw [h3]; omega, rfl⟩

theorem good_storage_deposit {E : Env} {s : St} {p : Acct} {d : Nat} {acc : Option Acct}
    {ro : Option Bool} {rs : List PR} {o : Out} (hs : Pre s)
    (h : method E s ⟨p, d, .storage_deposit acc ro, rs⟩ = some o) : Good E s d o := by
  simp only [method] at h
  cases hg : get s.accts (acc.getD p) with
  | some w =>
    simp only [hg, Option.some.injEq] at h
    subst h
    refine ⟨hs, ?_, rfl⟩
    by_cases hd : 0 < d
    · simp only [hd, ite_true, sumT_one]; omega
    · simp only [hd, ite_false, sumT_nil]; omega
  | none =>
    simp only [hg] at h
    by_cases hm : d < E.minBal
    · simp [hm] at h
    · simp only [hm, ite_false, Option.some.injEq] at h
      subst h
      refine ⟨pre_set hs _ 0 _ _ (by rw [bal_of_none hg]) hs.bound, ?_, rfl⟩
      simp only [length_set_none hg, Nat.add_mul, Nat.one_mul]
      by_cases hd : 0 < d - E.minBal
      · simp only [hd, ite_true, sumT_one]; omega
      · simp only [hd, ite_false, sumT_nil]; omega

theorem good_storage_withdraw {E : Env} {s : St} {p : Acct} {d : Nat} {amt : Option Nat}
    {rs : List PR} {o : Out} (hs : Pre s)
    (h : method E s ⟨p, d, .storage_withdraw amt, rs⟩ = some o) : Good E s d o := by
  simp only [method] at h
  by_cases hd : d ≠ 1
  · simp [hd] at h
  · simp only [hd, ite_false] at h
    cases hg : get s.accts p with
    | none => simp [hg] at h
    | some w =>
      simp only [hg] at h
      cases amt with
      | none =>
        simp only [Option.some.injEq] at h; subst h; exact good_view hs _
      | some a =>
        simp only at h
        by_cases ha : 0 < a
        · simp [ha] at h
        · simp only [ha, ite_false, Option.some.injEq] at h; subst h; exact good_view hs _

theorem good_storage_unregister {E : Env} {s : St} {p : Acct} {d : Nat} {f : Option Bool}
    {rs : List PR} {o : Out} (hs : Pre s)
    (h : method E s ⟨p, d, .storage_unregister f, rs⟩ = some o) : Good E s d o := by
  simp only [method] at h
  by_cases hd : d ≠ 1
  · simp [hd] at h
  · simp only [hd, ite_false] at h
    cases hg : get s.accts p with
    | none =>
      simp only [hg, Option.some.injEq] at h; subst h; exact good_view hs _
    | some b =>
      simp only [hg] at h
      by_cases hc : b = 0 ∨ f = some true
      · simp only [hc, ite_true] at h
        by_cases hc2 : b ≤ s.supply
        · simp only [hc2, ite_true, Option.some.injEq] at h
          subst h
          have he := total_erase s.accts p
          rw [bal_of_some hg] at he
          have hl := length_erase_some hg
          have hsat := satAdd_le E.minBal 1
          refine ⟨⟨nodup_erase hs.nodup p, ?_, ?_⟩, ?_, rfl⟩
          · have := hs.cons; simp only; omega
          · have := hs.bound; simp only; omega
          · simp only [sumT_one]
            rw [← hl, Nat.add_mul, Nat.one_mul]; omega
        · simp only [hc2, ite_false] at h
          exact absurd h (by simp)
      · simp [hc] at h

/-- Every successful call keeps the structural facts and the storage bookkeeping. -/
theorem method_good (E : Env) {s : St} (hs : Pre s) {r : Rcpt} {o : Out}
    (h : method E s r = some o) : Good E s r.deposit o := by
  obtain ⟨p, d, m, rs⟩ := r
  cases m with
  | reinit => simp [method] at h
  | bad => simp [method] at h
  | ft_total_supply => simp only [method, Option.some.injEq] at h; subst h; exact good_view hs _
  | ft_balance_of a => simp only [method, Option.some.injEq] at h; subst h; exact good_view hs _
  | storage_balance_bounds =>
    simp only [method, Option.some.injEq] at h; subst h; exact good_view hs _
  | storage_balance_of a =>
    simp only [method, Option.some.injEq] at h; subst h; exact good_view hs _
  | ft_transfer rc x memo => exact good_ft_transfer hs h
  | ft_transfer_call rc x memo msg => exact good_ft_transfer_call hs h
  | ft_resolve_transfer sn rc amt => exact good_resolve hs h
  | storage_deposit acc ro => exact good_storage_deposit hs h
  | storage_withdraw amt => exact good_storage_withdraw hs h
  | storage_unregister f => exact good_storage_unregister hs h

/-- `exec` only adds the runtime's NEAR accounting to `method`. -/
theorem exec_some {E : Env} {s : St} {r : Rcpt} {o : Out} (h : exec E s r = some o) :
    ∃ o0, method E s r = some o0 ∧ o.st.accts = o0.st.accts ∧ o.st.supply = o0.st.supply ∧
      o.transfers = o0.transfers ∧ o.calls = o0.calls ∧ o.ret = o0.ret ∧
      s.near + r.deposit ≤ E.cap ∧ sumT o0.transfers ≤ s.near + r.deposit ∧
      o.st.near = s.near + r.deposit - sumT o0.transfers := by
  unfold exec at h
  cases hm : method E s r with
  | none => simp [hm] at h
  | some o0 =>
    simp only [hm] at h
    by_cases hc : s.near + r.deposit ≤ E.cap ∧ sumT o0.transfers ≤ s.near + r.deposit ∧
        E.base + stor E.entry o0.st.accts ≤ s.near + r.deposit - sumT o0.transfers
    · simp only [hc, and_self, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨o0, rfl, rfl, rfl, rfl, rfl, rfl, hc.1, hc.2.1, rfl⟩
    · simp only [hc, ite_false] at h; exact absurd h (by simp)

/-- `ft_transfer_call` is the only method that starts a settlement callback, and the entry it
    creates is exactly the transfer it made. -/
theorem calls_origin {E : Env} {s : St} {p : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (h : method E s ⟨p, d, m, rs⟩ = some o) :
    o.calls = [] ∨ ∃ rc x memo msg, m = .ft_transfer_call rc x memo msg ∧
      o.calls = [(p, rc, x)] ∧ p ≠ rc ∧ 0 < x ∧
      bal o.st.accts rc = bal s.accts rc + x ∧ bal o.st.accts p + x = bal s.accts p := by
  cases m with
  | ft_transfer_call rc x memo msg =>
    right
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
      cases hq : iTransfer s.accts s.supply p rc x with
      | none => simp [hq] at h
      | some q =>
        obtain ⟨l', sup'⟩ := q
        simp only [hq, Option.some.injEq] at h; subst h
        obtain ⟨hne, hx, bs, br, hgs, hgr, h1, _, _, rfl, rfl⟩ := iTransfer_some hq
        refine ⟨rc, x, memo, msg, rfl, rfl, hne, hx, ?_, ?_⟩
        · simp only; rw [bal_set_self, bal_of_some hgr]
        · simp only; rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self, bal_of_some hgs]; omega
  | ft_resolve_transfer sn rc amt =>
    left
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := method_resolve_some h
    rfl
  | _ =>
    left
    simp only [method] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (obtain rfl := Option.some.inj h; rfl)
      | (simp only [Option.some.injEq] at h; subst h; rfl)
      | skip
    all_goals (simp_all)

end ProvedFT
