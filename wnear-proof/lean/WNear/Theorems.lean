/-
  The four statements about wrap.near (see REPORT.md for the plain-words version):

  * T_conservation  — `inv_step`, `T_conservation`, `T_force_unregister_burns`
  * T_resolve       — `T_resolve`, `T_resolve_private`, `T_resolve_private_sys`, `T_resolve_never_fails`
  * T_exit          — `T_exit`, `exit_always`, `exit_full`
  * T_no_one_else   — `T_no_one_else`, `T_who_can_lower`
-/
import WNear.Lemmas

namespace WNear

/-- The invariant of every reachable state: map without repeated keys, `total_supply` = sum
    of balances (conservation), supply fits u128, and **solvency**: the contract's NEAR covers
    every wNEAR, one storage refund (`minBal`) per registered account, and the base storage
    stake. -/
structure Inv (E : Env) (S : Sys) : Prop where
  pre : Pre S.c
  solvent : S.c.supply + S.c.accts.length * E.minBal + E.base ≤ S.c.near
  cap : S.c.near ≤ E.cap

theorem exec_inv {E : Env} {s : St} (hs : Pre s)
    (hsol : s.supply + s.accts.length * E.minBal + E.base ≤ s.near) {r : Rcpt} {o : Out}
    (h : exec E s r = some o) :
    Pre o.st ∧ o.st.supply + o.st.accts.length * E.minBal + E.base ≤ o.st.near ∧
      o.st.near ≤ E.cap := by
  obtain ⟨o0, hm, ha, hsu, _, _, _, hcap, hpaid, hn⟩ := exec_some h
  have hg := method_good E hs hm
  have hobl := hg.obl
  refine ⟨⟨by rw [ha]; exact hg.pre.nodup, by rw [ha, hsu]; exact hg.pre.cons,
    by rw [hsu]; exact hg.pre.bound⟩, ?_, ?_⟩
  · rw [ha, hsu, hn]; omega
  · rw [hn]; omega

/-- With the invariant, the runtime's checks (balance for the transfers, storage stake) never
    fail: `exec` succeeds exactly when the code does. -/
theorem exec_of_method {E : Env} (hE : E.Sane) {s : St} (hs : Pre s)
    (hsol : s.supply + s.accts.length * E.minBal + E.base ≤ s.near) {r : Rcpt}
    (hcap : s.near + r.deposit ≤ E.cap) {o0 : Out} (hm : method E s r = some o0) :
    exec E s r = some { o0 with st := { o0.st with near := s.near + r.deposit - sumT o0.transfers } } := by
  have hg := method_good E hs hm
  have hobl := hg.obl
  have hst := stor_le E.entry E.minBal hE.entry_le o0.st.accts
  unfold exec
  rw [hm]
  have h2 : sumT o0.transfers ≤ s.near + r.deposit := by omega
  have h3 : E.base + stor E.entry o0.st.accts ≤ s.near + r.deposit - sumT o0.transfers := by
    omega
  simp [hcap, h2, h3]

/-! ## T_conservation -/

/-- Every step keeps the invariant: any call by anyone, any callback with any promise result,
    a dropped callback, NEAR arriving. -/
theorem inv_step (E : Env) {S : Sys} (hI : Inv E S) (st : Step) : Inv E (sysStep E S st) := by
  cases st with
  | call p d m rs =>
    simp only [sysStep]
    by_cases hp : p = E.self
    · simp only [hp, if_true]; exact hI
    · simp only [hp, if_false]
      cases he : exec E S.c ⟨p, d, m, rs⟩ with
      | none => exact hI
      | some o =>
        obtain ⟨h1, h2, h3⟩ := exec_inv hI.pre hI.solvent he
        exact ⟨h1, h2, h3⟩
  | resolve i res =>
    simp only [sysStep]
    cases hp : S.pending[i]? with
    | none => exact hI
    | some q =>
      obtain ⟨sn, rc, amt⟩ := q
      simp only
      cases he : exec E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ with
      | none => exact ⟨hI.pre, hI.solvent, hI.cap⟩
      | some o =>
        obtain ⟨h1, h2, h3⟩ := exec_inv hI.pre hI.solvent he
        exact ⟨h1, h2, h3⟩
  | resolveFails i => exact ⟨hI.pre, hI.solvent, hI.cap⟩
  | nearIn x =>
    simp only [sysStep]
    by_cases hx : S.c.near + x ≤ E.cap
    · simp only [hx, if_true]
      exact ⟨⟨hI.pre.nodup, hI.pre.cons, hI.pre.bound⟩, by have := hI.solvent; simp only; omega,
        by simp only; omega⟩
    · simp only [hx, if_false]; exact hI

theorem inv_reach {E : Env} {S : Sys} (h : Reach E S) : Inv E S := by
  induction h with
  | init n h1 h2 =>
    exact ⟨⟨trivial, rfl, Nat.zero_le _⟩, by simp only [List.length_nil, Nat.zero_mul]; omega, h2⟩
  | step st _ ih => exact inv_step E ih st

/-- **T_conservation.** In every reachable state `total_supply` equals the sum of all balances. -/
theorem T_conservation {E : Env} {S : Sys} (h : Reach E S) : S.c.supply = total S.c.accts :=
  (inv_reach h).pre.cons

/-- **Force-unregister burns.** `storage_unregister(force = true)` by a registered `u` holding
    `b` removes `u`, burns `b` (total_supply drops by `b`), keeps the NEAR that backed `b` in the
    contract, and pays `u` only the storage deposit plus the attached 1 yoctoNEAR. -/
theorem T_force_unregister_burns (E : Env) (hE : E.Sane) (S : Sys) (hI : Inv E S) (u : Acct)
    (hu : u ≠ E.self) (hcap : S.c.near < E.cap) (b : Nat) (hb : get S.c.accts u = some b) :
    let S' := sysStep E S (.call u 1 (.storage_unregister (some true)) [])
    S'.c.accts = erase S.c.accts u ∧ S'.c.supply = S.c.supply - b ∧
      S'.c.near = S.c.near - E.minBal ∧ S'.pending = S.pending ∧
      S'.paid = S.paid ++ [(u, E.minBal + 1)] := by
  have hbs : b ≤ S.c.supply := by rw [hI.pre.cons]; exact get_le_total hb
  have hm : method E S.c ⟨u, 1, .storage_unregister (some true), []⟩ =
      some ⟨⟨erase S.c.accts u, S.c.supply - b, S.c.near⟩, [(u, E.minBal + 1)], [], none⟩ := by
    simp [method, hb, hbs, hE.min_lt]
  have he := exec_of_method hE hI.pre hI.solvent (by simp only; omega) hm
  have hl := length_pos_of_get hb
  have hlm : E.minBal ≤ S.c.accts.length * E.minBal := by
    obtain ⟨k, hk⟩ : ∃ k, S.c.accts.length = k + 1 := ⟨S.c.accts.length - 1, by omega⟩
    rw [hk, Nat.add_mul, Nat.one_mul]; omega
  have hsol := hI.solvent
  simp only [sysStep, hu, if_false, he, sumT_one, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> (try rfl) <;> omega

/-! ## T_resolve -/

/-- **T_resolve, caller check.** Called by anyone but the contract itself, `ft_resolve_transfer`
    fails (`#[private]`), whatever the arguments, deposit or promise results. -/
theorem T_resolve_private (E : Env) (s : St) (p : Acct) (hp : p ≠ E.self) (d : Nat)
    (sn rc : Acct) (amt : Nat) (rs : List PR) :
    method E s ⟨p, d, .ft_resolve_transfer sn rc amt, rs⟩ = none := by
  simp [method, hp]

/-- The same at the system level: such a call changes nothing at all. -/
theorem T_resolve_private_sys (E : Env) (S : Sys) (p : Acct) (d : Nat) (sn rc : Acct)
    (amt : Nat) (rs : List PR) :
    sysStep E S (.call p d (.ft_resolve_transfer sn rc amt) rs) = S := by
  simp only [sysStep]
  by_cases hp : p = E.self
  · simp [hp]
  · have hm := T_resolve_private E S.c p hp d sn rc amt rs
    simp only [hp, if_false]
    unfold exec; rw [hm]

/-- **T_resolve, amounts.** When the callback of a transfer of `amt` from `sn` to `rc` runs
    with any promise result, the refund `f` taken from the receiver is at most the transferred
    amount, at most what the receiver holds at that moment (it may have moved the tokens away
    or unregistered: then `f` is smaller or 0) and at most the unused amount it reported.
    The receiver loses exactly `f`; nobody else but the sender is touched; if the sender is
    registered it gains exactly `f` (sender + receiver conserved, supply unchanged) and the
    call returns `amt - f`; if the sender has unregistered, `f` is burned from the supply and
    the call returns `amt`. -/
theorem T_resolve (E : Env) (s : St) (sn rc : Acct) (amt : Nat) (res : PR) (o : Out)
    (hne : sn ≠ rc)
    (h : method E s ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o) :
    let f := refundOf s.accts rc amt res
    f ≤ amt ∧ f ≤ bal s.accts rc ∧ f ≤ unusedOf amt res ∧
    bal o.st.accts rc + f = bal s.accts rc ∧
    (∀ a, a ≠ sn → a ≠ rc → get o.st.accts a = get s.accts a) ∧
    o.transfers = [] ∧ o.calls = [] ∧
    ((∃ v, get s.accts sn = some v) →
      bal o.st.accts sn = bal s.accts sn + f ∧ o.st.supply = s.supply ∧ o.ret = some (amt - f)) ∧
    (get s.accts sn = none →
      get o.st.accts sn = none ∧ o.st.supply + f = s.supply ∧ o.ret = some amt) := by
  intro f
  obtain ⟨_, _, res', l', sup', used, hrs, hq, rfl⟩ := method_resolve_some h
  cases hrs
  have hfa := refundOf_le_amt s.accts rc amt res
  have hfb := refundOf_le_bal s.accts rc amt res
  have hfu := refundOf_le_unused s.accts rc amt res
  have hgs1 : get (set s.accts rc (bal s.accts rc - f)) sn = get s.accts sn :=
    get_set_ne _ _ (Ne.symm hne)
  suffices H : bal l' rc + f = bal s.accts rc ∧
      (∀ a, a ≠ sn → a ≠ rc → get l' a = get s.accts a) ∧
      ((∃ v, get s.accts sn = some v) → bal l' sn = bal s.accts sn + f ∧ sup' = s.supply ∧
        used = amt - f) ∧
      (get s.accts sn = none → get l' sn = none ∧ sup' + f = s.supply ∧ used = amt) by
    obtain ⟨H1, H2, H3, H4⟩ := H
    refine ⟨hfa, hfb, hfu, H1, H2, rfl, rfl, fun hv => ?_, fun hn => ?_⟩
    · obtain ⟨a, b, c⟩ := H3 hv; exact ⟨a, b, by rw [c]⟩
    · obtain ⟨a, b, c⟩ := H4 hn; exact ⟨a, b, by rw [c]⟩
  rcases iResolve_cases hq with ⟨hf0, hl, hsu, hus⟩ | ⟨hf, sb, hg, ho, hl, hsu, hus⟩ |
      ⟨hf, hg, ho, hl, hsu, hus⟩
  · -- nothing to refund
    subst hl hsu
    have hf0' : f = 0 := hf0
    refine ⟨by omega, fun a _ _ => rfl, fun _ => ⟨by omega, rfl, by omega⟩,
      fun hn => ⟨hn, by omega, hus⟩⟩
  · -- refund to a registered sender
    subst hl hsu
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bal_set_ne _ _ hne, bal_set_self]; omega
    · intro a ha1 ha2
      rw [get_set_ne _ _ (Ne.symm ha1), get_set_ne _ _ (Ne.symm ha2)]
    · intro _
      refine ⟨?_, rfl, hus⟩
      rw [bal_set_self]
      have : bal s.accts sn = sb := bal_of_some (hgs1 ▸ hg)
      omega
    · intro hn; rw [hgs1, hn] at hg; cases hg
  · -- sender unregistered: burn
    subst hl hsu
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bal_set_self]; omega
    · intro a _ ha2
      rw [get_set_ne _ _ (Ne.symm ha2)]
    · intro ⟨v, hv⟩; rw [hgs1, hv] at hg; cases hg
    · intro _
      exact ⟨hg, by omega, hus⟩

theorem iResolve_total {l : Accts} {sup : Nat} (sn rc : Acct) (amt : Nat) (res : PR)
    (hc : sup = total l) (hb : sup ≤ U128_MAX) : ∃ q, iResolve l sup sn rc amt res = some q := by
  unfold iResolve
  by_cases hu : 0 < unusedOf amt res
  · by_cases hbr : 0 < bal l rc
    · simp only [hu, hbr, if_true]
      have hmin := Nat.min_le_left (bal l rc) (unusedOf amt res)
      have ht := total_set l rc (bal l rc - min (bal l rc) (unusedOf amt res))
      have htl := bal_le_total l rc
      cases hg : get (set l rc (bal l rc - min (bal l rc) (unusedOf amt res))) sn with
      | some sb =>
        have := get_le_total hg
        have ho : sb + min (bal l rc) (unusedOf amt res) ≤ U128_MAX := by omega
        simp [ho]
      | none =>
        have ho : min (bal l rc) (unusedOf amt res) ≤ sup := by omega
        simp [ho]
    · simp [hu, hbr]
  · simp [hu]

/-- **T_resolve, the refund cannot be blocked.** In every reachable state the callback
    succeeds for any promise result (no overflow or underflow is possible); only running out of
    gas can stop it, which `Step.resolveFails` covers. -/
theorem T_resolve_never_fails (E : Env) (hE : E.Sane) (S : Sys) (hI : Inv E S) (sn rc : Acct)
    (amt : Nat) (res : PR) :
    ∃ o, exec E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o := by
  obtain ⟨⟨l', sup', used⟩, hq⟩ := iResolve_total (l := S.c.accts) sn rc amt res hI.pre.cons
    hI.pre.bound
  have hm : method E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ =
      some ⟨⟨l', sup', S.c.near⟩, [], [], some used⟩ := by
    simp [method, hq]
  exact ⟨_, exec_of_method hE hI.pre hI.solvent (by have := hI.cap; simp only; omega) hm⟩

/-! ## T_exit -/

/-- **T_exit (one step, any amount).** From any state satisfying the invariant, a registered
    `u` (not the contract itself) holding `b` that calls `near_withdraw(x)`, `x ≤ b`, with
    exactly 1 yoctoNEAR succeeds: its balance becomes `b - x`, total_supply drops by `x`, the
    contract's NEAR drops by `x`, and the contract sends `u` a transfer of `x + 1` yoctoNEAR.
    `hcap`: the contract's balance is below the total NEAR supply (u holds the 1 yocto). -/
theorem T_exit (E : Env) (hE : E.Sane) (S : Sys) (hI : Inv E S) (u : Acct) (hu : u ≠ E.self)
    (hcap : S.c.near < E.cap) (b : Nat) (hb : get S.c.accts u = some b) (x : Nat) (hx : x ≤ b) :
    let S' := sysStep E S (.call u 1 (.near_withdraw x) [])
    S'.c.accts = set S.c.accts u (b - x) ∧ S'.c.supply = S.c.supply - x ∧
      S'.c.near = S.c.near - x ∧ S'.pending = S.pending ∧ S'.paid = S.paid ++ [(u, x + 1)] := by
  have hbs : b ≤ S.c.supply := by rw [hI.pre.cons]; exact get_le_total hb
  have hsol := hI.solvent
  have hx1 : x + 1 ≤ U128_MAX := by have := hE.cap_lt; omega
  have hw : iWithdraw S.c.accts S.c.supply u x = some (set S.c.accts u (b - x), S.c.supply - x) := by
    simp [iWithdraw, hb, hx, Nat.le_trans hx hbs]
  have hm : method E S.c ⟨u, 1, .near_withdraw x, []⟩ =
      some ⟨⟨set S.c.accts u (b - x), S.c.supply - x, S.c.near⟩, [(u, x + 1)], [], none⟩ := by
    simp [method, hw, hx1]
  have he := exec_of_method hE hI.pre hI.solvent (by simp only; omega) hm
  simp only [sysStep, hu, if_false, he, sumT_one, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> (try rfl) <;> omega

/-- **T_exit (headline).** Whatever happened before — any interleaving of anyone's calls, any
    behaviour of any receiver contract — a registered holder `u` (any account but wrap.near
    itself) with wNEAR balance `b` calls `near_withdraw(b)` attaching 1 yoctoNEAR, and the call
    succeeds: `u`'s balance becomes 0 and the contract sends `u` `b + 1` yoctoNEAR (its `b`
    plus the 1 yocto back). Nobody else has to act, and nothing anyone did before can make the
    call fail. -/
theorem exit_always (E : Env) (hE : E.Sane) (S : Sys) (hR : Reach E S) (u : Acct)
    (hu : u ≠ E.self) (hcap : S.c.near < E.cap) (b : Nat) (hb : get S.c.accts u = some b) :
    let S' := sysStep E S (.call u 1 (.near_withdraw b) [])
    bal S'.c.accts u = 0 ∧ S'.c.supply = S.c.supply - b ∧ S'.paid = S.paid ++ [(u, b + 1)] := by
  obtain ⟨h1, h2, _, _, h5⟩ := T_exit E hE S (inv_reach hR) u hu hcap b hb b (Nat.le_refl b)
  refine ⟨?_, h2, h5⟩
  rw [h1, bal_set_self]; simp

/-- **T_exit (full exit).** Two own calls — `near_withdraw(b)` and `storage_unregister()`, each
    with 1 yoctoNEAR — leave `u` unregistered and paid `b + 1` and then `minBal + 1`:
    all its wNEAR as NEAR plus its storage deposit back (net of the 2 yocto it attached). -/
theorem exit_full (E : Env) (hE : E.Sane) (S : Sys) (hI : Inv E S) (u : Acct) (hu : u ≠ E.self)
    (hcap : S.c.near < E.cap) (b : Nat) (hb : get S.c.accts u = some b) :
    let S1 := sysStep E S (.call u 1 (.near_withdraw b) [])
    let S2 := sysStep E S1 (.call u 1 (.storage_unregister none) [])
    get S2.c.accts u = none ∧ S2.paid = S.paid ++ [(u, b + 1), (u, E.minBal + 1)] := by
  intro S1 S2
  obtain ⟨h1, h2, h3, h4, h5⟩ := T_exit E hE S hI u hu hcap b hb b (Nat.le_refl b)
  have hI1 : Inv E S1 := inv_step E hI _
  have hg1 : get S1.c.accts u = some 0 := by rw [h1, Nat.sub_self, get_set_self]
  have hcap1 : S1.c.near < E.cap := by rw [h3]; omega
  have hm : method E S1.c ⟨u, 1, .storage_unregister none, []⟩ =
      some ⟨⟨erase S1.c.accts u, S1.c.supply - 0, S1.c.near⟩, [(u, E.minBal + 1)], [], none⟩ := by
    simp [method, hg1, hE.min_lt]
  have he := exec_of_method hE hI1.pre hI1.solvent (by simp only; omega) hm
  have hS2 : S2 = sysStep E S1 (.call u 1 (.storage_unregister none) []) := rfl
  simp only [hS2, sysStep, hu, if_false, he, List.append_nil]
  refine ⟨get_erase_self hI1.pre.nodup u, ?_⟩
  rw [h5]; simp

/-! ## T_no_one_else -/

/-- A call by `p` that is neither the contract nor `u` never lowers `u`'s balance. -/
theorem method_no_lower {E : Env} {s : St} {p : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (u : Acct) (hpu : p ≠ u) (hps : p ≠ E.self)
    (h : method E s ⟨p, d, m, rs⟩ = some o) : bal s.accts u ≤ bal o.st.accts u := by
  cases m with
  | new => simp [method] at h
  | bad => simp [method] at h
  | view => simp only [method, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | near_deposit =>
    simp only [method] at h
    by_cases hd : d = 0
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hg : get s.accts p with
      | some w =>
        simp only [hg] at h
        cases hq : iDeposit s.accts s.supply p d with
        | none => simp [hq] at h
        | some q =>
          obtain ⟨l', sup'⟩ := q
          simp only [hq, Option.some.injEq] at h; subst h
          obtain ⟨b, _, _, _, rfl, rfl⟩ := iDeposit_some hq
          simp only; rw [bal_set_ne _ _ hpu]; exact Nat.le_refl _
      | none =>
        simp only [hg] at h
        by_cases hm : d < E.minBal
        · simp [hm] at h
        · simp only [hm, if_false] at h
          cases hq : iDeposit (set s.accts p 0) s.supply p (d - E.minBal) with
          | none => simp [hq] at h
          | some q =>
            obtain ⟨l', sup'⟩ := q
            simp only [hq, Option.some.injEq] at h; subst h
            obtain ⟨b, _, _, _, rfl, rfl⟩ := iDeposit_some hq
            simp only; rw [bal_set_ne _ _ hpu, bal_set_ne _ _ hpu]; exact Nat.le_refl _
  | near_withdraw x =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hq : iWithdraw s.accts s.supply p x with
      | none => simp [hq] at h
      | some q =>
        obtain ⟨l', sup'⟩ := q
        simp only [hq] at h
        by_cases hx : x + 1 ≤ U128_MAX
        · simp only [hx, if_true, Option.some.injEq] at h; subst h
          obtain ⟨b, _, _, _, rfl, rfl⟩ := iWithdraw_some hq
          simp only; rw [bal_set_ne _ _ hpu]; exact Nat.le_refl _
        · simp [hx] at h
  | ft_transfer rc x | ft_transfer_call rc x =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hq : iTransfer s.accts s.supply p rc x with
      | none => simp [hq] at h
      | some q =>
        obtain ⟨l', sup'⟩ := q
        simp only [hq, Option.some.injEq] at h; subst h
        obtain ⟨hne, _, bs, br, _, hgr, _, _, _, rfl, rfl⟩ := iTransfer_some hq
        simp only
        by_cases hru : rc = u
        · subst hru; rw [bal_set_self, bal_of_some hgr]; omega
        · rw [bal_set_ne _ _ hru, bal_set_ne _ _ hpu]; exact Nat.le_refl _
  | ft_resolve_transfer sn rc amt =>
    obtain ⟨hp, _⟩ := method_resolve_some h
    exact absurd hp hps
  | storage_deposit acc =>
    simp only [method] at h
    cases hg : get s.accts (acc.getD p) with
    | some w => simp only [hg, Option.some.injEq] at h; subst h; exact Nat.le_refl _
    | none =>
      simp only [hg] at h
      by_cases hm : d < E.minBal
      · simp [hm] at h
      · simp only [hm, if_false, Option.some.injEq] at h; subst h
        simp only
        by_cases hau : acc.getD p = u
        · rw [← hau, bal_set_self, bal_of_none hg]; exact Nat.le_refl _
        · rw [bal_set_ne _ _ hau]; exact Nat.le_refl _
  | storage_withdraw amt =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hgp : get s.accts p with
      | none => simp [hgp] at h
      | some w =>
        simp only [hgp] at h
        cases amt with
        | none => simp only [Option.some.injEq] at h; subst h; exact Nat.le_refl _
        | some a =>
          simp only at h
          by_cases ha : 0 < a
          · simp [ha] at h
          · simp only [ha, if_false, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | storage_unregister f =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hg : get s.accts p with
      | none => simp only [hg, Option.some.injEq] at h; subst h; exact Nat.le_refl _
      | some b =>
        simp only [hg] at h
        by_cases hc : b = 0 ∨ f = some true
        · simp only [hc, if_true] at h
          by_cases hc2 : b ≤ s.supply ∧ E.minBal + 1 ≤ U128_MAX
          · simp only [hc2, and_self, if_true, Option.some.injEq] at h; subst h
            simp only; rw [bal_erase_ne _ hpu]; exact Nat.le_refl _
          · simp only [hc2, if_false] at h; exact absurd h (by simp)
        · simp [hc] at h

/-- In a resolve callback, an account that is not the receiver never loses; the receiver loses
    at most the transferred amount. -/
theorem resolve_lower {s : St} {sn rc : Acct} {amt : Nat} {res : PR} {l' : Accts}
    {sup' used : Nat} (hq : iResolve s.accts s.supply sn rc amt res = some (l', sup', used))
    (u : Acct) : (u ≠ rc → bal s.accts u ≤ bal l' u) ∧ bal s.accts u ≤ bal l' u + amt := by
  have hfa := refundOf_le_amt s.accts rc amt res
  have hfb := refundOf_le_bal s.accts rc amt res
  rcases iResolve_cases hq with ⟨_, rfl, _, _⟩ | ⟨_, sb, hg, _, rfl, _, _⟩ | ⟨_, _, _, rfl, _, _⟩
  · exact ⟨fun _ => Nat.le_refl _, by omega⟩
  · by_cases hus : sn = u
    · subst hus
      have hb1 : bal (set s.accts rc (bal s.accts rc - refundOf s.accts rc amt res)) sn = sb :=
        bal_of_some hg
      rw [bal_set_self]
      by_cases hur : sn = rc
      · subst hur; rw [bal_set_self] at hb1; constructor <;> omega
      · rw [bal_set_ne _ _ (Ne.symm hur)] at hb1; constructor <;> omega
    · rw [bal_set_ne _ _ hus]
      by_cases hur : rc = u
      · subst hur; rw [bal_set_self]; exact ⟨fun h => absurd rfl h, by omega⟩
      · rw [bal_set_ne _ _ hur]; exact ⟨fun _ => Nat.le_refl _, by omega⟩
  · by_cases hur : rc = u
    · subst hur; rw [bal_set_self]; exact ⟨fun h => absurd rfl h, by omega⟩
    · rw [bal_set_ne _ _ hur]; exact ⟨fun _ => Nat.le_refl _, by omega⟩

/-- **T_no_one_else.** A step that is not a call by `u` never lowers `u`'s balance, with one
    exception: the contract's own `ft_resolve_transfer` callback of a transfer some `sn` made
    *to* `u` with `ft_transfer_call`; that callback takes back at most the amount that transfer
    credited to `u`. (u's own calls are listed in `T_who_can_lower`.) -/
theorem T_no_one_else (E : Env) (S : Sys) (u : Acct) (st : Step)
    (hst : ∀ d m rs, st ≠ .call u d m rs) :
    bal S.c.accts u ≤ bal (sysStep E S st).c.accts u ∨
    ∃ i res sn amt, st = .resolve i res ∧ S.pending[i]? = some (sn, u, amt) ∧
      bal S.c.accts u ≤ bal (sysStep E S st).c.accts u + amt := by
  cases st with
  | call p d m rs =>
    left
    have hpu : p ≠ u := fun h => hst d m rs (by rw [h])
    simp only [sysStep]
    by_cases hp : p = E.self
    · simp only [hp, if_true]; exact Nat.le_refl _
    · simp only [hp, if_false]
      cases he : exec E S.c ⟨p, d, m, rs⟩ with
      | none => exact Nat.le_refl _
      | some o =>
        obtain ⟨o0, hm, ha, _⟩ := exec_some he
        simp only; rw [ha]; exact method_no_lower u hpu hp hm
  | resolve i res =>
    cases hpi : S.pending[i]? with
    | none => left; simp only [sysStep, hpi]; exact Nat.le_refl _
    | some q =>
      obtain ⟨sn, rc, amt⟩ := q
      have key : (u ≠ rc → bal S.c.accts u ≤ bal (sysStep E S (.resolve i res)).c.accts u) ∧
          bal S.c.accts u ≤ bal (sysStep E S (.resolve i res)).c.accts u + amt := by
        simp only [sysStep, hpi]
        cases he : exec E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ with
        | none => exact ⟨fun _ => Nat.le_refl _, Nat.le_add_right _ _⟩
        | some o =>
          obtain ⟨o0, hm, ha, _⟩ := exec_some he
          obtain ⟨_, _, res', l', sup', used, hrs, hq, rfl⟩ := method_resolve_some hm
          simp only; rw [ha]
          exact resolve_lower hq u
      by_cases hur : u = rc
      · subst hur; exact Or.inr ⟨i, res, sn, amt, rfl, hpi, key.2⟩
      · exact Or.inl (key.1 hur)
  | resolveFails i => left; exact Nat.le_refl _
  | nearIn x =>
    left; simp only [sysStep]
    by_cases hx : S.c.near + x ≤ E.cap
    · simp only [hx, if_true]; exact Nat.le_refl _
    · simp only [hx, if_false]; exact Nat.le_refl _

/-- A call by `u` itself lowers `u`'s balance only through these four methods. -/
theorem method_self_lower {E : Env} {s : St} {u : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (hus : u ≠ E.self) (h : method E s ⟨u, d, m, rs⟩ = some o)
    (hlt : bal o.st.accts u < bal s.accts u) :
    (∃ x, m = .near_withdraw x) ∨ (∃ rc x, m = .ft_transfer rc x) ∨
    (∃ rc x, m = .ft_transfer_call rc x) ∨ m = .storage_unregister (some true) := by
  cases m with
  | near_withdraw x => exact Or.inl ⟨x, rfl⟩
  | ft_transfer rc x => exact Or.inr (Or.inl ⟨rc, x, rfl⟩)
  | ft_transfer_call rc x => exact Or.inr (Or.inr (Or.inl ⟨rc, x, rfl⟩))
  | new => simp [method] at h
  | bad => simp [method] at h
  | view => simp only [method, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
  | ft_resolve_transfer sn rc amt =>
    obtain ⟨hp, _⟩ := method_resolve_some h; exact absurd hp hus
  | near_deposit =>
    exfalso
    simp only [method] at h
    by_cases hd : d = 0
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hg : get s.accts u with
      | some w =>
        simp only [hg] at h
        cases hq : iDeposit s.accts s.supply u d with
        | none => simp [hq] at h
        | some q =>
          obtain ⟨l', sup'⟩ := q
          simp only [hq, Option.some.injEq] at h; subst h
          obtain ⟨b, hb, _, _, rfl, rfl⟩ := iDeposit_some hq
          simp only at hlt; rw [bal_set_self, bal_of_some hb] at hlt; omega
      | none =>
        simp only [hg] at h
        by_cases hm : d < E.minBal
        · simp [hm] at h
        · simp only [hm, if_false] at h
          cases hq : iDeposit (set s.accts u 0) s.supply u (d - E.minBal) with
          | none => simp [hq] at h
          | some q =>
            obtain ⟨l', sup'⟩ := q
            simp only [hq, Option.some.injEq] at h; subst h
            obtain ⟨b, _, _, _, rfl, rfl⟩ := iDeposit_some hq
            simp only at hlt; rw [bal_set_self, bal_of_none hg] at hlt; omega
  | storage_deposit acc =>
    exfalso
    simp only [method] at h
    cases hg : get s.accts (acc.getD u) with
    | some w => simp only [hg, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
    | none =>
      simp only [hg] at h
      by_cases hm : d < E.minBal
      · simp [hm] at h
      · simp only [hm, if_false, Option.some.injEq] at h; subst h
        simp only at hlt
        by_cases hau : acc.getD u = u
        · rw [hau] at hg; rw [bal_of_none hg] at hlt; omega
        · rw [bal_set_ne _ _ hau] at hlt; omega
  | storage_withdraw amt =>
    exfalso
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hgp : get s.accts u with
      | none => simp [hgp] at h
      | some w =>
        simp only [hgp] at h
        cases amt with
        | none => simp only [Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
        | some a =>
          simp only at h
          by_cases ha : 0 < a
          · simp [ha] at h
          · simp only [ha, if_false, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
  | storage_unregister f =>
    cases f with
    | some fb =>
      cases fb with
      | true => exact Or.inr (Or.inr (Or.inr rfl))
      | false =>
        exfalso
        simp only [method] at h
        by_cases hd : d ≠ 1
        · simp [hd] at h
        · simp only [hd, if_false] at h
          cases hg : get s.accts u with
          | none => simp only [hg, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
          | some b =>
            simp only [hg] at h
            by_cases hb0 : b = 0
            · rw [bal_of_some hg, hb0] at hlt; omega
            · simp [hb0] at h
    | none =>
      exfalso
      simp only [method] at h
      by_cases hd : d ≠ 1
      · simp [hd] at h
      · simp only [hd, if_false] at h
        cases hg : get s.accts u with
        | none => simp only [hg, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
        | some b =>
          simp only [hg] at h
          by_cases hb0 : b = 0
          · rw [bal_of_some hg, hb0] at hlt; omega
          · simp [hb0] at h

/-- **T_who_can_lower (exact list).** If a step lowers `u`'s balance, it is one of:
    `u`'s own `near_withdraw`, `ft_transfer`, `ft_transfer_call`, `storage_unregister(force =
    true)`; or the contract's resolve callback of an `ft_transfer_call` whose receiver is `u`. -/
theorem T_who_can_lower (E : Env) (S : Sys) (u : Acct) (hus : u ≠ E.self) (st : Step)
    (hlt : bal (sysStep E S st).c.accts u < bal S.c.accts u) :
    (∃ d x rs, st = .call u d (.near_withdraw x) rs) ∨
    (∃ d rc x rs, st = .call u d (.ft_transfer rc x) rs) ∨
    (∃ d rc x rs, st = .call u d (.ft_transfer_call rc x) rs) ∨
    (∃ d rs, st = .call u d (.storage_unregister (some true)) rs) ∨
    (∃ i res sn amt, st = .resolve i res ∧ S.pending[i]? = some (sn, u, amt)) := by
  by_cases hcall : ∃ d m rs, st = .call u d m rs
  · obtain ⟨d, m, rs, rfl⟩ := hcall
    simp only [sysStep, hus, if_false] at hlt
    cases he : exec E S.c ⟨u, d, m, rs⟩ with
    | none => rw [he] at hlt; simp only at hlt; omega
    | some o =>
      rw [he] at hlt
      obtain ⟨o0, hm, ha, _⟩ := exec_some he
      simp only at hlt; rw [ha] at hlt
      rcases method_self_lower hus hm hlt with ⟨x, rfl⟩ | ⟨rc, x, rfl⟩ | ⟨rc, x, rfl⟩ | rfl
      · exact Or.inl ⟨d, x, rs, rfl⟩
      · exact Or.inr (Or.inl ⟨d, rc, x, rs, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨d, rc, x, rs, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, rs, rfl⟩)))
  · have hst : ∀ d m rs, st ≠ .call u d m rs := fun d m rs h => hcall ⟨d, m, rs, h⟩
    rcases T_no_one_else E S u st hst with h | ⟨i, res, sn, amt, h1, h2, _⟩
    · omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, res, sn, amt, h1, h2⟩)))

/-- **Origin of a callback in flight.** Only a successful `ft_transfer_call` creates one, and
    the entry `(sender, receiver, amount)` it creates is exactly the transfer it made: the
    receiver was credited `amount`, the sender debited `amount`, sender ≠ receiver. -/
theorem calls_origin {E : Env} {s : St} {p : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (h : method E s ⟨p, d, m, rs⟩ = some o) :
    o.calls = [] ∨ ∃ rc x, m = .ft_transfer_call rc x ∧ o.calls = [(p, rc, x)] ∧ p ≠ rc ∧
      bal o.st.accts rc = bal s.accts rc + x ∧ bal o.st.accts p + x = bal s.accts p := by
  cases m with
  | ft_transfer_call rc x =>
    right
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, if_false] at h
      cases hq : iTransfer s.accts s.supply p rc x with
      | none => simp [hq] at h
      | some q =>
        obtain ⟨l', sup'⟩ := q
        simp only [hq, Option.some.injEq] at h; subst h
        obtain ⟨hne, _, bs, br, hgs, hgr, h1, _, _, rfl, rfl⟩ := iTransfer_some hq
        refine ⟨rc, x, rfl, rfl, hne, ?_, ?_⟩
        · simp only; rw [bal_set_self, bal_of_some hgr]
        · simp only; rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self, bal_of_some hgs]; omega
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

/-! ## Solvency on mainnet -/

/-- The solvency part of `Inv` from numbers RPC returns for one block: if every account entry
    costs at least half the storage refund (`minBal` = 125 bytes, an entry ≥ 63 bytes since an
    account id has ≥ 2 characters) and `total_supply + 2 × (storage stake) ≤ balance`, where
    the storage stake is `storage_usage × byte cost` = `base + stor entry accts`, then
    `supply + accounts × minBal + base ≤ balance`. -/
theorem solvent_of_stake_bound (E : Env) (s : St) (he : ∀ a, E.minBal ≤ 2 * E.entry a)
    (h : s.supply + 2 * (E.base + stor E.entry s.accts) ≤ s.near) :
    s.supply + s.accts.length * E.minBal + E.base ≤ s.near := by
  have := length_mul_le_stor E.entry E.minBal he s.accts
  omega

end WNear
