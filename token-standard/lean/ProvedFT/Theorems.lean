/-
  The five properties of near-contract-standards 5.29.0 FungibleToken + StorageManagement
  (plain-English statements in PROPERTIES.md, hashes of the statements in properties.json):

  * P1 conservation        `P1_conservation`, `P1_inv_step`
  * P2 settlement          `P2_settlement`, `P2_settlement_call`, `P2_settlement_never_fails`
  * P3 callback ownership  `P3_callback_private`, `P3_callback_private_sys`
  * P4 balance ownership   `P4_balance_ownership`, `P4_who_can_lower`, `P4_pending_origin`
  * P5 storage             `P5_unregister_force`, `P5_unregister_zero`,
                           `P5_unregister_refused`, `P5_unregister_unknown`,
                           `P5_storage_deposit`, `P5_storage_solvent`
-/
import ProvedFT.Lemmas

namespace ProvedFT

/-- The invariant of every reachable state: map without repeated keys, `total_supply` = sum
    of balances, supply fits u128, storage solvency (the contract's NEAR covers the base storage
    stake plus one storage refund `minBal` per registered account), and every settlement
    callback in flight is for a positive amount between two different accounts. -/
structure Inv (E : Env) (S : Sys) : Prop where
  pre : Pre S.c
  solvent : S.c.accts.length * E.minBal + E.base ≤ S.c.near
  cap : S.c.near ≤ E.cap
  pend : ∀ e ∈ S.pending, e.1 ≠ e.2.1 ∧ 0 < e.2.2

theorem exec_inv {E : Env} {s : St} (hs : Pre s)
    (hsol : s.accts.length * E.minBal + E.base ≤ s.near) {r : Rcpt} {o : Out}
    (h : exec E s r = some o) :
    Pre o.st ∧ o.st.accts.length * E.minBal + E.base ≤ o.st.near ∧ o.st.near ≤ E.cap := by
  obtain ⟨o0, hm, ha, hsu, _, _, _, hcap, hpaid, hn⟩ := exec_some h
  have hg := method_good E hs hm
  have hobl := hg.obl
  refine ⟨⟨by rw [ha]; exact hg.pre.nodup, by rw [ha, hsu]; exact hg.pre.cons,
    by rw [hsu]; exact hg.pre.bound⟩, ?_, ?_⟩
  · rw [ha, hn]; omega
  · rw [hn]; omega

/-- With the invariant, the runtime's checks (balance for the transfers, storage stake) never
    fail: `exec` succeeds exactly when the code does. -/
theorem exec_of_method {E : Env} (hE : E.Sane) {s : St} (hs : Pre s)
    (hsol : s.accts.length * E.minBal + E.base ≤ s.near) {r : Rcpt}
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

theorem pend_calls {E : Env} {s : St} {r : Rcpt} {o : Out} (h : exec E s r = some o) :
    ∀ e ∈ o.calls, e.1 ≠ e.2.1 ∧ 0 < e.2.2 := by
  obtain ⟨o0, hm, _, _, _, hc, _⟩ := exec_some h
  obtain ⟨p, d, m, rs⟩ := r
  rw [hc]
  rcases calls_origin hm with h0 | ⟨rc, x, _, _, _, h1, hne, hx, _⟩
  · simp [h0]
  · intro e he; rw [h1] at he; simp at he; subst he; exact ⟨hne, hx⟩

theorem pend_erase {l : List (Acct × Acct × Nat)} (h : ∀ e ∈ l, e.1 ≠ e.2.1 ∧ 0 < e.2.2)
    (i : Nat) : ∀ e ∈ l.eraseIdx i, e.1 ≠ e.2.1 ∧ 0 < e.2.2 :=
  fun e he => h e (List.mem_of_mem_eraseIdx he)

/-! ## P1 conservation -/

/-- **P1, one step.** Every step keeps the invariant: any call by anyone, any settlement
    callback with any promise result, a dropped callback, NEAR arriving. -/
theorem P1_inv_step (E : Env) {S : Sys} (hI : Inv E S) (st : Step) : Inv E (sysStep E S st) := by
  cases st with
  | call p d m rs =>
    simp only [sysStep]
    cases he : exec E S.c ⟨p, d, m, resultsFor E p rs⟩ with
    | none => exact hI
    | some o =>
      obtain ⟨h1, h2, h3⟩ := exec_inv hI.pre hI.solvent he
      refine ⟨h1, h2, h3, ?_⟩
      intro e he'
      rcases List.mem_append.mp he' with h | h
      · exact hI.pend e h
      · exact pend_calls he e h
  | resolve i res =>
    simp only [sysStep]
    cases hp : S.pending[i]? with
    | none => exact hI
    | some q =>
      obtain ⟨sn, rc, amt⟩ := q
      simp only
      cases he : exec E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ with
      | none => exact ⟨hI.pre, hI.solvent, hI.cap, pend_erase hI.pend i⟩
      | some o =>
        obtain ⟨h1, h2, h3⟩ := exec_inv hI.pre hI.solvent he
        refine ⟨h1, h2, h3, ?_⟩
        intro e he'
        rcases List.mem_append.mp he' with h | h
        · exact pend_erase hI.pend i e h
        · exact pend_calls he e h
  | resolveFails i => exact ⟨hI.pre, hI.solvent, hI.cap, pend_erase hI.pend i⟩
  | nearIn x =>
    simp only [sysStep]
    by_cases hx : S.c.near + x ≤ E.cap
    · rw [if_pos hx]
      exact ⟨⟨hI.pre.nodup, hI.pre.cons, hI.pre.bound⟩, by have := hI.solvent; simp only; omega,
        by simp only; omega, hI.pend⟩
    · rw [if_neg hx]; exact hI

theorem inv_reach {E : Env} {S : Sys} (h : Reach E S) : Inv E S := by
  induction h with
  | init s hs => exact ⟨hs.1, hs.2.1, hs.2.2, by simp⟩
  | step st _ ih => exact P1_inv_step E ih st

/-- **P1 conservation.** In every reachable state `total_supply` equals the sum of all
    balances. -/
theorem P1_conservation {E : Env} {S : Sys} (h : Reach E S) : S.c.supply = total S.c.accts :=
  (inv_reach h).pre.cons

/-! ## P2 transfer_call settlement -/

/-- **P2, the callback itself.** When the settlement callback of a transfer of `amt` from `sn`
    to `rc` runs with any promise result, the refund `f` taken from the receiver is at most the
    transferred amount, at most what the receiver holds at that moment, and at most the unused
    amount it reported. The receiver loses exactly `f`; nobody but the sender and the receiver is
    touched; no NEAR is sent and no new callback started. If the sender is still registered it
    gains exactly `f` (sender + receiver total and supply unchanged) and the call returns
    `amt - f`; if the sender has unregistered, `f` is burned from the supply and the call
    returns `amt`. -/
theorem P2_settlement_call (E : Env) (s : St) (sn rc : Acct) (amt : Nat) (res : PR) (o : Out)
    (hne : sn ≠ rc)
    (h : method E s ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o) :
    let f := refundOf s.accts rc amt res
    f ≤ amt ∧ f ≤ bal s.accts rc ∧ f ≤ unusedOf amt res ∧
    bal o.st.accts rc + f = bal s.accts rc ∧
    (∀ a, a ≠ sn → a ≠ rc → get o.st.accts a = get s.accts a) ∧
    o.transfers = [] ∧ o.calls = [] ∧
    ((∃ v, get s.accts sn = some v) →
      bal o.st.accts sn = bal s.accts sn + f ∧ o.st.supply = s.supply ∧ o.ret = .u128 (amt - f)) ∧
    (get s.accts sn = none →
      get o.st.accts sn = none ∧ o.st.supply + f = s.supply ∧ o.ret = .u128 amt) := by
  intro f
  obtain ⟨_, _, res', rest, l', sup', used, evs, hrs, hq, rfl⟩ := method_resolve_some h
  simp only [List.cons.injEq] at hrs
  obtain ⟨rfl, _⟩ := hrs
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
  rcases iResolve_cases hq with ⟨hf0, hl, hsu, hus, _⟩ | ⟨hf, sb, hg, ho, hl, hsu, hus, _⟩ |
      ⟨hf, hg, ho, hl, hsu, hus, _⟩
  · subst hl hsu
    have hf0' : f = 0 := hf0
    refine ⟨by omega, fun a _ _ => rfl, fun _ => ⟨by omega, rfl, by omega⟩,
      fun hn => ⟨hn, by omega, hus⟩⟩
  · subst hl hsu
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
  · subst hl hsu
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
    · rw [if_pos hu, if_pos hbr]
      simp only
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
    · rw [if_pos hu, if_neg hbr]; exact ⟨_, rfl⟩
  · rw [if_neg hu]; exact ⟨_, rfl⟩

/-- **P2, the refund cannot be blocked.** In every state satisfying the invariant the
    settlement callback succeeds for any promise result (no overflow or underflow is possible);
    only running out of gas can stop it, which `Step.resolveFails` covers. -/
theorem P2_settlement_never_fails (E : Env) (hE : E.Sane) (S : Sys) (hI : Inv E S)
    (sn rc : Acct) (amt : Nat) (res : PR) :
    ∃ o, exec E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o := by
  obtain ⟨⟨l', sup', used, evs⟩, hq⟩ := iResolve_total (l := S.c.accts) sn rc amt res
    hI.pre.cons hI.pre.bound
  have hm : method E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ =
      some ⟨⟨l', sup', S.c.near⟩, [], [], evs, .u128 used⟩ := by
    simp [method, hq]
  exact ⟨_, exec_of_method hE hI.pre hI.solvent (by have := hI.cap; simp only; omega) hm⟩

/-- **P2 transfer_call settlement.** In every reachable state, when the settlement callback of
    the `i`-th transfer in flight (`amt` from `sn` to `rc`) runs with any promise result, the
    refund `f` is at most `amt` and at most the receiver's balance at that moment; the receiver
    loses exactly `f`; no other account but the sender changes; the callback leaves the list of
    callbacks in flight and sends no NEAR. If the sender is registered, the sender gains exactly
    `f`, so the sender + receiver total is conserved and the supply is unchanged; if the sender
    has unregistered, `f` is burned (the supply drops by `f`). -/
theorem P2_settlement (E : Env) (hE : E.Sane) (S : Sys) (hR : Reach E S) (i : Nat)
    (sn rc : Acct) (amt : Nat) (res : PR) (hp : S.pending[i]? = some (sn, rc, amt)) :
    let S' := sysStep E S (.resolve i res)
    let f := refundOf S.c.accts rc amt res
    f ≤ amt ∧ f ≤ bal S.c.accts rc ∧ bal S'.c.accts rc + f = bal S.c.accts rc ∧
    (∀ a, a ≠ sn → a ≠ rc → get S'.c.accts a = get S.c.accts a) ∧
    S'.pending = S.pending.eraseIdx i ∧ S'.paid = S.paid ∧
    ((∃ v, get S.c.accts sn = some v) →
      bal S'.c.accts sn + bal S'.c.accts rc = bal S.c.accts sn + bal S.c.accts rc ∧
      bal S'.c.accts sn = bal S.c.accts sn + f ∧ S'.c.supply = S.c.supply) ∧
    (get S.c.accts sn = none →
      get S'.c.accts sn = none ∧ S'.c.supply + f = S.c.supply) := by
  intro S' f
  have hI := inv_reach hR
  have hmem : (sn, rc, amt) ∈ S.pending := List.mem_of_getElem? hp
  have hne : sn ≠ rc := (hI.pend _ hmem).1
  obtain ⟨o, he⟩ := P2_settlement_never_fails E hE S hI sn rc amt res
  obtain ⟨o0, hm, ha, hsu, htr, hca, _⟩ := exec_some he
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8, h9⟩ := P2_settlement_call E S.c sn rc amt res o0 hne hm
  have hS' : S' = ⟨o.st, S.pending.eraseIdx i ++ o.calls, S.paid ++ o.transfers⟩ := by
    simp only [S', sysStep, hp, he]
  rw [hS']
  simp only
  rw [ha, hsu, hca, htr, h6, h7, List.append_nil, List.append_nil]
  refine ⟨h1, h2, h4, h5, rfl, rfl, fun hv => ?_, fun hn => ⟨(h9 hn).1, (h9 hn).2.1⟩⟩
  obtain ⟨a, b, _⟩ := h8 hv
  exact ⟨by omega, a, b⟩

/-! ## P3 callback ownership -/

/-- **P3, the method.** Called with any predecessor other than the token contract itself,
    `ft_resolve_transfer` fails (`#[private]`), whatever the arguments, the deposit or the
    promise results. -/
theorem P3_callback_private (E : Env) (s : St) (p : Acct) (hp : p ≠ E.self) (d : Nat)
    (sn rc : Acct) (amt : Nat) (rs : List PR) :
    method E s ⟨p, d, .ft_resolve_transfer sn rc amt, rs⟩ = none := by
  simp [method, hp]

/-- **P3 callback ownership.** No receipt other than the token's own settlement callback can
    make `ft_resolve_transfer` take effect: a call of it by any account — a user, another
    contract, another contract's `promise_then` callback with promise results of its choice, or
    a transaction signed with the token account's own key — changes nothing at all. -/
theorem P3_callback_private_sys (E : Env) (S : Sys) (p : Acct) (d : Nat) (sn rc : Acct)
    (amt : Nat) (rs : List PR) :
    sysStep E S (.call p d (.ft_resolve_transfer sn rc amt) rs) = S := by
  simp only [sysStep]
  by_cases hp : p = E.self
  · have hm : method E S.c ⟨p, d, .ft_resolve_transfer sn rc amt, resultsFor E p rs⟩ = none := by
      simp [method, resultsFor, hp]
    unfold exec; rw [hm]
  · have hm := P3_callback_private E S.c p hp d sn rc amt (resultsFor E p rs)
    unfold exec; rw [hm]

/-! ## P4 balance ownership -/

/-- A call by `p ≠ u` never lowers `u`'s balance, except a resolve call, which only the
    contract's callback can make. -/
theorem method_no_lower {E : Env} {s : St} {p : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (u : Acct) (hpu : p ≠ u) (hres : ∀ sn rc amt, m = .ft_resolve_transfer sn rc amt → False)
    (h : method E s ⟨p, d, m, rs⟩ = some o) : bal s.accts u ≤ bal o.st.accts u := by
  cases m with
  | reinit => simp [method] at h
  | bad => simp [method] at h
  | ft_total_supply | ft_balance_of _ | storage_balance_bounds | storage_balance_of _ =>
    simp only [method, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | ft_transfer rc x memo | ft_transfer_call rc x memo _ =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
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
  | ft_resolve_transfer sn rc amt => exact absurd (hres sn rc amt rfl) id
  | storage_deposit acc ro =>
    simp only [method] at h
    cases hg : get s.accts (acc.getD p) with
    | some w => simp only [hg, Option.some.injEq] at h; subst h; exact Nat.le_refl _
    | none =>
      simp only [hg] at h
      by_cases hm : d < E.minBal
      · simp [hm] at h
      · simp only [hm, ite_false, Option.some.injEq] at h; subst h
        simp only
        by_cases hau : acc.getD p = u
        · rw [← hau, bal_set_self, bal_of_none hg]; exact Nat.le_refl _
        · rw [bal_set_ne _ _ hau]; exact Nat.le_refl _
  | storage_withdraw amt =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
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
          · simp only [ha, ite_false, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | storage_unregister f =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
      cases hg : get s.accts p with
      | none => simp only [hg, Option.some.injEq] at h; subst h; exact Nat.le_refl _
      | some b =>
        simp only [hg] at h
        by_cases hc : b = 0 ∨ f = some true
        · simp only [hc, ite_true] at h
          by_cases hc2 : b ≤ s.supply
          · simp only [hc2, ite_true, Option.some.injEq] at h; subst h
            simp only; rw [bal_erase_ne _ hpu]; exact Nat.le_refl _
          · simp only [hc2, ite_false] at h; exact absurd h (by simp)
        · simp [hc] at h

/-- In a settlement callback, an account that is not the receiver never loses; the receiver
    loses at most the transferred amount. -/
theorem resolve_lower {s : St} {sn rc : Acct} {amt : Nat} {res : PR} {l' : Accts}
    {sup' used : Nat} {evs : List Ev}
    (hq : iResolve s.accts s.supply sn rc amt res = some (l', sup', used, evs))
    (u : Acct) : (u ≠ rc → bal s.accts u ≤ bal l' u) ∧ bal s.accts u ≤ bal l' u + amt := by
  have hfa := refundOf_le_amt s.accts rc amt res
  have hfb := refundOf_le_bal s.accts rc amt res
  rcases iResolve_cases hq with ⟨_, rfl, _, _, _⟩ | ⟨_, sb, hg, _, rfl, _, _, _⟩ |
      ⟨_, _, _, rfl, _, _, _⟩
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

/-- **P4 balance ownership.** A step that is not a call by `u` never lowers `u`'s balance, with
    one exception: the token's own settlement callback of a transfer some `sn` made *to* `u` with
    `ft_transfer_call`, which takes back at most the amount of that transfer. (`u`'s own calls
    are listed in `P4_who_can_lower`; `P4_pending_origin` says where the amount comes from.) -/
theorem P4_balance_ownership (E : Env) (S : Sys) (u : Acct) (st : Step)
    (hst : ∀ d m rs, st ≠ .call u d m rs) :
    bal S.c.accts u ≤ bal (sysStep E S st).c.accts u ∨
    ∃ i res sn amt, st = .resolve i res ∧ S.pending[i]? = some (sn, u, amt) ∧
      bal S.c.accts u ≤ bal (sysStep E S st).c.accts u + amt := by
  cases st with
  | call p d m rs =>
    left
    have hpu : p ≠ u := fun h => hst d m rs (by rw [h])
    simp only [sysStep]
    cases he : exec E S.c ⟨p, d, m, resultsFor E p rs⟩ with
    | none => exact Nat.le_refl _
    | some o =>
      obtain ⟨o0, hm, ha, _⟩ := exec_some he
      simp only; rw [ha]
      refine method_no_lower u hpu ?_ hm
      intro sn rc amt hmr
      subst hmr
      obtain ⟨hps, _, _, _, _, _, _, _, hrs, _⟩ := method_resolve_some hm
      simp [resultsFor, hps] at hrs
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
          obtain ⟨_, _, res', rest, l', sup', used, evs, hrs, hq, rfl⟩ := method_resolve_some hm
          simp only; rw [ha]
          exact resolve_lower hq u
      by_cases hur : u = rc
      · subst hur; exact Or.inr ⟨i, res, sn, amt, rfl, hpi, key.2⟩
      · exact Or.inl (key.1 hur)
  | resolveFails i => left; exact Nat.le_refl _
  | nearIn x =>
    left; simp only [sysStep]
    by_cases hx : S.c.near + x ≤ E.cap
    · rw [if_pos hx]; exact Nat.le_refl _
    · rw [if_neg hx]; exact Nat.le_refl _

/-- A call by `u` itself lowers `u`'s balance only through these three methods. -/
theorem method_self_lower {E : Env} {s : St} {u : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (hres : ∀ sn rc amt, m = .ft_resolve_transfer sn rc amt → False)
    (h : method E s ⟨u, d, m, rs⟩ = some o)
    (hlt : bal o.st.accts u < bal s.accts u) :
    (∃ rc x memo, m = .ft_transfer rc x memo) ∨ (∃ rc x memo msg, m = .ft_transfer_call rc x memo msg) ∨
    m = .storage_unregister (some true) := by
  cases m with
  | ft_transfer rc x memo => exact Or.inl ⟨rc, x, memo, rfl⟩
  | ft_transfer_call rc x memo msg => exact Or.inr (Or.inl ⟨rc, x, memo, msg, rfl⟩)
  | reinit => simp [method] at h
  | bad => simp [method] at h
  | ft_total_supply | ft_balance_of _ | storage_balance_bounds | storage_balance_of _ =>
    simp only [method, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
  | ft_resolve_transfer sn rc amt => exact absurd (hres sn rc amt rfl) id
  | storage_deposit acc ro =>
    exfalso
    simp only [method] at h
    cases hg : get s.accts (acc.getD u) with
    | some w => simp only [hg, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
    | none =>
      simp only [hg] at h
      by_cases hm : d < E.minBal
      · simp [hm] at h
      · simp only [hm, ite_false, Option.some.injEq] at h; subst h
        simp only at hlt
        by_cases hau : acc.getD u = u
        · rw [hau] at hg; rw [bal_of_none hg] at hlt; omega
        · rw [bal_set_ne _ _ hau] at hlt; omega
  | storage_withdraw amt =>
    exfalso
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
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
          · simp only [ha, ite_false, Option.some.injEq] at h; subst h
            exact absurd hlt (Nat.lt_irrefl _)
  | storage_unregister f =>
    cases f with
    | some fb =>
      cases fb with
      | true => exact Or.inr (Or.inr rfl)
      | false =>
        exfalso
        simp only [method] at h
        by_cases hd : d ≠ 1
        · simp [hd] at h
        · simp only [hd, ite_false] at h
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
      · simp only [hd, ite_false] at h
        cases hg : get s.accts u with
        | none => simp only [hg, Option.some.injEq] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
        | some b =>
          simp only [hg] at h
          by_cases hb0 : b = 0
          · rw [bal_of_some hg, hb0] at hlt; omega
          · simp [hb0] at h

/-- **P4, exact list.** If a step lowers `u`'s balance, it is one of: `u`'s own `ft_transfer`,
    `ft_transfer_call` or `storage_unregister(force = true)`, or the token's settlement callback
    of an `ft_transfer_call` whose receiver is `u`. -/
theorem P4_who_can_lower (E : Env) (S : Sys) (u : Acct) (st : Step)
    (hlt : bal (sysStep E S st).c.accts u < bal S.c.accts u) :
    (∃ d rc x memo rs, st = .call u d (.ft_transfer rc x memo) rs) ∨
    (∃ d rc x memo msg rs, st = .call u d (.ft_transfer_call rc x memo msg) rs) ∨
    (∃ d rs, st = .call u d (.storage_unregister (some true)) rs) ∨
    (∃ i res sn amt, st = .resolve i res ∧ S.pending[i]? = some (sn, u, amt)) := by
  by_cases hcall : ∃ d m rs, st = .call u d m rs
  · obtain ⟨d, m, rs, rfl⟩ := hcall
    simp only [sysStep] at hlt
    cases he : exec E S.c ⟨u, d, m, resultsFor E u rs⟩ with
    | none => rw [he] at hlt; simp only at hlt; omega
    | some o =>
      rw [he] at hlt
      obtain ⟨o0, hm, ha, _⟩ := exec_some he
      simp only at hlt; rw [ha] at hlt
      have hres : ∀ sn rc amt, m = .ft_resolve_transfer sn rc amt → False := by
        intro sn rc amt hmr
        subst hmr
        obtain ⟨hps, _, _, _, _, _, _, _, hrs, _⟩ := method_resolve_some hm
        simp [resultsFor, hps] at hrs
      rcases method_self_lower hres hm hlt with ⟨rc, x, memo, rfl⟩ | ⟨rc, x, memo, msg, rfl⟩ | rfl
      · exact Or.inl ⟨d, rc, x, memo, rs, rfl⟩
      · exact Or.inr (Or.inl ⟨d, rc, x, memo, msg, rs, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨d, rs, rfl⟩))
  · have hst : ∀ d m rs, st ≠ .call u d m rs := fun d m rs h => hcall ⟨d, m, rs, h⟩
    rcases P4_balance_ownership E S u st hst with h | ⟨i, res, sn, amt, h1, h2, _⟩
    · omega
    · exact Or.inr (Or.inr (Or.inr ⟨i, res, sn, amt, h1, h2⟩))

/-- **P4, where a callback in flight comes from.** Only a successful `ft_transfer_call` starts
    one, and the entry `(sender, receiver, amount)` it starts is exactly the transfer it made:
    sender ≠ receiver, a positive amount, the receiver was credited `amount` and the sender
    debited `amount`. Every callback runs at most once (`P2_settlement`: it leaves the list). -/
theorem P4_pending_origin (E : Env) (S : Sys) (st : Step) (e : Acct × Acct × Nat)
    (he : e ∈ (sysStep E S st).pending) (hnew : e ∉ S.pending) :
    ∃ p d rc x memo msg rs, st = .call p d (.ft_transfer_call rc x memo msg) rs ∧
      e = (p, rc, x) ∧ p ≠ rc ∧ 0 < x ∧
      bal (sysStep E S st).c.accts rc = bal S.c.accts rc + x ∧
      bal (sysStep E S st).c.accts p + x = bal S.c.accts p := by
  cases st with
  | call p d m rs =>
    simp only [sysStep] at he ⊢
    cases hx : exec E S.c ⟨p, d, m, resultsFor E p rs⟩ with
    | none => rw [hx] at he; exact absurd he hnew
    | some o =>
      rw [hx] at he
      simp only at he ⊢
      obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some hx
      rcases List.mem_append.mp he with h | h
      · exact absurd h hnew
      · rw [hc] at h
        rcases calls_origin hm with h0 | ⟨rc, x, memo, msg, rfl, h1, hne, hxp, hb1, hb2⟩
        · rw [h0] at h; simp at h
        · rw [h1] at h; simp at h; subst h
          rw [ha]
          exact ⟨p, d, rc, x, memo, msg, rs, rfl, rfl, hne, hxp, hb1, hb2⟩
  | resolve i res =>
    exfalso
    simp only [sysStep] at he
    cases hp : S.pending[i]? with
    | none => rw [hp] at he; exact hnew he
    | some q =>
      obtain ⟨sn, rc, amt⟩ := q
      rw [hp] at he
      simp only at he
      cases hx : exec E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ with
      | none => rw [hx] at he; exact hnew (List.mem_of_mem_eraseIdx he)
      | some o =>
        rw [hx] at he
        obtain ⟨o0, hm, _, _, _, hc, _⟩ := exec_some hx
        obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := method_resolve_some hm
        simp only at hc
        rcases List.mem_append.mp he with h | h
        · exact hnew (List.mem_of_mem_eraseIdx h)
        · rw [hc] at h; simp at h
  | resolveFails i => exact absurd (List.mem_of_mem_eraseIdx he) hnew
  | nearIn x =>
    exfalso
    simp only [sysStep] at he
    by_cases hx : S.c.near + x ≤ E.cap
    · rw [if_pos hx] at he; exact hnew he
    · rw [if_neg hx] at he; exact hnew he

/-! ## P5 storage -/

/-- **P5 storage solvency.** In every reachable state the contract's NEAR covers the base
    storage stake plus one storage refund `minBal` per registered account, so it can always
    pay every unregister refund, and the actual storage stake of the account entries is
    covered too. -/
theorem P5_storage_solvent (E : Env) (hE : E.Sane) {S : Sys} (h : Reach E S) :
    S.c.accts.length * E.minBal + E.base ≤ S.c.near ∧
    E.base + stor E.entry S.c.accts ≤ S.c.near := by
  have hI := inv_reach h
  have := stor_le E.entry E.minBal hE.entry_le S.c.accts
  have := hI.solvent
  exact ⟨hI.solvent, by omega⟩

/-- **P5, forced unregister.** `storage_unregister(force = true)` with 1 yoctoNEAR by a
    registered `u` holding `b` succeeds in every reachable state: `u` is removed, its balance
    `b` is burned (total_supply drops by exactly `b`), and the contract sends `u` the storage
    deposit plus the attached 1 yoctoNEAR (`minBal + 1`). -/
theorem P5_unregister_force (E : Env) (hE : E.Sane) (S : Sys) (hR : Reach E S) (u : Acct)
    (hcap : S.c.near < E.cap) (b : Nat) (hb : get S.c.accts u = some b) (rs : List PR) :
    let S' := sysStep E S (.call u 1 (.storage_unregister (some true)) rs)
    S'.c.accts = erase S.c.accts u ∧ S'.c.supply = S.c.supply - b ∧ total S'.c.accts + b = total S.c.accts ∧
      S'.c.near = S.c.near - E.minBal ∧ S'.pending = S.pending ∧
      S'.paid = S.paid ++ [(u, E.minBal + 1)] := by
  have hI := inv_reach hR
  have hbs : b ≤ S.c.supply := by rw [hI.pre.cons]; exact get_le_total hb
  have hm : method E S.c ⟨u, 1, .storage_unregister (some true), resultsFor E u rs⟩ =
      some ⟨⟨erase S.c.accts u, S.c.supply - b, S.c.near⟩, [(u, E.minBal + 1)], [], [], .bool true⟩ := by
    simp [method, hb, hbs, satAdd_eq hE.min_lt]
  have he := exec_of_method hE hI.pre hI.solvent (by simp only; omega) hm
  have hl := length_pos_of_get hb
  have hlm : E.minBal ≤ S.c.accts.length * E.minBal := by
    obtain ⟨k, hk⟩ : ∃ k, S.c.accts.length = k + 1 := ⟨S.c.accts.length - 1, by omega⟩
    rw [hk, Nat.add_mul, Nat.one_mul]; omega
  have hsol := hI.solvent
  have htot := total_erase S.c.accts u
  rw [bal_of_some hb] at htot
  simp only [sysStep, he, sumT_one, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | exact htot | omega

/-- **P5, unregister with zero balance.** `storage_unregister` with 1 yoctoNEAR by a registered
    `u` whose balance is 0 succeeds with or without `force`: `u` is removed, the supply is
    unchanged, and the contract sends `u` `minBal + 1`. -/
theorem P5_unregister_zero (E : Env) (hE : E.Sane) (S : Sys) (hR : Reach E S) (u : Acct)
    (hcap : S.c.near < E.cap) (hb : get S.c.accts u = some 0) (force : Option Bool)
    (rs : List PR) :
    let S' := sysStep E S (.call u 1 (.storage_unregister force) rs)
    S'.c.accts = erase S.c.accts u ∧ S'.c.supply = S.c.supply ∧
      S'.c.near = S.c.near - E.minBal ∧ S'.pending = S.pending ∧
      S'.paid = S.paid ++ [(u, E.minBal + 1)] := by
  have hI := inv_reach hR
  have hm : method E S.c ⟨u, 1, .storage_unregister force, resultsFor E u rs⟩ =
      some ⟨⟨erase S.c.accts u, S.c.supply - 0, S.c.near⟩, [(u, E.minBal + 1)], [], [], .bool true⟩ := by
    simp [method, hb, satAdd_eq hE.min_lt]
  have he := exec_of_method hE hI.pre hI.solvent (by simp only; omega) hm
  have hl := length_pos_of_get hb
  have hlm : E.minBal ≤ S.c.accts.length * E.minBal := by
    obtain ⟨k, hk⟩ : ∃ k, S.c.accts.length = k + 1 := ⟨S.c.accts.length - 1, by omega⟩
    rw [hk, Nat.add_mul, Nat.one_mul]; omega
  have hsol := hI.solvent
  simp only [sysStep, he, sumT_one, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | omega

/-- **P5, unregister refused.** Without `force = true`, `storage_unregister` by an account with
    a positive balance fails: nothing changes (the balance, the supply, the registration, the
    NEAR). -/
theorem P5_unregister_refused (E : Env) (S : Sys) (u : Acct) (d : Nat) (b : Nat)
    (hb : get S.c.accts u = some b) (hpos : 0 < b) (force : Option Bool)
    (hf : force ≠ some true) (rs : List PR) :
    sysStep E S (.call u d (.storage_unregister force) rs) = S := by
  have hm : method E S.c ⟨u, d, .storage_unregister force, resultsFor E u rs⟩ = none := by
    have hb0 : b ≠ 0 := by omega
    by_cases hd : d ≠ 1
    · simp [method, hd]
    · simp [method, hd, hb, hb0, hf]
  simp only [sysStep]
  unfold exec; rw [hm]

/-- **P5, unregister of an unknown account.** `storage_unregister` with 1 yoctoNEAR by an
    account that is not registered succeeds, returns `false`, changes no balance and not the
    supply, and sends nothing; the contract keeps the 1 yoctoNEAR. -/
theorem P5_unregister_unknown (E : Env) (hE : E.Sane) (S : Sys) (hR : Reach E S) (u : Acct)
    (hcap : S.c.near < E.cap) (hb : get S.c.accts u = none) (force : Option Bool) (rs : List PR) :
    let S' := sysStep E S (.call u 1 (.storage_unregister force) rs)
    S'.c.accts = S.c.accts ∧ S'.c.supply = S.c.supply ∧ S'.c.near = S.c.near + 1 ∧
      S'.pending = S.pending ∧ S'.paid = S.paid ∧
      (method E S.c ⟨u, 1, .storage_unregister force, rs⟩).map Out.ret = some (.bool false) := by
  have hI := inv_reach hR
  have hm : method E S.c ⟨u, 1, .storage_unregister force, resultsFor E u rs⟩ =
      some ⟨S.c, [], [], [], .bool false⟩ := by
    simp [method, hb]
  have hr : (method E S.c ⟨u, 1, .storage_unregister force, rs⟩).map Out.ret = some (.bool false) := by
    simp [method, hb]
  have he := exec_of_method hE hI.pre hI.solvent (by simp only; omega) hm
  simp only [sysStep, he, sumT_nil, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, hr⟩ <;> first | trivial | omega

/-- **P5, registration.** `storage_deposit` for an unregistered account `a` (the caller or
    another account) with a deposit `d ≥ minBal` registers `a` with balance 0, keeps exactly
    `minBal`, refunds the rest `d - minBal` to the caller, and changes no balance and not the
    supply. Below `minBal` it fails. -/
theorem P5_storage_deposit (E : Env) (hE : E.Sane) (S : Sys) (hR : Reach E S) (p a : Acct)
    (d : Nat) (hd : S.c.near + d ≤ E.cap) (ha : get S.c.accts a = none) (ro : Option Bool)
    (rs : List PR) :
    let S' := sysStep E S (.call p d (.storage_deposit (some a) ro) rs)
    (d < E.minBal → S' = S) ∧
    (E.minBal ≤ d → S'.c.accts = set S.c.accts a 0 ∧ S'.c.supply = S.c.supply ∧
      S'.c.near = S.c.near + E.minBal ∧
      S'.paid = S.paid ++ (if 0 < d - E.minBal then [(p, d - E.minBal)] else [])) := by
  have hI := inv_reach hR
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hm : method E S.c ⟨p, d, .storage_deposit (some a) ro, resultsFor E p rs⟩ = none := by
      simp [method, ha, hlt]
    simp only [sysStep]; unfold exec; rw [hm]
  · have hnlt : ¬ d < E.minBal := by omega
    have hm : method E S.c ⟨p, d, .storage_deposit (some a) ro, resultsFor E p rs⟩ =
        some ⟨⟨set S.c.accts a 0, S.c.supply, S.c.near⟩,
          (if 0 < d - E.minBal then [(p, d - E.minBal)] else []), [], [],
          .storageBalance E.minBal 0⟩ := by
      simp [method, ha, hnlt]
    have he := exec_of_method hE hI.pre hI.solvent hd hm
    simp only [sysStep, he, List.append_nil]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try trivial)
    by_cases hp : 0 < d - E.minBal
    · simp only [hp, ite_true, sumT_one]; omega
    · simp only [hp, ite_false, sumT_nil]; omega

end ProvedFT
