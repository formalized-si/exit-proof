/-
  Contract invariant `CInv` and the relation `Rel` that every internal step
  (ping, deposit, withdraw, stake, unstake) establishes between the state before
  and after it.
-/
import StakingPool.Spec

namespace StakingPool

/-- Contract-level invariant (holds in every reachable state, see `Reach.inv`). -/
structure CInv (c : Contract) : Prop where
  wf : c.accts.WF
  /-- the contract always holds some "orphan" shares nobody owns (from `new`) -/
  sh : c.sumSh < c.ts
  /-- share price is at least 1 -/
  price : c.ts ≤ c.s
  fee : 0 < c.fee.den ∧ c.fee.num ≤ c.fee.den

/-! ## Arithmetic -/

theorem mul_div_le_of_le {a b x : Nat} (hb : 0 < b) (hab : a ≤ b) : a * x / b ≤ x := by
  calc a * x / b ≤ b * x / b := Nat.div_le_div_right (Nat.mul_le_mul_right x hab)
    _ = x := Nat.mul_div_cancel_left x hb

theorem le_of_mul_le_mul_r {a b c : Nat} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  Nat.le_of_mul_le_mul_right h hc

/-- price comparison is transitive through a state with positive share count -/
theorem price_trans {s1 t1 s2 t2 s3 t3 : Nat} (h12 : s1 * t2 ≤ s2 * t1) (h23 : s2 * t3 ≤ s3 * t2)
    (ht2 : 0 < t2) : s1 * t3 ≤ s3 * t1 := by
  have h1 : s1 * t3 * t2 ≤ s3 * t1 * t2 := by
    calc s1 * t3 * t2 = (s1 * t2) * t3 := by rw [Nat.mul_assoc, Nat.mul_comm t3, ← Nat.mul_assoc]
      _ ≤ (s2 * t1) * t3 := Nat.mul_le_mul_right _ h12
      _ = (s2 * t3) * t1 := by rw [Nat.mul_assoc, Nat.mul_comm t1, ← Nat.mul_assoc]
      _ ≤ (s3 * t2) * t1 := Nat.mul_le_mul_right _ h23
      _ = s3 * t1 * t2 := by rw [Nat.mul_assoc, Nat.mul_comm t2, ← Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right h1 ht2

/-- A staked value rounded down never decreases when the price does not decrease and the
share count does not decrease. -/
theorem value_mono {s t s' t' sh sh' : Nat} (hp : s * t' ≤ s' * t) (ht : 0 < t) (ht' : 0 < t')
    (hsh : sh ≤ sh') : s * sh / t ≤ s' * sh' / t' := by
  apply (Nat.le_div_iff_mul_le ht').2
  have hq : s * sh / t * t ≤ s * sh := Nat.div_mul_le_self _ _
  have h1 : s * sh / t * t' * t ≤ s' * sh' * t := by
    calc s * sh / t * t' * t = (s * sh / t * t) * t' := by
            rw [Nat.mul_assoc, Nat.mul_comm t', ← Nat.mul_assoc]
      _ ≤ (s * sh) * t' := Nat.mul_le_mul_right _ hq
      _ = (s * t') * sh := by rw [Nat.mul_assoc, Nat.mul_comm sh, ← Nat.mul_assoc]
      _ ≤ (s' * t) * sh := Nat.mul_le_mul_right _ hp
      _ = (s' * sh) * t := by rw [Nat.mul_assoc, Nat.mul_comm t, ← Nat.mul_assoc]
      _ ≤ s' * sh' * t := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsh)
  exact Nat.le_of_mul_le_mul_right h1 ht

/-! ## Saving one account -/

theorem save_meas {c : Contract} (hwf : c.accts.WF) (id : AccountId) (a : Account) :
    (c.save id a).accts.WF ∧
    (c.save id a).sumU + (c.get id).unstaked = c.sumU + a.unstaked ∧
    (c.save id a).sumSh + (c.get id).stakeShares = c.sumSh + a.stakeShares ∧
    (∀ t, (c.save id a).cool t + gCool t (c.get id) = c.cool t + gCool t a) :=
  ⟨hwf.save id a, Accts.sum_save hwf id a measure_gU, Accts.sum_save hwf id a measure_gSh,
    fun t => Accts.sum_save hwf id a (measure_gCool t)⟩

theorem norm_avail_le (a : Account) : a.norm.availEpoch ≤ a.availEpoch := by
  rcases norm_cases a with h | ⟨h, _, _⟩ <;> simp [h, Account.zero]

theorem gCool_norm (t : Nat) (a : Account) : gCool t a.norm = gCool t a := ((measure_gCool t) a).1

theorem norm_of_shares_pos {a : Account} (h : 0 < a.stakeShares) : a.norm = a := by
  unfold Account.norm; split
  · omega
  · rfl

/-! ## Projections of updated states -/

@[simp] theorem save_s (c : Contract) (id : AccountId) (a : Account) : (c.save id a).s = c.s := rfl
@[simp] theorem save_ts (c : Contract) (id : AccountId) (a : Account) : (c.save id a).ts = c.ts := rfl
@[simp] theorem save_ltb (c : Contract) (id : AccountId) (a : Account) : (c.save id a).ltb = c.ltb := rfl
@[simp] theorem save_owner (c : Contract) (id : AccountId) (a : Account) : (c.save id a).owner = c.owner := rfl
@[simp] theorem save_key (c : Contract) (id : AccountId) (a : Account) : (c.save id a).key = c.key := rfl
@[simp] theorem save_fee (c : Contract) (id : AccountId) (a : Account) : (c.save id a).fee = c.fee := rfl
@[simp] theorem save_paused (c : Contract) (id : AccountId) (a : Account) : (c.save id a).paused = c.paused := rfl
@[simp] theorem save_lastEpoch (c : Contract) (id : AccountId) (a : Account) :
    (c.save id a).lastEpoch = c.lastEpoch := rfl

/-! ## The step relation -/

/-- What one internal step establishes between the states before (`c`) and after (`c'`)
it, at env `e`, consuming `r` units of the 10^12 yocto price-guarantee fund. -/
structure RelC (e : Env) (c c' : Contract) (r : Nat) : Prop where
  inv : CInv c'
  fund : c'.s + c'.sumU + c.ltb ≤ c.s + c.sumU + c'.ltb + r
  avail : ∀ id, (c'.get id).availEpoch ≤ max (c.get id).availEpoch (e.epoch + NUM_EPOCHS_TO_UNLOCK)
  mono : ∀ t, e.epoch ≤ t → t ≤ e.epoch + 3 → c.s + c.cool t ≤ c'.s + c'.cool t
  price : c.s * c'.ts ≤ c'.s * c.ts
  frame : ∀ u, u ≠ e.pred →
    (c'.get u).unstaked = (c.get u).unstaked ∧ (c'.get u).availEpoch = (c.get u).availEpoch ∧
    (c.get u).stakeShares ≤ (c'.get u).stakeShares ∧
    (u ≠ c.owner → (c'.get u).stakeShares = (c.get u).stakeShares)
  owner : c'.owner = c.owner

def Rel (e : Env) (c c' : Contract) (r : Nat) : Prop := CInv c → RelC e c c' r

/-- the fee, key and paused flag are untouched -/
def KFP (c c' : Contract) : Prop := c'.fee = c.fee ∧ c'.key = c.key ∧ c'.paused = c.paused

theorem Rel.refl (e : Env) (c : Contract) : Rel e c c 0 := fun hc =>
  { inv := hc
    fund := by omega
    avail := fun id => Nat.le_max_left _ _
    mono := fun _ _ _ => Nat.le_refl _
    price := Nat.le_refl _
    frame := fun _ _ => ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
    owner := rfl }

theorem Rel.trans {e : Env} {c1 c2 c3 : Contract} {r1 r2 : Nat} (h1 : Rel e c1 c2 r1)
    (h2 : Rel e c2 c3 r2) : Rel e c1 c3 (r1 + r2) := fun hc =>
  let a := h1 hc
  let b := h2 a.inv
  { inv := b.inv
    fund := by have := a.fund; have := b.fund; omega
    avail := fun id => by
      have a1 := a.avail id; have a2 := b.avail id
      simp only [Nat.max_def] at *; split at a2 <;> split at a1 <;> split <;> omega
    mono := fun t ht1 ht2 => Nat.le_trans (a.mono t ht1 ht2) (b.mono t ht1 ht2)
    price := price_trans a.price b.price (Nat.lt_of_le_of_lt (Nat.zero_le _) a.inv.sh)
    frame := fun u hu => by
      obtain ⟨a1, b1, c1', d1⟩ := a.frame u hu
      obtain ⟨a2, b2, c2', d2⟩ := b.frame u hu
      refine ⟨a2.trans a1, b2.trans b1, Nat.le_trans c1' c2', fun ho => ?_⟩
      have ho2 : u ≠ c2.owner := by rw [a.owner]; exact ho
      rw [d2 ho2, d1 ho]
    owner := b.owner.trans a.owner }

/-! ## Pieces -/

theorem gCool_le (t : Nat) (a : Account) : gCool t a ≤ a.unstaked := by
  unfold gCool; split <;> omega

theorem sh_le_sum {c : Contract} (hwf : c.accts.WF) (id : AccountId) :
    (c.get id).stakeShares ≤ c.sumSh := Accts.le_sum hwf id (g := gSh) rfl

theorem u_le_sum {c : Contract} (hwf : c.accts.WF) (id : AccountId) :
    (c.get id).unstaked ≤ c.sumU := Accts.le_sum hwf id (g := gU) rfl

/-- Everything the invariants need to know about a state whose map is the old map with
one account overwritten by `⟨u, sh, av⟩`. -/
theorem save_facts {c c' : Contract} (hwf : c.accts.WF) {id : AccountId} {u sh av : Nat}
    (h : c'.accts = c.accts.save id ⟨u, sh, av⟩) :
    c'.accts.WF ∧ c'.sumU + (c.get id).unstaked = c.sumU + u ∧
    c'.sumSh + (c.get id).stakeShares = c.sumSh + sh ∧
    (∀ t, c'.cool t + gCool t (c.get id) = c.cool t + (if t < av then u else 0)) ∧
    (∀ k, k ≠ id → c'.get k = c.get k) ∧ (c'.get id).unstaked = u ∧ (c'.get id).stakeShares = sh ∧
    (c'.get id).availEpoch ≤ av ∧ ((0 < u ∨ 0 < sh) → (c'.get id).availEpoch = av) := by
  have hget : ∀ k, c'.get k = if k = id then (Account.mk u sh av).norm else c.get k := by
    intro k; show c'.accts.get k = _; rw [h]; rfl
  refine ⟨by rw [h]; exact hwf.save _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c'.accts.sum gU + _ = _; rw [h]; exact Accts.sum_save hwf id _ measure_gU
  · show c'.accts.sum gSh + _ = _; rw [h]; exact Accts.sum_save hwf id _ measure_gSh
  · intro t; show c'.accts.sum (gCool t) + _ = _; rw [h]; exact Accts.sum_save hwf id _ (measure_gCool t)
  · intro k hk; rw [hget]; simp [hk]
  · rw [hget]; simp [norm_unstaked]
  · rw [hget]; simp [norm_shares]
  · rw [hget]; simp only [ite_true]; exact norm_avail_le _
  · intro hp; rw [hget]; simp only [ite_true]
    unfold Account.norm; split
    · next h' => simp at h'; omega
    · rfl

theorem depositInt_rel {c c' : Contract} {e : Env} {amt : Nat} (h : c.depositInt e = .ok (c', amt)) :
    Rel e c c' 0 ∧ KFP c c' ∧ amt = e.deposit ∧ c'.ltb = c.ltb + e.deposit ∧ c'.s = c.s := by
  obtain ⟨rfl, _, _, hc'⟩ := depositInt_spec h
  have es : c'.s = c.s := by subst hc'; rfl
  have ets : c'.ts = c.ts := by subst hc'; rfl
  have eltb : c'.ltb = c.ltb + e.deposit := by subst hc'; rfl
  have eacc : c'.accts = c.accts.save e.pred
      ⟨(c.get e.pred).unstaked + e.deposit, (c.get e.pred).stakeShares, (c.get e.pred).availEpoch⟩ := by
    subst hc'; rfl
  have eo : c'.owner = c.owner := by subst hc'; rfl
  have kfp : KFP c c' := by subst hc'; exact ⟨rfl, rfl, rfl⟩
  refine ⟨fun hc => ?_, kfp, rfl, eltb, es⟩
  obtain ⟨hwf', hU, hSh, hC, hfr, hu, hsh, hav, _⟩ := save_facts hc.wf eacc
  have := hc.sh; have := hc.price; have := hc.fee
  exact {
    inv := ⟨hwf', by omega, by omega, by rw [kfp.1]; exact hc.fee⟩
    fund := by omega
    avail := fun id => by
      by_cases hid : id = e.pred
      · subst hid; exact Nat.le_trans hav (Nat.le_max_left _ _)
      · rw [hfr id hid]; exact Nat.le_max_left _ _
    mono := fun t _ _ => by
      have h1 := hC t
      have h2 : gCool t (c.get e.pred) ≤
          (if t < (c.get e.pred).availEpoch then (c.get e.pred).unstaked + e.deposit else 0) := by
        simp only [gCool]; split <;> omega
      omega
    price := by rw [es, ets]; exact Nat.le_refl _
    frame := fun u hu' => by rw [hfr u hu']; exact ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
    owner := eo }

theorem withdrawInt_rel {c c' : Contract} {e : Env} {x : Nat} (h : c.withdrawInt e x = .ok c') :
    Rel e c c' 0 ∧ KFP c c' ∧ x ≤ e.balance ∧ c'.ltb + x = c.ltb ∧ c'.s = c.s ∧
    (c.get e.pred).availEpoch ≤ e.epoch ∧ x ≠ 0 ∧ x ≤ (c.get e.pred).unstaked := by
  obtain ⟨hx, hle, hav, hbal, hltb, hc'⟩ := withdrawInt_spec h
  have es : c'.s = c.s := by subst hc'; rfl
  have ets : c'.ts = c.ts := by subst hc'; rfl
  have eltb : c'.ltb = c.ltb - x := by subst hc'; rfl
  have eacc : c'.accts = c.accts.save e.pred
      ⟨(c.get e.pred).unstaked - x, (c.get e.pred).stakeShares, (c.get e.pred).availEpoch⟩ := by
    subst hc'; rfl
  have eo : c'.owner = c.owner := by subst hc'; rfl
  have kfp : KFP c c' := by subst hc'; exact ⟨rfl, rfl, rfl⟩
  refine ⟨fun hc => ?_, kfp, hbal, by omega, es, hav, hx, hle⟩
  obtain ⟨hwf', hU, hSh, hC, hfr, hu, hsh, hav', _⟩ := save_facts hc.wf eacc
  have := hc.sh; have := hc.price; have := hc.fee
  have hUle := u_le_sum hc.wf e.pred
  exact {
    inv := ⟨hwf', by omega, by omega, by rw [kfp.1]; exact hc.fee⟩
    fund := by omega
    avail := fun id => by
      by_cases hid : id = e.pred
      · subst hid; exact Nat.le_trans hav' (Nat.le_max_left _ _)
      · rw [hfr id hid]; exact Nat.le_max_left _ _
    mono := fun t ht _ => by
      have h1 := hC t
      have h2 : gCool t (c.get e.pred) = 0 := by simp only [gCool]; split <;> omega
      have h3 : (if t < (c.get e.pred).availEpoch then (c.get e.pred).unstaked - x else 0) = 0 := by
        split <;> omega
      omega
    price := by rw [es, ets]; exact Nat.le_refl _
    frame := fun u hu' => by rw [hfr u hu']; exact ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
    owner := eo }

theorem stakeInt_rel {c c' : Contract} {e : Env} {x : Nat} (h : c.stakeInt e x = .ok c') :
    Rel e c c' 1 ∧ KFP c c' ∧ c'.ltb = c.ltb := by
  obtain ⟨n, charge, amt, hx, hs, hts, hn, hn0, hch, hch0, hle, hamt, _, _, _, hc'⟩ := stakeInt_spec h
  have es : c'.s = c.s + amt := by subst hc'; rfl
  have ets : c'.ts = c.ts + n := by subst hc'; rfl
  have eltb : c'.ltb = c.ltb := by subst hc'; rfl
  have eacc : c'.accts = c.accts.save e.pred
      ⟨(c.get e.pred).unstaked - charge, (c.get e.pred).stakeShares + n, (c.get e.pred).availEpoch⟩ := by
    subst hc'; rfl
  have eo : c'.owner = c.owner := by subst hc'; rfl
  have kfp : KFP c c' := by subst hc'; exact ⟨rfl, rfl, rfl⟩
  refine ⟨fun hc => ?_, kfp, eltb⟩
  obtain ⟨hwf', hU, hSh, hC, hfr, hu, hsh, hav', _⟩ := save_facts hc.wf eacc
  have := hc.sh; have hpr := hc.price; have := hc.fee
  have hUle := u_le_sum hc.wf e.pred
  have htsp : 0 < c.ts := Nat.pos_of_ne_zero hts
  have r1 : charge ≤ amt := by rw [hch, hamt]; exact div_le_cdiv _ _
  have r2 : amt ≤ charge + 1 := by rw [hch, hamt]; exact cdiv_le_div_add_one htsp
  have r3 : c.s * n ≤ amt * c.ts := by rw [hamt]; exact cdiv_mul_ge htsp
  have r4 : n ≤ amt := by
    have : n * c.ts ≤ amt * c.ts := by
      calc n * c.ts = c.ts * n := Nat.mul_comm _ _
        _ ≤ c.s * n := Nat.mul_le_mul_right _ hpr
        _ ≤ amt * c.ts := r3
    exact Nat.le_of_mul_le_mul_right this htsp
  exact {
    inv := ⟨hwf', by omega, by omega, by rw [kfp.1]; exact hc.fee⟩
    fund := by omega
    avail := fun id => by
      by_cases hid : id = e.pred
      · subst hid; exact Nat.le_trans hav' (Nat.le_max_left _ _)
      · rw [hfr id hid]; exact Nat.le_max_left _ _
    mono := fun t _ _ => by
      have h1 := hC t
      have h2 : gCool t (c.get e.pred) ≤
          (if t < (c.get e.pred).availEpoch then (c.get e.pred).unstaked - charge else 0) + charge := by
        simp only [gCool]; split <;> omega
      omega
    price := by
      rw [es, ets, Nat.mul_add, Nat.add_mul]
      omega
    frame := fun u hu' => by rw [hfr u hu']; exact ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
    owner := eo }

theorem unstakeInt_rel {c c' : Contract} {e : Env} {x : Nat} (h : c.unstakeInt e x = .ok c') :
    Rel e c c' 1 ∧ KFP c c' ∧ c'.ltb = c.ltb ∧
    (CInv c → (c.get e.pred).unstaked + x ≤ (c'.get e.pred).unstaked ∧
      (c'.get e.pred).availEpoch = e.epoch + NUM_EPOCHS_TO_UNLOCK) := by
  obtain ⟨n, recv, ua, hx, hs, hts, hn, hn0, hle, hrecv, hr0, hu128, hep, hua, huas, hnts, hc'⟩ :=
    unstakeInt_spec h
  have es : c'.s = c.s - ua := by subst hc'; rfl
  have ets : c'.ts = c.ts - n := by subst hc'; rfl
  have eltb : c'.ltb = c.ltb := by subst hc'; rfl
  have eacc : c'.accts = c.accts.save e.pred
      ⟨(c.get e.pred).unstaked + recv, (c.get e.pred).stakeShares - n, e.epoch + NUM_EPOCHS_TO_UNLOCK⟩ := by
    subst hc'; rfl
  have eo : c'.owner = c.owner := by subst hc'; rfl
  have kfp : KFP c c' := by subst hc'; exact ⟨rfl, rfl, rfl⟩
  have htsp : 0 < c.ts := Nat.pos_of_ne_zero hts
  have hsp : 0 < c.s := Nat.pos_of_ne_zero hs
  have r1 : ua ≤ recv := by rw [hua, hrecv]; exact div_le_cdiv _ _
  have r2 : recv ≤ ua + 1 := by rw [hua, hrecv]; exact cdiv_le_div_add_one htsp
  have r3 : ua * c.ts ≤ c.s * n := by rw [hua]; exact Nat.div_mul_le_self _ _
  have r5 : x ≤ ua := by
    have h1 : c.ts * x ≤ n * c.s := by rw [hn]; exact cdiv_mul_ge hsp
    rw [hua]; apply (Nat.le_div_iff_mul_le htsp).2
    rw [Nat.mul_comm x, Nat.mul_comm c.s]; exact h1
  refine ⟨fun hc => ?_, kfp, eltb, fun hc => ?_⟩
  · obtain ⟨hwf', hU, hSh, hC, hfr, hu, hsh, hav', hav''⟩ := save_facts hc.wf eacc
    have := hc.sh; have hpr := hc.price; have := hc.fee
    have hshle := sh_le_sum hc.wf e.pred
    have r6 : ua ≤ n + (c.s - c.ts) := by
      obtain ⟨D, hD⟩ : ∃ D, c.s = c.ts + D := ⟨c.s - c.ts, by omega⟩
      have h1 : c.s * n = c.ts * n + D * n := by rw [hD, Nat.add_mul]
      have h2 : D * n ≤ D * c.ts := Nat.mul_le_mul_left _ hnts
      have h3 : ua * c.ts ≤ (n + D) * c.ts := by
        rw [Nat.add_mul, Nat.mul_comm n]; omega
      have := Nat.le_of_mul_le_mul_right h3 htsp
      omega
    exact {
      inv := ⟨hwf', by omega, by omega, by rw [kfp.1]; exact hc.fee⟩
      fund := by omega
      avail := fun id => by
        by_cases hid : id = e.pred
        · subst hid; exact Nat.le_trans hav' (Nat.le_max_right _ _)
        · rw [hfr id hid]; exact Nat.le_max_left _ _
      mono := fun t _ ht2 => by
        have h1 := hC t
        have h2 : gCool t (c.get e.pred) ≤ (c.get e.pred).unstaked := gCool_le t _
        have h3 : (if t < e.epoch + NUM_EPOCHS_TO_UNLOCK then (c.get e.pred).unstaked + recv else 0) =
            (c.get e.pred).unstaked + recv := by
          have : t < e.epoch + NUM_EPOCHS_TO_UNLOCK := by simp only [NUM_EPOCHS_TO_UNLOCK]; omega
          simp only [this, ite_true]
        omega
      price := by
        rw [es, ets, Nat.mul_sub, Nat.sub_mul]
        have : c.s * n ≤ c.s * c.ts := Nat.mul_le_mul_left _ hnts
        have : ua * c.ts ≤ c.s * c.ts := Nat.mul_le_mul_right _ huas
        omega
      frame := fun u hu' => by rw [hfr u hu']; exact ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
      owner := eo }
  · obtain ⟨_, _, _, _, _, hu, _, _, hav''⟩ := save_facts hc.wf eacc
    exact ⟨by omega, hav'' (Or.inl (by omega))⟩

/-- `internal_ping` -/
theorem ping_rel {c c1 : Contract} {e : Env} {b : Bool} (hc : CInv c) (h : c.ping e = .ok (c1, b)) :
    RelC e c c1 0 ∧ KFP c c1 ∧ c1.sumU = c.sumU ∧ (∀ t, c1.cool t = c.cool t) ∧
    c1.s + c.ltb = c.s + c1.ltb ∧ c.ltb ≤ c1.ltb ∧
    ((b = false ∧ c1 = c) ∨
      (b = true ∧ c1.ltb + e.deposit = e.locked + e.balance ∧ e.locked + e.balance ≤ U128_MAX)) ∧
    (∀ k, (c1.get k).unstaked = (c.get k).unstaked ∧ (c1.get k).availEpoch = (c.get k).availEpoch) := by
  rcases ping_spec h with ⟨_, hc1, rfl⟩ | ⟨_, rfl, hb1, hb2, hb3, cd, hcd, hc1⟩
  · rw [hc1]
    exact ⟨Rel.refl e c hc, ⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, rfl, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩,
      fun _ => ⟨rfl, rfl⟩⟩
  have hltb1 : c1.ltb = e.locked + e.balance - e.deposit := by subst hc1; rfl
  have hfin : c1.ltb + e.deposit = e.locked + e.balance := by omega
  have hpr := hc.price; have hsh := hc.sh; have hfee := hc.fee
  rcases hcd with ⟨hR0, rfl⟩ | ⟨hRpos, hd⟩
  · -- no reward
    have es : c1.s = c.s := by subst hc1; rfl
    have ets : c1.ts = c.ts := by subst hc1; rfl
    have eacc : c1.accts = c.accts := by subst hc1; rfl
    have eo : c1.owner = c.owner := by subst hc1; rfl
    have kfp : KFP c c1 := by subst hc1; exact ⟨rfl, rfl, rfl⟩
    have hg : ∀ k, c1.get k = c.get k := fun k => by show c1.accts.get k = _; rw [eacc]; rfl
    have hU : c1.sumU = c.sumU := by simp only [Contract.sumU]; rw [eacc]
    have hS : c1.sumSh = c.sumSh := by simp only [Contract.sumSh]; rw [eacc]
    have hC : ∀ t, c1.cool t = c.cool t := fun t => by simp only [Contract.cool]; rw [eacc]
    refine ⟨{ inv := ⟨by rw [eacc]; exact hc.wf, by omega, by omega, by rw [kfp.1]; exact hfee⟩
              fund := by omega
              avail := fun id => by rw [hg]; exact Nat.le_max_left _ _
              mono := fun t _ _ => by rw [hC, es]; exact Nat.le_refl _
              price := by rw [es, ets]; exact Nat.le_refl _
              frame := fun u _ => by rw [hg]; exact ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
              owner := eo }, kfp, hU, hC, by omega, by omega, Or.inr ⟨rfl, hfin, hb1⟩,
            fun k => by rw [hg]; exact ⟨rfl, rfl⟩⟩
  · -- reward R > 0 distributed
    obtain ⟨fee, n, _, hfee_eq, hfR, _, hs0, hn, _, hcase⟩ := distribute_spec hd
    dsimp only at hfee_eq hs0 hn hfR hcase
    have hRle : c.ltb ≤ e.locked + e.balance - e.deposit := hb3
    -- n ≤ fee
    have hnfee : n ≤ fee := by
      rw [hn]; exact mul_div_le_of_le (Nat.pos_of_ne_zero hs0) (by omega)
    -- price: s * n ≤ R * ts
    have hpn : c.s * n ≤ (e.locked + e.balance - e.deposit - c.ltb) * c.ts := by
      have h1 : n * (c.s + (e.locked + e.balance - e.deposit - c.ltb - fee)) ≤ c.ts * fee := by
        rw [hn]; exact Nat.div_mul_le_self _ _
      have h2 : c.s * n ≤ n * (c.s + (e.locked + e.balance - e.deposit - c.ltb - fee)) := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      have h3 : c.ts * fee ≤ c.ts * (e.locked + e.balance - e.deposit - c.ltb) :=
        Nat.mul_le_mul_left _ hfR
      rw [Nat.mul_comm _ c.ts]; omega
    rcases hcase with ⟨hn0, rfl⟩ | ⟨hnpos, _, _, rfl⟩
    · have es : c1.s = c.s + (e.locked + e.balance - e.deposit - c.ltb) := by subst hc1; simp; omega
      have ets : c1.ts = c.ts := by subst hc1; rfl
      have eacc : c1.accts = c.accts := by subst hc1; rfl
      have eo : c1.owner = c.owner := by subst hc1; rfl
      have kfp : KFP c c1 := by subst hc1; exact ⟨rfl, rfl, rfl⟩
      have hg : ∀ k, c1.get k = c.get k := fun k => by show c1.accts.get k = _; rw [eacc]; rfl
      have hU : c1.sumU = c.sumU := by simp only [Contract.sumU]; rw [eacc]
      have hS : c1.sumSh = c.sumSh := by simp only [Contract.sumSh]; rw [eacc]
      have hC : ∀ t, c1.cool t = c.cool t := fun t => by simp only [Contract.cool]; rw [eacc]
      refine ⟨{ inv := ⟨by rw [eacc]; exact hc.wf, by omega, by omega, by rw [kfp.1]; exact hfee⟩
                fund := by omega
                avail := fun id => by rw [hg]; exact Nat.le_max_left _ _
                mono := fun t _ _ => by rw [hC, es]; omega
                price := by rw [es, ets, Nat.add_mul]; exact Nat.le_add_right _ _
                frame := fun u _ => by rw [hg]; exact ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
                owner := eo }, kfp, hU, hC, by omega, by omega, Or.inr ⟨rfl, hfin, hb1⟩,
              fun k => by rw [hg]; exact ⟨rfl, rfl⟩⟩
    · have es : c1.s = c.s + (e.locked + e.balance - e.deposit - c.ltb) := by subst hc1; simp; omega
      have ets : c1.ts = c.ts + n := by subst hc1; rfl
      have eacc : c1.accts = c.accts.save c.owner
          ⟨(c.get c.owner).unstaked, (c.get c.owner).stakeShares + n, (c.get c.owner).availEpoch⟩ := by
        subst hc1; rfl
      have eo : c1.owner = c.owner := by subst hc1; rfl
      have kfp : KFP c c1 := by subst hc1; exact ⟨rfl, rfl, rfl⟩
      obtain ⟨hwf', hU, hSh, hC, hfr, hu, hsh', hav', hav''⟩ := save_facts hc.wf eacc
      have hav2 := hav'' (Or.inr (by omega))
      have hC' : ∀ t, c1.cool t = c.cool t := fun t => by
        have := hC t; simp only [gCool] at this; omega
      have hg : ∀ k, (c1.get k).unstaked = (c.get k).unstaked ∧ (c1.get k).availEpoch = (c.get k).availEpoch := by
        intro k; by_cases hk : k = c.owner
        · subst hk; exact ⟨hu, hav2⟩
        · rw [hfr k hk]; exact ⟨rfl, rfl⟩
      refine ⟨{ inv := ⟨hwf', by omega, by omega, by rw [kfp.1]; exact hfee⟩
                fund := by omega
                avail := fun id => by rw [(hg id).2]; exact Nat.le_max_left _ _
                mono := fun t _ _ => by rw [hC', es]; omega
                price := by
                  rw [es, ets, Nat.add_mul, Nat.mul_add]
                  omega
                frame := fun u _ => by
                  refine ⟨(hg u).1, (hg u).2, ?_, fun hu' => by rw [hfr u hu']⟩
                  by_cases hk : u = c.owner
                  · subst hk; omega
                  · rw [hfr u hk]; exact Nat.le_refl _
                owner := eo }, kfp, by omega, hC', by omega, by omega, Or.inr ⟨rfl, hfin, hb1⟩, hg⟩

end StakingPool
