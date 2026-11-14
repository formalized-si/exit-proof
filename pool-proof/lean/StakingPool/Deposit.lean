/-
  Money in: a successful deposit raises the depositor's claim by at least the deposit.
-/
import StakingPool.Safety

namespace StakingPool

theorem div_add_div_le (a b t : Nat) : a / t + b / t ≤ (a + b) / t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · apply (Nat.le_div_iff_mul_le ht).2
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)

/-- ping never decreases anybody's claim -/
theorem ping_claim {c c1 : Contract} {e : Env} {b : Bool} (hc : CInv c) (h : c.ping e = .ok (c1, b))
    (u : AccountId) : claim c u ≤ claim c1 u := by
  obtain ⟨r1, _, _, _, _, _, _, hacct⟩ := ping_rel hc h
  have hts : 0 < c.ts := Nat.lt_of_le_of_lt (Nat.zero_le _) hc.sh
  have hts1 : 0 < c1.ts := Nat.lt_of_le_of_lt (Nat.zero_le _) r1.inv.sh
  have := value_mono r1.price hts hts1 (ping_shares hc h u)
  unfold claim; rw [(hacct u).1]; omega

/-- `stake(amount)` never decreases the staker's claim (the rounding goes its way) -/
theorem stakeInt_claim {c c' : Contract} {e : Env} {x : Nat} (hc : CInv c) (h : c.stakeInt e x = .ok c') :
    claim c e.pred ≤ claim c' e.pred := by
  obtain ⟨n, charge, amt, _, _, hts, _, _, hch, _, hle, hamt, _, _, _, hc'⟩ := stakeInt_spec h
  have es : c'.s = c.s + amt := by subst hc'; rfl
  have ets : c'.ts = c.ts + n := by subst hc'; rfl
  have eacc : c'.accts = c.accts.save e.pred
      ⟨(c.get e.pred).unstaked - charge, (c.get e.pred).stakeShares + n, (c.get e.pred).availEpoch⟩ := by
    subst hc'; rfl
  obtain ⟨_, _, _, _, _, hu, hsh, _, _⟩ := save_facts hc.wf eacc
  obtain ⟨r, _, _⟩ := stakeInt_rel h
  have rc := r hc
  have htsp : 0 < c.ts := Nat.pos_of_ne_zero hts
  have hts' : 0 < c'.ts := by omega
  -- value at the new price of all shares ≥ value at the old price
  have h1 : c.s * ((c.get e.pred).stakeShares + n) / c.ts ≤ c'.s * (c'.get e.pred).stakeShares / c'.ts :=
    value_mono rc.price htsp hts' (by rw [hsh]; exact Nat.le_refl _)
  have h2 : c.s * (c.get e.pred).stakeShares / c.ts + charge ≤ c.s * ((c.get e.pred).stakeShares + n) / c.ts := by
    rw [hch, Nat.mul_add]; exact div_add_div_le _ _ _
  unfold claim; rw [hu]; omega

/-- **Money in.** A successful `deposit` or `deposit_and_stake` with attached deposit `d`
raises the caller's claim (`get_account_total_balance`) by at least `d` — no rounding loss.
Together with `exit_guarantee` this says: what you deposit, you can take out. -/
theorem deposit_claim {vk : String → Bool} {c c' : Contract} {e : Env} {m : Method} {eff : Eff}
    (hc : CInv c) (h : exec vk c e m = .ok (c', eff)) (hm : m = .deposit ∨ m = .depositAndStake) :
    claim c e.pred + e.deposit ≤ claim c' e.pred := by
  have h := exec_owner_body h
  rcases hm with rfl | rfl
  · simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨⟨c2, amt⟩, hd, h⟩ := h; simp only at h
    obtain ⟨_, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have hc1 := (ping_rel hc hp).1.inv
    have := ping_claim hc hp e.pred
    obtain ⟨_, _, _, _, es⟩ := depositInt_rel hd
    obtain ⟨_, _, _, hc2'⟩ := depositInt_spec hd
    have ets : c2.ts = c1.ts := by subst hc2'; rfl
    have eacc : c2.accts = c1.accts.save e.pred
        ⟨(c1.get e.pred).unstaked + e.deposit, (c1.get e.pred).stakeShares, (c1.get e.pred).availEpoch⟩ := by
      subst hc2'; rfl
    obtain ⟨_, _, _, _, _, hu, hsh, _, _⟩ := save_facts hc1.wf eacc
    unfold claim at *; rw [hu, hsh, es, ets]; omega
  · simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨⟨c2, amt⟩, hd, h⟩ := h; simp only at h
    obtain ⟨c3, hs, _, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have hc1 := (ping_rel hc hp).1.inv
    have h1 := ping_claim hc hp e.pred
    obtain ⟨r2, _, rfl, _, es⟩ := depositInt_rel hd
    obtain ⟨_, _, _, hc2'⟩ := depositInt_spec hd
    have ets : c2.ts = c1.ts := by subst hc2'; rfl
    have eacc : c2.accts = c1.accts.save e.pred
        ⟨(c1.get e.pred).unstaked + e.deposit, (c1.get e.pred).stakeShares, (c1.get e.pred).availEpoch⟩ := by
      subst hc2'; rfl
    obtain ⟨_, _, _, _, _, hu, hsh, _, _⟩ := save_facts hc1.wf eacc
    have hc2 := (r2 hc1).inv
    have h3 := stakeInt_claim hc2 hs
    have h2 : claim c1 e.pred + e.deposit = claim c2 e.pred := by
      unfold claim; rw [hu, hsh, es, ets]; omega
    omega

end StakingPool
