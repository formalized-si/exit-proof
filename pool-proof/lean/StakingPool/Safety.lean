/-
  Safety: what other accounts and the owner can and cannot do; the share price
  never decreases (the `verify_stake_price_increase_guarantee` property).
-/
import StakingPool.Exit

namespace StakingPool

/-- The owner-only methods. -/
def Method.ownerOnly : Method → Bool
  | .pauseStaking | .resumeStaking | .updateFee _ | .updateStakingKey _ | .vote _ _ => true
  | _ => false

/-- **Share price never decreases** (any successful call, by anybody). Price = `s / ts`;
stated without division: `s * ts' ≤ s' * ts`. -/
theorem exec_price {vk : String → Bool} {c c' : Contract} {e : Env} {m : Method} {eff : Eff}
    (hc : CInv c) (hk : c.paused = false → vk c.key = true) (h : exec vk c e m = .ok (c', eff)) :
    c.s * c'.ts ≤ c'.s * c.ts := by
  obtain ⟨c1, pp, rest, _, _, _⟩ := exec_facts hc hk h
  exact price_trans pp.rel.price rest.price (Nat.lt_of_le_of_lt (Nat.zero_le _) pp.rel.inv.sh)

/-- ... and along every step of every reachable world (protocol steps do not touch the
contract state). -/
theorem step_price {vk : String → Bool} {self : AccountId} {w w' : World} {a : Option AccountId}
    (hR : Reach vk self w) (hs : Step vk self a w w') : w.c.s * w'.c.ts ≤ w'.c.s * w.c.ts := by
  have hw := hR.inv
  cases hs with
  | call p m d h => exact exec_price hw.c hw.key h
  | advance => exact Nat.le_refl _
  | income => exact Nat.le_refl _
  | rebalance => exact Nat.le_refl _

/-- Every successful call consumes at most one yocto of the 10^12-yocto price-guarantee
fund: rounding favours the calling delegator by at most 1 yocto per call, paid by the fund,
never by the other delegators (whose share price does not decrease). -/
theorem exec_rounding {vk : String → Bool} {c c' : Contract} {e : Env} {m : Method} {eff : Eff}
    (hc : CInv c) (hk : c.paused = false → vk c.key = true) (h : exec vk c e m = .ok (c', eff)) :
    ∃ c1 : Contract, c1.s + c.ltb = c.s + c1.ltb ∧ c1.sumU = c.sumU ∧
      c'.s + c'.sumU + c1.ltb ≤ c1.s + c1.sumU + c'.ltb + 1 := by
  obtain ⟨c1, pp, rest, _, _, _⟩ := exec_facts hc hk h
  exact ⟨c1, pp.ltb, pp.sumU, rest.fund⟩

/-! ## The owner -/

theorem exec_owner_body {vk : String → Bool} {c c' : Contract} {e : Env} {m : Method} {eff : Eff}
    (h : exec vk c e m = .ok (c', eff)) : execBody vk c e m = .ok (c', eff) := by
  simp only [exec, bind_ok, ensure_ok] at h
  obtain ⟨_, _, h⟩ := h; exact h

/-- `update_reward_fee_fraction` = ping with the OLD fee (all rewards so far are distributed
with it), then the new fee. -/
theorem updateFee_shape {vk : String → Bool} {c c' : Contract} {e : Env} {f : Fee} {eff : Eff}
    (h : exec vk c e (.updateFee f) = .ok (c', eff)) :
    e.pred = c.owner ∧ f.den ≠ 0 ∧ f.num ≤ f.den ∧ eff.transfer = 0 ∧
      ∃ c1 b, c.ping e = .ok (c1, b) ∧ c' = { c1 with fee := f } := by
  have h := exec_owner_body h
  simp only [execBody, bind_ok, pure_ok] at h
  obtain ⟨_, ho, _, hf, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
  obtain ⟨_, _, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  exact ⟨assertOwner_ok.1 ho, (assertValid_ok.1 hf).1, (assertValid_ok.1 hf).2, by rw [← heq.2],
    c1, b, hp, heq.1.symm⟩

theorem updateStakingKey_shape {vk : String → Bool} {c c' : Contract} {e : Env} {k : String} {eff : Eff}
    (h : exec vk c e (.updateStakingKey k) = .ok (c', eff)) :
    e.pred = c.owner ∧ eff.transfer = 0 ∧ ∃ c1 b, c.ping e = .ok (c1, b) ∧ c' = { c1 with key := k } := by
  have h := exec_owner_body h
  simp only [execBody, bind_ok, pure_ok] at h
  obtain ⟨_, ho, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
  obtain ⟨_, _, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  exact ⟨assertOwner_ok.1 ho, by rw [← heq.2], c1, b, hp, heq.1.symm⟩

theorem pauseStaking_shape {vk : String → Bool} {c c' : Contract} {e : Env} {eff : Eff}
    (h : exec vk c e .pauseStaking = .ok (c', eff)) :
    e.pred = c.owner ∧ eff.transfer = 0 ∧ ∃ c1 b, c.ping e = .ok (c1, b) ∧ c' = { c1 with paused := true } := by
  have h := exec_owner_body h
  simp only [execBody, bind_ok, pure_ok, ensure_ok] at h
  obtain ⟨_, ho, _, _, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
  obtain ⟨_, _, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  exact ⟨assertOwner_ok.1 ho, by rw [← heq.2], c1, b, hp, heq.1.symm⟩

theorem resumeStaking_shape {vk : String → Bool} {c c' : Contract} {e : Env} {eff : Eff}
    (h : exec vk c e .resumeStaking = .ok (c', eff)) :
    e.pred = c.owner ∧ eff.transfer = 0 ∧ ∃ c1 b, c.ping e = .ok (c1, b) ∧ c' = { c1 with paused := false } := by
  have h := exec_owner_body h
  simp only [execBody, bind_ok, pure_ok, ensure_ok] at h
  obtain ⟨_, ho, _, _, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
  obtain ⟨_, _, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  exact ⟨assertOwner_ok.1 ho, by rw [← heq.2], c1, b, hp, heq.1.symm⟩

theorem vote_shape {vk : String → Bool} {c c' : Contract} {e : Env} {a : AccountId} {b : Bool} {eff : Eff}
    (h : exec vk c e (.vote a b) = .ok (c', eff)) :
    e.pred = c.owner ∧ c' = c ∧ eff.transfer = 0 := by
  have h := exec_owner_body h
  simp only [execBody, bind_ok, pure_ok, ensure_ok] at h
  obtain ⟨_, ho, _, _, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨assertOwner_ok.1 ho, rfl, rfl⟩

/-- **What the owner can do (T_safety, owner part).** A successful owner-only method
(pause/resume staking, change the reward fee, change the staking key, vote) is a ping
followed by setting `paused`, `fee` or `key` (or nothing, for `vote`). It changes nobody's
unstaked balance or unlock epoch, nobody's shares except the owner's own fee shares from the
ping, never decreases the share price, and transfers nothing. -/
theorem owner_methods {vk : String → Bool} {c c' : Contract} {e : Env} {m : Method} {eff : Eff}
    (hc : CInv c) (h : exec vk c e m = .ok (c', eff)) (hm : m.ownerOnly = true) :
    e.pred = c.owner ∧ eff.transfer = 0 ∧ c'.owner = c.owner ∧ c.s * c'.ts ≤ c'.s * c.ts ∧
    ∀ u, (c'.get u).unstaked = (c.get u).unstaked ∧ (c'.get u).availEpoch = (c.get u).availEpoch ∧
      (c.get u).stakeShares ≤ (c'.get u).stakeShares ∧
      (u ≠ c.owner → (c'.get u).stakeShares = (c.get u).stakeShares) := by
  -- after the ping, the setters keep the accounts and the totals
  have key : ∀ (c1 c' : Contract) (b : Bool), c.ping e = .ok (c1, b) → c'.accts = c1.accts →
      c'.s = c1.s → c'.ts = c1.ts → c'.owner = c1.owner →
      c'.owner = c.owner ∧ c.s * c'.ts ≤ c'.s * c.ts ∧
      ∀ u, (c'.get u).unstaked = (c.get u).unstaked ∧ (c'.get u).availEpoch = (c.get u).availEpoch ∧
        (c.get u).stakeShares ≤ (c'.get u).stakeShares ∧
        (u ≠ c.owner → (c'.get u).stakeShares = (c.get u).stakeShares) := by
    intro c1 c' b hp ha hs hts ho
    obtain ⟨r1, _, _, _, _, _, _, hacct⟩ := ping_rel hc hp
    have hg : ∀ u, c'.get u = c1.get u := fun u => by show c'.accts.get u = _; rw [ha]; rfl
    refine ⟨ho.trans r1.owner, by rw [hs, hts]; exact r1.price, fun u => ?_⟩
    rw [hg u]
    refine ⟨(hacct u).1, (hacct u).2, ping_shares hc hp u, fun hu => ?_⟩
    -- the ping changes no shares but the owner's
    have h' : c.ping { e with pred := c.owner } = .ok (c1, b) := hp
    exact ((ping_rel hc h').1.frame u hu).2.2.2 hu
  cases m with
  | updateFee f =>
    obtain ⟨ho, _, _, ht, c1, b, hp, rfl⟩ := updateFee_shape h
    exact ⟨ho, ht, key c1 _ b hp rfl rfl rfl rfl⟩
  | updateStakingKey k =>
    obtain ⟨ho, ht, c1, b, hp, rfl⟩ := updateStakingKey_shape h
    exact ⟨ho, ht, key c1 _ b hp rfl rfl rfl rfl⟩
  | pauseStaking =>
    obtain ⟨ho, ht, c1, b, hp, rfl⟩ := pauseStaking_shape h
    exact ⟨ho, ht, key c1 _ b hp rfl rfl rfl rfl⟩
  | resumeStaking =>
    obtain ⟨ho, ht, c1, b, hp, rfl⟩ := resumeStaking_shape h
    exact ⟨ho, ht, key c1 _ b hp rfl rfl rfl rfl⟩
  | vote a b =>
    obtain ⟨ho, rfl, ht⟩ := vote_shape h
    exact ⟨ho, ht, rfl, Nat.le_refl _, fun u => ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩⟩
  | _ => simp [Method.ownerOnly] at hm

end StakingPool
