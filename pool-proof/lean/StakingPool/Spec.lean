/-
  Ok-result characterisations of the internal methods (what a successful
  internal call computes, with every assert that had to pass).
-/
import StakingPool.Basic

namespace StakingPool

theorem multiply_ok {f : Fee} {v r : Nat} :
    f.multiply v = .ok r ↔ f.den ≠ 0 ∧ f.num * v / f.den ≤ U128_MAX ∧ r = f.num * v / f.den := by
  unfold Fee.multiply; split <;> simp_all [asU128_ok, throw_ok]

theorem restake_ok {c : Contract} {vk : String → Bool} {r : Option Nat} :
    c.restake vk = .ok r ↔ (c.paused = true ∧ r = none) ∨ (c.paused = false ∧ vk c.key = true ∧ r = some c.s) := by
  unfold Contract.restake
  cases hp : c.paused <;> cases hk : vk c.key <;>
    simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, eq_comm]

theorem assertOwner_ok {c : Contract} {e : Env} {u : Unit} : assertOwner c e = .ok u ↔ e.pred = c.owner := by
  simp [assertOwner, ensure_ok]

theorem assertValid_ok {f : Fee} {u : Unit} : f.assertValid = .ok u ↔ f.den ≠ 0 ∧ f.num ≤ f.den := by
  simp [Fee.assertValid, bind_ok, ensure_ok]

theorem payOwner_spec {c c' : Contract} {n : Nat} (h : c.payOwner n = .ok c') :
    (c.get c.owner).stakeShares + n ≤ U128_MAX ∧ c.ts + n ≤ U128_MAX ∧
    c' = { c.save c.owner ⟨(c.get c.owner).unstaked, (c.get c.owner).stakeShares + n, (c.get c.owner).availEpoch⟩
           with ts := c.ts + n } := by
  simp only [Contract.payOwner, bind_ok, add128_ok, pure_ok] at h
  obtain ⟨sh, ⟨hsh, rfl⟩, ts, ⟨hts, rfl⟩, rfl⟩ := h
  exact ⟨hsh, hts, rfl⟩

/-- `distribute` = the `total_reward > 0` branch of `internal_ping`. -/
theorem distribute_spec {c c' : Contract} {R : Nat} (h : c.distribute R = .ok c') :
    ∃ fee n, c.fee.den ≠ 0 ∧ fee = c.fee.num * R / c.fee.den ∧ fee ≤ R ∧
      c.s + (R - fee) ≤ U128_MAX ∧ c.s + (R - fee) ≠ 0 ∧ n = c.ts * fee / (c.s + (R - fee)) ∧
      c.s + (R - fee) + fee ≤ U128_MAX ∧
      ((n = 0 ∧ c' = { c with s := c.s + (R - fee) + fee }) ∨
       (0 < n ∧ (c.get c.owner).stakeShares + n ≤ U128_MAX ∧ c.ts + n ≤ U128_MAX ∧
        c' = { (c.save c.owner ⟨(c.get c.owner).unstaked, (c.get c.owner).stakeShares + n, (c.get c.owner).availEpoch⟩)
                with s := c.s + (R - fee) + fee, ts := c.ts + n })) := by
  simp only [Contract.distribute, bind_ok, multiply_ok, sub128_ok, add128_ok, sharesDown_ok, pure_ok] at h
  obtain ⟨fee, ⟨hden, _, rfl⟩, rem, ⟨hfr, rfl⟩, s1, ⟨hs1, rfl⟩, n, ⟨hs0, _, hn⟩, c2, hc2, s2, ⟨hs2, rfl⟩, rfl⟩ := h
  refine ⟨_, n, hden, rfl, hfr, hs1, hs0, hn, ?_⟩
  simp only [ite_ok, pure_ok] at hc2
  rcases hc2 with ⟨hpos, hp⟩ | ⟨hz, rfl⟩
  · obtain ⟨hsh, hts, rfl⟩ := payOwner_spec hp
    exact ⟨hs2, Or.inr ⟨hpos, hsh, hts, rfl⟩⟩
  · exact ⟨hs2, Or.inl ⟨by omega, rfl⟩⟩

theorem ping_spec {c c' : Contract} {e : Env} {b : Bool} (h : c.ping e = .ok (c', b)) :
    (c.lastEpoch = e.epoch ∧ c' = c ∧ b = false) ∨
    (c.lastEpoch ≠ e.epoch ∧ b = true ∧ e.locked + e.balance ≤ U128_MAX ∧
      e.deposit ≤ e.locked + e.balance ∧ c.ltb ≤ e.locked + e.balance - e.deposit ∧
      ∃ cd, ((e.locked + e.balance - e.deposit - c.ltb = 0 ∧ cd = { c with lastEpoch := e.epoch }) ∨
             (0 < e.locked + e.balance - e.deposit - c.ltb ∧
               ({ c with lastEpoch := e.epoch } : Contract).distribute
                 (e.locked + e.balance - e.deposit - c.ltb) = .ok cd)) ∧
        c' = { cd with ltb := e.locked + e.balance - e.deposit }) := by
  unfold Contract.ping at h
  split at h
  · simp only [pure_ok, Prod.mk.injEq] at h
    exact Or.inl ⟨by assumption, h.1.symm, h.2.symm⟩
  · simp only [bind_ok, add128_ok, sub128_ok, ensure_ok, pure_ok, Prod.mk.injEq] at h
    obtain ⟨tb0, ⟨h1, rfl⟩, tb, ⟨h2, rfl⟩, _, h3, cd, hcd, h4, h5⟩ := h
    refine Or.inr ⟨by assumption, h5.symm, h1, h2, h3, cd, ?_, h4.symm⟩
    simp only [ite_ok, pure_ok] at hcd
    rcases hcd with ⟨hr, hd⟩ | ⟨hr, hd⟩
    · exact Or.inr ⟨hr, hd⟩
    · exact Or.inl ⟨by omega, hd.symm⟩

theorem depositInt_spec {c c' : Contract} {e : Env} {amt : Nat} (h : c.depositInt e = .ok (c', amt)) :
    amt = e.deposit ∧ (c.get e.pred).unstaked + e.deposit ≤ U128_MAX ∧ c.ltb + e.deposit ≤ U128_MAX ∧
    c' = { c.save e.pred ⟨(c.get e.pred).unstaked + e.deposit, (c.get e.pred).stakeShares, (c.get e.pred).availEpoch⟩
           with ltb := c.ltb + e.deposit } := by
  simp only [Contract.depositInt, bind_ok, add128_ok, pure_ok, Prod.mk.injEq] at h
  obtain ⟨u, ⟨hu, rfl⟩, l, ⟨hl, rfl⟩, h1, h2⟩ := h
  exact ⟨h2.symm, hu, hl, h1.symm⟩

theorem withdrawInt_spec {c c' : Contract} {e : Env} {x : Nat} (h : c.withdrawInt e x = .ok c') :
    x ≠ 0 ∧ x ≤ (c.get e.pred).unstaked ∧ (c.get e.pred).availEpoch ≤ e.epoch ∧ x ≤ e.balance ∧
    x ≤ c.ltb ∧
    c' = { c.save e.pred ⟨(c.get e.pred).unstaked - x, (c.get e.pred).stakeShares, (c.get e.pred).availEpoch⟩
           with ltb := c.ltb - x } := by
  simp only [Contract.withdrawInt, bind_ok, ensure_ok, sub128_ok, pure_ok] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, l, ⟨h5, rfl⟩, rfl⟩ := h
  exact ⟨h1, h2, h3, h4, h5, rfl⟩

theorem stakeInt_spec {c c' : Contract} {e : Env} {x : Nat} (h : c.stakeInt e x = .ok c') :
    ∃ n charge amt, x ≠ 0 ∧ c.s ≠ 0 ∧ c.ts ≠ 0 ∧ n = c.ts * x / c.s ∧ n ≠ 0 ∧
      charge = c.s * n / c.ts ∧ charge ≠ 0 ∧ charge ≤ (c.get e.pred).unstaked ∧
      amt = (c.s * n + (c.ts - 1)) / c.ts ∧
      (c.get e.pred).stakeShares + n ≤ U128_MAX ∧ c.s + amt ≤ U128_MAX ∧ c.ts + n ≤ U128_MAX ∧
      c' = { c.save e.pred ⟨(c.get e.pred).unstaked - charge, (c.get e.pred).stakeShares + n, (c.get e.pred).availEpoch⟩
             with s := c.s + amt, ts := c.ts + n } := by
  simp only [Contract.stakeInt, bind_ok, ensure_ok, sharesDown_ok, amountDown_ok, amountUp_ok,
    add128_ok, pure_ok] at h
  obtain ⟨_, hx, n, ⟨hs, _, rfl⟩, _, hn, ch, ⟨hts, _, rfl⟩, _, hch, _, hle, sh, ⟨hsh, rfl⟩,
    amt, ⟨_, _, rfl⟩, s', ⟨hs', rfl⟩, ts', ⟨hts', rfl⟩, rfl⟩ := h
  exact ⟨_, _, _, hx, hs, hts, rfl, hn, rfl, hch, hle, rfl, hsh, hs', hts', rfl⟩

theorem unstakeInt_spec {c c' : Contract} {e : Env} {x : Nat} (h : c.unstakeInt e x = .ok c') :
    ∃ n recv ua, x ≠ 0 ∧ c.s ≠ 0 ∧ c.ts ≠ 0 ∧ n = (c.ts * x + (c.s - 1)) / c.s ∧ n ≠ 0 ∧
      n ≤ (c.get e.pred).stakeShares ∧ recv = (c.s * n + (c.ts - 1)) / c.ts ∧ recv ≠ 0 ∧
      (c.get e.pred).unstaked + recv ≤ U128_MAX ∧ e.epoch + NUM_EPOCHS_TO_UNLOCK ≤ U64_MAX ∧
      ua = c.s * n / c.ts ∧ ua ≤ c.s ∧ n ≤ c.ts ∧
      c' = { c.save e.pred ⟨(c.get e.pred).unstaked + recv, (c.get e.pred).stakeShares - n, e.epoch + NUM_EPOCHS_TO_UNLOCK⟩
             with s := c.s - ua, ts := c.ts - n } := by
  simp only [Contract.unstakeInt, bind_ok, ensure_ok, sharesUp_ok, amountDown_ok, amountUp_ok,
    add128_ok, add64_ok, sub128_ok, pure_ok] at h
  obtain ⟨_, hx, _, hs, n, ⟨_, _, rfl⟩, _, hn, _, hle, recv, ⟨hts, _, rfl⟩, _, hr, u, ⟨hu, rfl⟩,
    av, ⟨hav, rfl⟩, ua, ⟨_, _, rfl⟩, s', ⟨hua, rfl⟩, ts', ⟨hnts, rfl⟩, rfl⟩ := h
  exact ⟨_, _, _, hx, hs, hts, rfl, hn, hle, rfl, hr, hu, hav, rfl, hua, hnts, rfl⟩

end StakingPool
