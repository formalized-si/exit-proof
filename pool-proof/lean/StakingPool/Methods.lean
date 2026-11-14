/-
  Method level: every successful public call is `internal_ping` (state `c → c1`)
  followed by internal steps (`c1 → c'`) that satisfy `RelC` with at most one unit of
  rounding, plus the facts about the key, the books (`ltb`) and the transfer.
-/
import StakingPool.Facts

namespace StakingPool

/-- What a successful `internal_ping` did (or the identity, for methods without ping). -/
structure PingPart (e : Env) (c c1 : Contract) (reward : Nat) : Prop where
  rel : RelC e c c1 0
  kfp : KFP c c1
  s : c1.s = c.s + reward
  sumU : c1.sumU = c.sumU
  cool : ∀ t, c1.cool t = c.cool t
  ltb : c1.s + c.ltb = c.s + c1.ltb
  books : c1.ltb = c.ltb ∨ c1.ltb + e.deposit = e.locked + e.balance
  acct : ∀ k, (c1.get k).unstaked = (c.get k).unstaked ∧ (c1.get k).availEpoch = (c.get k).availEpoch

theorem PingPart.refl (e : Env) (c : Contract) (hc : CInv c) : PingPart e c c 0 :=
  { rel := Rel.refl e c hc, kfp := ⟨rfl, rfl, rfl⟩, s := rfl, sumU := rfl, cool := fun _ => rfl,
    ltb := rfl, books := Or.inl rfl, acct := fun _ => ⟨rfl, rfl⟩ }

theorem PingPart.of_ping {c c1 : Contract} {e : Env} {b : Bool} (hc : CInv c)
    (h : c.ping e = .ok (c1, b)) : PingPart e c c1 (c1.s - c.s) := by
  obtain ⟨r, kfp, hU, hC, hl, hle, hb, hacct⟩ := ping_rel hc h
  refine { rel := r, kfp := kfp, s := by omega, sumU := hU, cool := hC, ltb := hl, books := ?_, acct := hacct }
  rcases hb with ⟨_, rfl⟩ | ⟨_, h2, _⟩
  · exact Or.inl rfl
  · exact Or.inr h2

/-- The summary of one successful public call. -/
def CallFacts (vk : String → Bool) (e : Env) (c c' : Contract) (eff : Eff) : Prop :=
  ∃ c1, PingPart e c c1 eff.reward ∧ RelC e c1 c' 1 ∧ (c'.paused = false → vk c'.key = true) ∧
    c'.ltb + eff.transfer ≤ c1.ltb + e.deposit ∧ eff.transfer ≤ e.balance

/-- setting fee / key / paused -/
theorem setter_rel (e : Env) {c c' : Contract} (hc : CInv c) (hs : c'.s = c.s) (hts : c'.ts = c.ts)
    (hl : c'.ltb = c.ltb) (ha : c'.accts = c.accts) (ho : c'.owner = c.owner)
    (hf : 0 < c'.fee.den ∧ c'.fee.num ≤ c'.fee.den) : RelC e c c' 0 := by
  have hg : ∀ k, c'.get k = c.get k := fun k => by show c'.accts.get k = _; rw [ha]; rfl
  have hU : c'.sumU = c.sumU := by simp only [Contract.sumU]; rw [ha]
  have hS : c'.sumSh = c.sumSh := by simp only [Contract.sumSh]; rw [ha]
  have hC : ∀ t, c'.cool t = c.cool t := fun t => by simp only [Contract.cool]; rw [ha]
  have := hc.sh; have := hc.price
  exact { inv := ⟨by rw [ha]; exact hc.wf, by omega, by omega, hf⟩
          fund := by omega
          avail := fun id => by rw [hg]; exact Nat.le_max_left _ _
          mono := fun t _ _ => by rw [hC, hs]; exact Nat.le_refl _
          price := by rw [hs, hts]; exact Nat.le_refl _
          frame := fun u _ => by rw [hg]; exact ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl⟩
          owner := ho }

theorem RelC.weaken {e : Env} {c c' : Contract} {r r' : Nat} (h : RelC e c c' r) (hr : r ≤ r') :
    RelC e c c' r' := { h with fund := by have := h.fund; omega }

theorem RelC.trans {e : Env} {c1 c2 c3 : Contract} {r1 r2 : Nat} (a : RelC e c1 c2 r1)
    (b : RelC e c2 c3 r2) : RelC e c1 c3 (r1 + r2) :=
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

theorem RelC.then {e : Env} {c1 c2 c3 : Contract} {r1 r2 : Nat} (a : RelC e c1 c2 r1)
    (b : Rel e c2 c3 r2) : RelC e c1 c3 (r1 + r2) := a.trans (b a.inv)

theorem restake_key {c : Contract} {vk : String → Bool} {st : Option Nat}
    (h : c.restake vk = .ok st) : c.paused = false → vk c.key = true := by
  intro hp; rcases restake_ok.1 h with ⟨h1, _⟩ | ⟨_, h2, _⟩
  · rw [hp] at h1; exact absurd h1 (by decide)
  · exact h2

theorem key_of_kfp {vk : String → Bool} {c c' : Contract} (h : KFP c c')
    (hk : c.paused = false → vk c.key = true) : c'.paused = false → vk c'.key = true := by
  intro hp; rw [h.2.1]; exact hk (h.2.2 ▸ hp)

theorem KFP.trans {c1 c2 c3 : Contract} (a : KFP c1 c2) (b : KFP c2 c3) : KFP c1 c3 :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.trans a.2.2⟩

/-- Every successful public call satisfies `CallFacts`. -/
theorem exec_facts {vk : String → Bool} {c c' : Contract} {e : Env} {m : Method} {eff : Eff}
    (hc : CInv c) (hk : c.paused = false → vk c.key = true)
    (h : exec vk c e m = .ok (c', eff)) : CallFacts vk e c c' eff := by
  simp only [exec, bind_ok, ensure_ok] at h
  obtain ⟨_, hpay, h⟩ := h
  cases m with
  | ping =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    exact ⟨c1, pp, (Rel.refl e c1 pp.rel.inv).weaken (Nat.zero_le _), key_of_kfp pp.kfp hk,
      by show c1.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | deposit =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨⟨c2, amt⟩, hd, h⟩ := h; simp only at h
    obtain ⟨st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, _, hl, _⟩ := depositInt_rel hd
    exact ⟨c1, pp, (r pp.rel.inv).weaken (Nat.zero_le _), key_of_kfp (pp.kfp.trans kfp) hk,
      by show c2.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | depositAndStake =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨⟨c2, amt⟩, hd, h⟩ := h; simp only at h
    obtain ⟨c3, hs, st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, _, hl, _⟩ := depositInt_rel hd
    obtain ⟨r2, kfp2, hl2⟩ := stakeInt_rel hs
    have rc := (r pp.rel.inv).then r2
    exact ⟨c1, pp, rc.weaken (by omega), key_of_kfp ((pp.kfp.trans kfp).trans kfp2) hk,
      by show c3.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | withdrawAll =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨c2, hw, st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, hbal, hl, _⟩ := withdrawInt_rel hw
    exact ⟨c1, pp, (r pp.rel.inv).weaken (Nat.zero_le _), key_of_kfp (pp.kfp.trans kfp) hk,
      by show c2.ltb + (c1.get e.pred).unstaked ≤ _; omega, hbal⟩
  | withdraw amount =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨c2, hw, st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, hbal, hl, _⟩ := withdrawInt_rel hw
    exact ⟨c1, pp, (r pp.rel.inv).weaken (Nat.zero_le _), key_of_kfp (pp.kfp.trans kfp) hk,
      by show c2.ltb + amount ≤ _; omega, hbal⟩
  | stakeAll =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨c2, hs, st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, hl⟩ := stakeInt_rel hs
    exact ⟨c1, pp, r pp.rel.inv, key_of_kfp (pp.kfp.trans kfp) hk,
      by show c2.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | stake amount =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨c2, hs, st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, hl⟩ := stakeInt_rel hs
    exact ⟨c1, pp, r pp.rel.inv, key_of_kfp (pp.kfp.trans kfp) hk,
      by show c2.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | unstakeAll =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨amt, _, c2, hs, st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, hl, _⟩ := unstakeInt_rel hs
    exact ⟨c1, pp, r pp.rel.inv, key_of_kfp (pp.kfp.trans kfp) hk,
      by show c2.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | unstake amount =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨c2, hs, st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    obtain ⟨r, kfp, hl, _⟩ := unstakeInt_rel hs
    exact ⟨c1, pp, r pp.rel.inv, key_of_kfp (pp.kfp.trans kfp) hk,
      by show c2.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | updateStakingKey k =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨_, _, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨st, hr, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    have hc1 := pp.rel.inv
    exact ⟨c1, pp, (setter_rel (c' := { c1 with key := k }) e hc1 rfl rfl rfl rfl rfl hc1.fee).weaken
      (Nat.zero_le _), restake_key hr, by show c1.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | updateFee f =>
    simp only [execBody, bind_ok, pure_ok] at h
    obtain ⟨_, _, _, hf, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨st, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    have hc1 := pp.rel.inv
    obtain ⟨hf1, hf2⟩ := assertValid_ok.1 hf
    exact ⟨c1, pp, (setter_rel (c' := { c1 with fee := f }) e hc1 rfl rfl rfl rfl rfl
      ⟨Nat.pos_of_ne_zero hf1, hf2⟩).weaken (Nat.zero_le _),
      fun hp => (key_of_kfp (c' := c1) pp.kfp hk) hp, by show c1.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | vote acct isVote =>
    simp only [execBody, bind_ok, pure_ok, ensure_ok] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    exact ⟨c, PingPart.refl e c hc, (Rel.refl e c hc).weaken (Nat.zero_le _), hk,
      by show c.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | pauseStaking =>
    simp only [execBody, bind_ok, pure_ok, ensure_ok] at h
    obtain ⟨_, _, _, _, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨_, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    have hc1 := pp.rel.inv
    exact ⟨c1, pp, (setter_rel (c' := { c1 with paused := true }) e hc1 rfl rfl rfl rfl rfl hc1.fee).weaken
      (Nat.zero_le _), fun h => by simp at h, by show c1.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | resumeStaking =>
    simp only [execBody, bind_ok, pure_ok, ensure_ok] at h
    obtain ⟨_, _, _, _, ⟨c1, b⟩, hp, h⟩ := h; simp only at h
    obtain ⟨st, hr, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    have pp := PingPart.of_ping hc hp
    have hc1 := pp.rel.inv
    exact ⟨c1, pp, (setter_rel (c' := { c1 with paused := false }) e hc1 rfl rfl rfl rfl rfl hc1.fee).weaken
      (Nat.zero_le _), restake_key hr, by show c1.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | onStakeAction =>
    simp only [execBody, bind_ok, pure_ok, ensure_ok] at h
    obtain ⟨_, _, heq⟩ := h
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    exact ⟨c, PingPart.refl e c hc, (Rel.refl e c hc).weaken (Nat.zero_le _), hk,
      by show c.ltb + 0 ≤ _; omega, Nat.zero_le _⟩
  | reinit =>
    simp [execBody, throw_ok] at h

end StakingPool
