/-
  The exit guarantee: a delegator can always get its money back by its own calls.
-/
import StakingPool.World

namespace StakingPool

/-! ## Successful runs (existence) -/

theorem ok_bind' {α β} {a : α} {f : α → M β} : ((Except.ok a : M α) >>= f) = f a := rfl

theorem ensure_true {p : Prop} [Decidable p] {m : String} (h : p) : ensure p m = .ok () := by
  simp [ensure, h, pure, Except.pure]

theorem payOwner_ok_iff {c : Contract} {n : Nat} {r : Contract} :
    c.payOwner n = .ok r ↔ (c.get c.owner).stakeShares + n ≤ U128_MAX ∧ c.ts + n ≤ U128_MAX ∧
    r = { c.save c.owner ⟨(c.get c.owner).unstaked, (c.get c.owner).stakeShares + n, (c.get c.owner).availEpoch⟩
           with ts := c.ts + n } := by
  constructor
  · exact payOwner_spec
  · rintro ⟨h1, h2, rfl⟩
    simp only [Contract.payOwner, bind_ok, add128_ok, pure_ok]
    exact ⟨_, ⟨h1, rfl⟩, _, ⟨h2, rfl⟩, rfl⟩

theorem distribute_exists {c : Contract} {R : Nat} (hd : 0 < c.fee.den) (hn : c.fee.num ≤ c.fee.den)
    (hpr : c.ts ≤ c.s) (hts : 0 < c.ts) (hsh : (c.get c.owner).stakeShares ≤ c.ts)
    (hR : c.s + R ≤ U128_MAX) : ∃ r, c.distribute R = .ok r := by
  have hfee : c.fee.num * R / c.fee.den ≤ R := mul_div_le_of_le hd hn
  simp only [Contract.distribute, bind_ok, multiply_ok, sub128_ok, add128_ok, sharesDown_ok, pure_ok,
    ite_ok, payOwner_ok_iff]
  generalize hF : c.fee.num * R / c.fee.den = F at *
  have hsp : 0 < c.s + (R - F) := by omega
  have hnle : c.ts * F / (c.s + (R - F)) ≤ F := mul_div_le_of_le hsp (by omega)
  generalize hN : c.ts * F / (c.s + (R - F)) = n at *
  by_cases hnp : n > 0
  · refine ⟨_, _, ⟨by omega, by omega, rfl⟩, _, ⟨hfee, rfl⟩, _, ⟨by omega, rfl⟩, _,
      ⟨by omega, by omega, hN.symm⟩, _, Or.inl ⟨hnp, ?_, ?_, rfl⟩, _, ⟨?_, rfl⟩, rfl⟩
    · show (c.get c.owner).stakeShares + n ≤ _; omega
    · show c.ts + n ≤ _; omega
    · show c.s + (R - F) + F ≤ _; omega
  · refine ⟨_, _, ⟨by omega, by omega, rfl⟩, _, ⟨hfee, rfl⟩, _, ⟨by omega, rfl⟩, _,
      ⟨by omega, by omega, hN.symm⟩, _, Or.inr ⟨hnp, rfl⟩, _, ⟨?_, rfl⟩, rfl⟩
    show c.s + (R - F) + F ≤ _; omega

theorem ping_exists {c : Contract} {e : Env} (hc : CInv c) (hf : c.s ≤ c.ltb)
    (hb : e.locked + e.balance ≤ U128_MAX) (hl : c.ltb + e.deposit ≤ e.locked + e.balance) :
    ∃ r, c.ping e = .ok r := by
  unfold Contract.ping
  split
  · exact ⟨_, rfl⟩
  · simp only [bind_ok, add128_ok, sub128_ok, ensure_ok, pure_ok, ite_ok]
    have hsh := Nat.le_trans (sh_le_sum hc.wf c.owner) (Nat.le_of_lt hc.sh)
    by_cases hR : e.locked + e.balance - e.deposit - c.ltb > 0
    · obtain ⟨cd, hcd⟩ := distribute_exists (c := { c with lastEpoch := e.epoch })
        (R := e.locked + e.balance - e.deposit - c.ltb) hc.fee.1 hc.fee.2 hc.price
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hc.sh) hsh (by show c.s + _ ≤ _; omega)
      exact ⟨_, _, ⟨hb, rfl⟩, _, ⟨by omega, rfl⟩, (), by omega, cd, Or.inl ⟨hR, hcd⟩, rfl⟩
    · exact ⟨_, _, ⟨hb, rfl⟩, _, ⟨by omega, rfl⟩, (), by omega, _, Or.inr ⟨hR, rfl⟩, rfl⟩

theorem restake_exists {c : Contract} {vk : String → Bool} (hk : c.paused = false → vk c.key = true) :
    ∃ r, c.restake vk = .ok r := by
  cases hp : c.paused
  · exact ⟨_, restake_ok.2 (Or.inr ⟨hp, hk hp, rfl⟩)⟩
  · exact ⟨_, restake_ok.2 (Or.inl ⟨hp, rfl⟩)⟩

theorem unstakeInt_exists {c : Contract} {e : Env} {x : Nat} (hc : CInv c) (hx : 0 < x)
    (hsh : x * c.ts ≤ c.s * (c.get e.pred).stakeShares)
    (hU : (c.get e.pred).unstaked + c.s ≤ U128_MAX) (hs : c.s ≤ U128_MAX)
    (hE : e.epoch + NUM_EPOCHS_TO_UNLOCK ≤ U64_MAX) : ∃ r, c.unstakeInt e x = .ok r := by
  have hts : 0 < c.ts := Nat.lt_of_le_of_lt (Nat.zero_le _) hc.sh
  have hsp : 0 < c.s := Nat.lt_of_lt_of_le hts hc.price
  have hshts : (c.get e.pred).stakeShares < c.ts := Nat.lt_of_le_of_lt (sh_le_sum hc.wf e.pred) hc.sh
  -- n = ceil(ts * x / s)
  have hn_le : (c.ts * x + (c.s - 1)) / c.s ≤ (c.get e.pred).stakeShares := by
    calc (c.ts * x + (c.s - 1)) / c.s ≤ (c.s * (c.get e.pred).stakeShares + (c.s - 1)) / c.s :=
          Nat.div_le_div_right (by rw [Nat.mul_comm c.ts]; omega)
      _ = (c.get e.pred).stakeShares := cdiv_mul_self hsp
  have hn_pos : 0 < (c.ts * x + (c.s - 1)) / c.s := by
    apply (Nat.le_div_iff_mul_le hsp).2
    have : 1 ≤ c.ts * x := Nat.mul_pos hts hx
    omega
  generalize hn : (c.ts * x + (c.s - 1)) / c.s = n at hn_le hn_pos
  have hnts : n ≤ c.ts := by omega
  have hr_le : (c.s * n + (c.ts - 1)) / c.ts ≤ c.s := by
    calc (c.s * n + (c.ts - 1)) / c.ts ≤ (c.ts * c.s + (c.ts - 1)) / c.ts :=
          Nat.div_le_div_right (by rw [Nat.mul_comm c.ts]; have := Nat.mul_le_mul_left c.s hnts; omega)
      _ = c.s := cdiv_mul_self hts
  have hr_pos : 0 < (c.s * n + (c.ts - 1)) / c.ts := by
    apply (Nat.le_div_iff_mul_le hts).2
    have : 1 ≤ c.s * n := Nat.mul_pos hsp hn_pos
    omega
  have hpr := hc.price
  have hua : c.s * n / c.ts ≤ c.s := by
    apply Nat.div_le_of_le_mul
    rw [Nat.mul_comm c.ts]; exact Nat.mul_le_mul_left _ hnts
  simp only [Contract.unstakeInt, bind_ok, ensure_ok, sharesUp_ok, amountUp_ok, amountDown_ok,
    add128_ok, add64_ok, sub128_ok, pure_ok]
  refine ⟨_, (), by omega, (), by omega, n, ⟨by omega, by omega, hn.symm⟩, (), by omega, (), hn_le,
    _, ⟨by omega, by omega, rfl⟩, (), by omega, _, ⟨by omega, rfl⟩, _, ⟨hE, rfl⟩, _,
    ⟨by show c.ts ≠ 0; omega, by show c.s * n / c.ts ≤ _; omega, rfl⟩, _, ⟨by show c.s * n / c.ts ≤ c.s; omega, rfl⟩,
    _, ⟨by show n ≤ c.ts; omega, rfl⟩, rfl⟩

theorem withdrawInt_exists {c : Contract} {e : Env} {x : Nat} (hx : x ≠ 0)
    (hu : x ≤ (c.get e.pred).unstaked) (hav : (c.get e.pred).availEpoch ≤ e.epoch)
    (hb : x ≤ e.balance) (hl : x ≤ c.ltb) : ∃ r, c.withdrawInt e x = .ok r := by
  simp only [Contract.withdrawInt, bind_ok, ensure_ok, sub128_ok, pure_ok]
  exact ⟨_, (), hx, (), hu, (), hav, (), hb, _, ⟨hl, rfl⟩, rfl⟩

/-! ## The delegator's own calls -/

/-- What `get_account_total_balance(u)` shows: unstaked + staked rounded down. -/
def claim (c : Contract) (u : AccountId) : Nat :=
  (c.get u).unstaked + c.s * (c.get u).stakeShares / c.ts

/-- the staked part of `get_account(u)` -/
def stakedView (c : Contract) (u : AccountId) : Nat := c.s * (c.get u).stakeShares / c.ts

/-- **Solvency.** In every reachable world (fewer than 10^12 calls so far) the pool account
really holds (liquid + locked) at least the books' total staked balance plus every
delegator's unstaked balance. -/
theorem solvency {vk : String → Bool} {self : AccountId} {w : World} (hR : Reach vk self w)
    (hn : w.ncalls ≤ FUND) : w.c.s + w.c.sumU ≤ w.liquid + w.locked := by
  have hw := hR.inv; have := hw.fund; have := hw.cons; omega

/-- the fund after a ping: the books cover the stake and every unstaked balance -/
theorem fund_le {vk : String → Bool} {w : World} (hw : WInv vk w) (hn : w.ncalls ≤ FUND) :
    w.c.s + w.c.sumU ≤ w.c.ltb := by have := hw.fund; omega

/-- ping never takes shares away from anybody (it only adds the owner's fee shares) -/
theorem ping_shares {c c1 : Contract} {e : Env} {b : Bool} (hc : CInv c) (h : c.ping e = .ok (c1, b))
    (u : AccountId) : (c.get u).stakeShares ≤ (c1.get u).stakeShares := by
  have h' : c.ping { e with pred := u ++ "!" } = .ok (c1, b) := h
  have hne : u ≠ u ++ "!" := by
    intro h; have := congrArg String.length h; simp [String.length_append] at this
  exact ((ping_rel hc h').1.frame u hne).2.2.1

/-- **`unstake_all` succeeds** for a delegator with a positive staked balance, in every
reachable world (balances within u128, fewer than 10^12 calls so far, epoch < 2^64 - 4), and
leaves it at least its whole `get_account_total_balance` as unstaked balance, unlocked after
`NUM_EPOCHS_TO_UNLOCK` epochs. -/
theorem unstake_all_ok {vk : String → Bool} {self : AccountId} {w : World} (hw : WInv vk w)
    (u : AccountId) (hn : w.ncalls ≤ FUND) (hB : w.liquid + w.locked ≤ U128_MAX)
    (hE : w.epoch + NUM_EPOCHS_TO_UNLOCK ≤ U64_MAX) (hpos : 0 < stakedView w.c u) :
    ∃ c' eff, exec vk w.c (w.env self u 0) .unstakeAll = .ok (c', eff) ∧
      claim w.c u ≤ (c'.get u).unstaked ∧
      (c'.get u).availEpoch = w.epoch + NUM_EPOCHS_TO_UNLOCK ∧ eff.transfer = 0 := by
  have hc := hw.c
  have hf := fund_le hw hn
  have hcons := hw.cons
  -- the ping
  obtain ⟨⟨c1, b⟩, hp⟩ := ping_exists (e := w.env self u 0) hc (by omega)
    (by simp only [World.env_locked, World.env_balance]; omega)
    (by simp only [World.env_locked, World.env_balance, World.env_deposit]; omega)
  obtain ⟨r1, kfp1, hU1, _, hl1, hle1, hb1, hacct⟩ := ping_rel hc hp
  have hc1 := r1.inv
  have hts1 : 0 < c1.ts := Nat.lt_of_le_of_lt (Nat.zero_le _) hc1.sh
  have hts : 0 < w.c.ts := Nat.lt_of_le_of_lt (Nat.zero_le _) hc.sh
  have hf1 : c1.s + c1.sumU ≤ c1.ltb := by omega
  have hltb1 : c1.ltb ≤ U128_MAX := by
    rcases hb1 with ⟨_, rfl⟩ | ⟨_, h2, _⟩
    · omega
    · simp only [World.env_locked, World.env_balance, World.env_deposit] at h2; omega
  -- the amount
  have hsh := ping_shares hc hp u
  have hval : stakedView w.c u ≤ c1.s * (c1.get u).stakeShares / c1.ts :=
    value_mono r1.price hts hts1 hsh
  have hamt_u : c1.s * (c1.get u).stakeShares / c1.ts ≤ U128_MAX := by
    have : c1.s * (c1.get u).stakeShares / c1.ts ≤ c1.s := by
      apply Nat.div_le_of_le_mul; rw [Nat.mul_comm c1.ts]
      exact Nat.mul_le_mul_left _ (Nat.le_of_lt (Nat.lt_of_le_of_lt (sh_le_sum hc1.wf u) hc1.sh))
    omega
  have hUu := u_le_sum hc1.wf u
  obtain ⟨c2, hu2⟩ := unstakeInt_exists (e := w.env self u 0) (x := c1.s * (c1.get u).stakeShares / c1.ts)
    hc1 (by omega) (Nat.div_mul_le_self _ _) (by simp only [World.env_pred]; omega) (by omega)
    (by simp only [World.env_epoch]; exact hE)
  obtain ⟨r2, kfp2, _, hfin⟩ := unstakeInt_rel hu2
  obtain ⟨hu2a, hu2b⟩ := hfin hc1
  obtain ⟨st, hst⟩ := restake_exists (c := c2) (vk := vk)
    (key_of_kfp (kfp1.trans kfp2) hw.key)
  have hamt : c1.amountDown (c1.get u).stakeShares = .ok (c1.s * (c1.get u).stakeShares / c1.ts) :=
    amountDown_ok.2 ⟨by omega, hamt_u, rfl⟩
  refine ⟨c2, { stake := st, reward := c1.s - w.c.s }, ?_, ?_, ?_, rfl⟩
  · simp only [exec, execBody,
      ensure_true (p := Method.payable .unstakeAll = true ∨ (w.env self u 0).deposit = 0) (Or.inr rfl),
      ok_bind', hp, World.env_pred, hamt, hu2, hst]
    rfl
  · simp only [World.env_pred] at hu2a
    have := (hacct u).1
    unfold claim; unfold stakedView at hval; omega
  · simp only [World.env_pred, World.env_epoch] at hu2b; exact hu2b

/-- **`withdraw_all` succeeds** for a delegator whose unstaking delay is over, in every
reachable world where the protocol-unlock assumption holds, and pays out its whole
unstaked balance. -/
theorem withdraw_all_ok {vk : String → Bool} {self : AccountId} {w : World} (hw : WInv vk w)
    (hpua : PUA w) (u : AccountId) (hn : w.ncalls ≤ FUND) (hB : w.liquid + w.locked ≤ U128_MAX)
    (hav : (w.c.get u).availEpoch ≤ w.epoch) (hpos : 0 < (w.c.get u).unstaked) :
    ∃ c' eff, exec vk w.c (w.env self u 0) .withdrawAll = .ok (c', eff) ∧
      eff.transfer = (w.c.get u).unstaked := by
  have hc := hw.c
  have hf := fund_le hw hn
  have hcons := hw.cons
  have hliq := liquid_covers hw hpua hn u hav
  obtain ⟨⟨c1, b⟩, hp⟩ := ping_exists (e := w.env self u 0) hc (by omega)
    (by simp only [World.env_locked, World.env_balance]; omega)
    (by simp only [World.env_locked, World.env_balance, World.env_deposit]; omega)
  obtain ⟨r1, kfp1, hU1, _, hl1, hle1, hb1, hacct⟩ := ping_rel hc hp
  have hc1 := r1.inv
  have hUu := u_le_sum hc1.wf u
  have hf1 : c1.s + c1.sumU ≤ c1.ltb := by omega
  have ha := hacct u
  obtain ⟨c2, hw2⟩ := withdrawInt_exists (c := c1) (e := w.env self u 0) (x := (c1.get u).unstaked)
    (by omega) (by simp only [World.env_pred]; exact Nat.le_refl _)
    (by simp only [World.env_pred, World.env_epoch]; omega)
    (by simp only [World.env_balance]; omega) (by omega)
  obtain ⟨_, kfp2, _⟩ := withdrawInt_rel hw2
  obtain ⟨st, hst⟩ : ∃ st, (if b = true then c2.restake vk else pure none) = Except.ok st := by
    cases b
    · exact ⟨none, rfl⟩
    · exact restake_exists (key_of_kfp (kfp1.trans kfp2) hw.key)
  refine ⟨c2, { transfer := (c1.get u).unstaked, stake := st, reward := c1.s - w.c.s }, ?_, ha.1⟩
  simp only [exec, execBody,
    ensure_true (p := Method.payable .withdrawAll = true ∨ (w.env self u 0).deposit = 0) (Or.inr rfl),
    ok_bind', hp, World.env_pred, hw2, hst]
  rfl

/-! ## Other accounts and the protocol cannot touch the delegator's account -/

/-- Steps that are not calls by `u`. -/
inductive Others (vk : String → Bool) (self u : AccountId) : World → World → Prop
  | refl (w : World) : Others vk self u w w
  | step {w1 w2 w3 : World} {a : Option AccountId} (h1 : Others vk self u w1 w2)
      (hs : Step vk self a w2 w3) (ha : a ≠ some u) : Others vk self u w1 w3

theorem Others.reach {vk : String → Bool} {self u : AccountId} {w1 w2 : World}
    (h : Others vk self u w1 w2) (h1 : Reach vk self w1) : Reach vk self w2 := by
  induction h with
  | refl => exact h1
  | step _ hs _ ih => exact Reach.step ih hs

/-- **No one else can decrease `u`'s balances.** A call by anybody else (including the
owner) leaves `u`'s unstaked balance and unlock epoch unchanged and never decreases its
shares (only the owner's shares grow, by its fee); the share price never decreases. -/
theorem others_call {vk : String → Bool} {c c' : Contract} {e : Env} {m : Method} {eff : Eff}
    (hc : CInv c) (hk : c.paused = false → vk c.key = true) (h : exec vk c e m = .ok (c', eff))
    (u : AccountId) (hu : u ≠ e.pred) :
    (c'.get u).unstaked = (c.get u).unstaked ∧ (c'.get u).availEpoch = (c.get u).availEpoch ∧
    (c.get u).stakeShares ≤ (c'.get u).stakeShares ∧
    (u ≠ c.owner → (c'.get u).stakeShares = (c.get u).stakeShares) ∧
    c.s * c'.ts ≤ c'.s * c.ts ∧ claim c u ≤ claim c' u := by
  obtain ⟨c1, pp, rest, _, _, _⟩ := exec_facts hc hk h
  obtain ⟨a1, b1, s1, o1⟩ := pp.rel.frame u hu
  obtain ⟨a2, b2, s2, o2⟩ := rest.frame u hu
  have hts : 0 < c.ts := Nat.lt_of_le_of_lt (Nat.zero_le _) hc.sh
  have hts' : 0 < c'.ts := Nat.lt_of_le_of_lt (Nat.zero_le _) rest.inv.sh
  have hprice : c.s * c'.ts ≤ c'.s * c.ts :=
    price_trans pp.rel.price rest.price (Nat.lt_of_le_of_lt (Nat.zero_le _) pp.rel.inv.sh)
  refine ⟨a2.trans a1, b2.trans b1, Nat.le_trans s1 s2, fun ho => ?_, hprice, ?_⟩
  · have ho1 : u ≠ c1.owner := by rw [pp.rel.owner]; exact ho
    rw [o2 ho1, o1 ho]
  · unfold claim
    have := value_mono hprice hts hts' (Nat.le_trans s1 s2)
    rw [a2.trans a1]; omega

theorem others_preserve {vk : String → Bool} {self u : AccountId} {w1 w2 : World}
    (h : Others vk self u w1 w2) (h1 : Reach vk self w1) :
    (w2.c.get u).unstaked = (w1.c.get u).unstaked ∧
    (w2.c.get u).availEpoch = (w1.c.get u).availEpoch ∧ w1.epoch ≤ w2.epoch ∧
    claim w1.c u ≤ claim w2.c u := by
  induction h with
  | refl => exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | step h12 hs ha ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have hr2 := h12.reach h1
    have hw2 := hr2.inv
    cases hs with
    | call p m d hcall =>
      have hpu : u ≠ p := fun he => ha (by rw [he])
      obtain ⟨a, b, _, _, _, cl⟩ := others_call hw2.c hw2.key hcall u (by simp only [World.env_pred]; exact hpu)
      simp only [World.afterCall]
      exact ⟨a.trans i1, b.trans i2, i3, Nat.le_trans i4 cl⟩
    | advance w => exact ⟨i1, i2, by simp only [World.advance]; omega, i4⟩
    | income w a b => exact ⟨i1, i2, i3, i4⟩
    | rebalance w a b _ => exact ⟨i1, i2, i3, i4⟩

/-! ## The exit theorem -/

/-- **Exit guarantee (T_exit).** Take any reachable state `w0` of the pool (any history of
calls by anybody, the owner included, and of protocol steps) and any delegator `u`.
Then `u`, by its own calls only, gets at least `get_account_total_balance(u)` of `w0` back:

* if its staked balance is positive, `unstake_all` succeeds at `w0`;
* afterwards, whatever the other accounts and the protocol do, at any epoch at least
  `NUM_EPOCHS_TO_UNLOCK = 4` after `w0` at which the protocol has released the stake
  (`PUA`), `withdraw_all` succeeds and transfers to `u` at least that amount.

Side conditions: the pool's balance fits in u128 (NEAR's total supply is ~2^110), the epoch
height is below 2^64 - 4, and fewer than 10^12 calls have been made to the pool in total
(each call may use one yocto of the 10^12-yocto price-guarantee fund). There is no rounding
loss at all: the rounding of `unstake` is paid by the fund, not by the delegator. -/
theorem exit_guarantee {vk : String → Bool} {self : AccountId} {w0 : World}
    (hR : Reach vk self w0) (u : AccountId)
    (hN : w0.ncalls < FUND) (hB : w0.liquid + w0.locked ≤ U128_MAX)
    (hE : w0.epoch + NUM_EPOCHS_TO_UNLOCK ≤ U64_MAX) :
    ∃ w1, (w1 = w0 ∨ ∃ c' eff, exec vk w0.c (w0.env self u 0) .unstakeAll = .ok (c', eff) ∧
                                w1 = w0.afterCall 0 c' eff) ∧ Reach vk self w1 ∧
      claim w0.c u ≤ (w1.c.get u).unstaked ∧
      ∀ w2, Others vk self u w1 w2 →
        w0.epoch + NUM_EPOCHS_TO_UNLOCK ≤ w2.epoch → PUA w2 →
        w2.ncalls ≤ FUND → w2.liquid + w2.locked ≤ U128_MAX → 0 < claim w0.c u →
        ∃ c3 eff, exec vk w2.c (w2.env self u 0) .withdrawAll = .ok (c3, eff) ∧
          claim w0.c u ≤ eff.transfer := by
  have hw0 := hR.inv
  -- step 1: unstake_all (or nothing to unstake)
  obtain ⟨w1, hw1, hR1, hcl, hav1⟩ : ∃ w1, (w1 = w0 ∨ ∃ c' eff, exec vk w0.c (w0.env self u 0)
      .unstakeAll = .ok (c', eff) ∧ w1 = w0.afterCall 0 c' eff) ∧ Reach vk self w1 ∧
      claim w0.c u ≤ (w1.c.get u).unstaked ∧ (w1.c.get u).availEpoch ≤ w0.epoch + NUM_EPOCHS_TO_UNLOCK := by
    by_cases hpos : 0 < stakedView w0.c u
    · obtain ⟨c', eff, hex, hcl, hav, _⟩ := unstake_all_ok (self := self) hw0 u (by omega) hB hE hpos
      have hs := Step.call (vk := vk) (self := self) (w := w0) u .unstakeAll 0 hex
      exact ⟨_, Or.inr ⟨c', eff, hex, rfl⟩, Reach.step hR hs, hcl, by simp only [World.afterCall]; omega⟩
    · refine ⟨w0, Or.inl rfl, hR, ?_, hw0.avail u⟩
      unfold claim; unfold stakedView at hpos; omega
  refine ⟨w1, hw1, hR1, hcl, fun w2 hO hep hpua hn2 hB2 hclpos => ?_⟩
  -- step 2: withdraw_all
  have hR2 := hO.reach hR1
  have hw2 := hR2.inv
  obtain ⟨p1, p2, p3, _⟩ := others_preserve hO hR1
  obtain ⟨c3, eff, hex, htr⟩ := withdraw_all_ok (self := self) hw2 hpua u hn2 hB2
    (by rw [p2]; omega) (by rw [p1]; omega)
  exact ⟨c3, eff, hex, by rw [htr, p1]; exact hcl⟩

end StakingPool
