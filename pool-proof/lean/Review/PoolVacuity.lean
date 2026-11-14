/-
  Adversarial review: non-vacuity of `StakingPool.exit_guarantee`.

  We build a concrete reachable world by real steps (`new`, two delegators'
  `deposit_and_stake`, protocol staking (`rebalance`), an epoch boundary, a validator reward
  (`income`), a third party's `ping`), instantiate `exit_guarantee` for delegator alice, pin
  down the existential `w1` (it must be alice's `unstake_all`), then build a concrete
  continuation `w2` without alice's calls (4 epoch boundaries, more rewards, another third
  party's `ping`, the protocol releasing alice's stake), check every hypothesis of the
  second half by kernel evaluation (`decide +kernel`, no `native_decide`), and obtain from
  the theorem a successful `withdraw_all` paying at least alice's claim (> 100 NEAR).
-/
import StakingPool
open StakingPool

namespace Review

def vk : String → Bool := fun _ => true
def poolId : AccountId := "pool.poolv1.near"
def NEAR : Nat := 1000000000000000000000000

/-- run one call (the world is unchanged if the call fails) -/
def runCall (w : World) (p : AccountId) (m : Method) (d : Nat) : World :=
  match exec vk w.c (w.env poolId p d) m with
  | .ok (c', eff) => w.afterCall d c' eff
  | .error _ => w

def callOk (w : World) (p : AccountId) (m : Method) (d : Nat) : Bool :=
  match exec vk w.c (w.env poolId p d) m with
  | .ok _ => true
  | .error _ => false

def effOf (w : World) (p : AccountId) (m : Method) (d : Nat) : Option Eff :=
  match exec vk w.c (w.env poolId p d) m with
  | .ok (_, eff) => some eff
  | .error _ => none

theorem step_runCall (w : World) (p : AccountId) (m : Method) (d : Nat)
    (h : callOk w p m d = true) : Step vk poolId (some p) w (runCall w p m d) := by
  unfold callOk at h; unfold runCall
  cases he : exec vk w.c (w.env poolId p d) m with
  | ok r => obtain ⟨c', eff⟩ := r; exact Step.call p m d he
  | error e => rw [he] at h; simp at h

/-- protocol: the pool's stake action lands, locking exactly the books' total -/
def lockBooks (w : World) : World :=
  { w with liquid := w.liquid + w.locked - w.c.s, locked := w.c.s }

theorem step_lockBooks (w : World) (h : w.c.s ≤ w.liquid + w.locked) :
    Step vk poolId none w (lockBooks w) := by
  have := Step.rebalance (vk := vk) (self := poolId) w (w.liquid + w.locked - w.c.s) w.c.s (by omega)
  exact this

/-- protocol: a validator reward of `x` lands on the locked balance (`income` with a = 0) -/
def reward (w : World) (x : Nat) : World := { w with liquid := w.liquid + 0, locked := w.locked + x }

theorem step_reward (w : World) (x : Nat) : Step vk poolId none w (reward w x) := Step.income w 0 x

/-! ## the initial pool (`new` from the factory with 30 NEAR) -/

def fee0 : Fee := ⟨10, 100⟩
def initEnv : Env :=
  { self := poolId, pred := "poolv1.near", epoch := 100, balance := 30 * NEAR, locked := 0, deposit := 0 }

def c0 : Contract :=
  { owner := "owner.near", key := "ed25519:K", lastEpoch := 100, ltb := 30 * NEAR,
    ts := 30 * NEAR - FUND, s := 30 * NEAR - FUND, fee := fee0, accts := Accts.empty, paused := false }

theorem init_ok : init vk initEnv "owner.near" "ed25519:K" fee0 = .ok (c0, { stake := some c0.s }) := by
  rfl

def wInit : World := World.init c0 100 (30 * NEAR)

theorem reach_init : Reach vk poolId wInit :=
  Reach.init "poolv1.near" "owner.near" "ed25519:K" fee0 100 (30 * NEAR) (by decide +kernel) init_ok

/-! ## history up to w0 -/

def wA : World := runCall wInit "alice.near" .depositAndStake (100 * NEAR)
def wB : World := lockBooks wA
def wC : World := runCall wB "bob.near" .depositAndStake (50 * NEAR)
def wD : World := lockBooks wC
def wE : World := wD.advance                        -- epoch 101
def wF : World := reward wE (2 * NEAR)              -- validator reward lands in locked
def w0 : World := runCall wF "carol.near" .ping 0   -- third party distributes it (10% fee)

theorem reach_w0 : Reach vk poolId w0 := by
  have hA : Reach vk poolId wA := Reach.step reach_init (step_runCall _ _ _ _ (by decide +kernel))
  have hB : Reach vk poolId wB := Reach.step hA (step_lockBooks _ (by decide +kernel))
  have hC : Reach vk poolId wC := Reach.step hB (step_runCall _ _ _ _ (by decide +kernel))
  have hD : Reach vk poolId wD := Reach.step hC (step_lockBooks _ (by decide +kernel))
  have hE : Reach vk poolId wE := Reach.step hD (Step.advance _)
  have hF : Reach vk poolId wF := Reach.step hE (step_reward _ _)
  exact Reach.step hF (step_runCall _ _ _ _ (by decide +kernel))

/-- alice's claim at w0 is more than her 100 NEAR deposit (she earned a reward share) -/
theorem claim_w0 : 100 * NEAR < claim w0.c "alice.near" := by decide +kernel

/-- alice holds stake at w0, so `w1 = w0` is impossible -/
theorem not_w0_branch : ¬ claim w0.c "alice.near" ≤ (w0.c.get "alice.near").unstaked := by
  decide +kernel

/-! ## after alice's unstake_all: a continuation without alice's calls -/

def W1 : World := runCall w0 "alice.near" .unstakeAll 0
def V1 : World := W1.advance                          -- 102
def V2 : World := reward V1 NEAR                       -- reward on the still-locked stake
def V3 : World := V2.advance                          -- 103
def V4 : World := runCall V3 "dave.near" .ping 0       -- third party distributes it
def V5 : World := V4.advance                          -- 104
def V6 : World := V5.advance                          -- 105 = 101 + 4
def W2 : World := lockBooks V6                         -- protocol released alice's stake

theorem others_W1_W2 : Others vk poolId "alice.near" W1 W2 := by
  have h1 : Others vk poolId "alice.near" W1 V1 := Others.step (Others.refl _) (Step.advance _) (by decide)
  have h2 : Others vk poolId "alice.near" W1 V2 := Others.step h1 (step_reward _ _) (by decide)
  have h3 : Others vk poolId "alice.near" W1 V3 := Others.step h2 (Step.advance _) (by decide)
  have h4 : Others vk poolId "alice.near" W1 V4 :=
    Others.step h3 (step_runCall _ _ _ _ (by decide +kernel)) (by decide)
  have h5 : Others vk poolId "alice.near" W1 V5 := Others.step h4 (Step.advance _) (by decide)
  have h6 : Others vk poolId "alice.near" W1 V6 := Others.step h5 (Step.advance _) (by decide)
  exact Others.step h6 (step_lockBooks _ (by decide +kernel)) (by decide)

theorem pua_W2 : PUA W2 := by decide +kernel
/-- PUA genuinely restricts the protocol: had it kept everything locked, PUA fails -/
theorem not_pua_V6 : ¬ PUA V6 := by decide +kernel
theorem ep_W2 : w0.epoch + NUM_EPOCHS_TO_UNLOCK ≤ W2.epoch := by decide +kernel
theorem n_W2 : W2.ncalls ≤ FUND := by decide +kernel
theorem b_W2 : W2.liquid + W2.locked ≤ U128_MAX := by decide +kernel

/-- **Non-vacuity.** The headline theorem fires on this world: its first half is alice's real
`unstake_all`, and its second half yields a successful `withdraw_all` paying more than 100 NEAR. -/
theorem exit_fires :
    ∃ c3 eff, exec vk W2.c (W2.env poolId "alice.near" 0) .withdrawAll = .ok (c3, eff) ∧
      100 * NEAR < eff.transfer := by
  obtain ⟨w1, hw1, _, hcl, hall⟩ :=
    exit_guarantee (vk := vk) (self := poolId) reach_w0 "alice.near"
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hw1' : w1 = W1 := by
    rcases hw1 with rfl | ⟨c', eff, hex, rfl⟩
    · exact absurd hcl not_w0_branch
    · show _ = runCall w0 "alice.near" .unstakeAll 0
      unfold runCall; rw [hex]
  subst hw1'
  obtain ⟨c3, eff, hex, hge⟩ := hall W2 others_W1_W2 ep_W2 pua_W2 n_W2 b_W2
    (Nat.lt_trans (by decide +kernel) claim_w0)
  exact ⟨c3, eff, hex, Nat.lt_of_lt_of_le claim_w0 hge⟩

/-- **PUA is load-bearing.** `V6` is reached from `W1` without alice's calls, at epoch
`w0.epoch + 4`, within all numeric bounds, but the protocol has not released her stake: there
`withdraw_all` fails ("Exceeded the account balance."). So the second half of `exit_guarantee`
is exactly as strong as the protocol assumption at the moment of withdrawal; the theorem says
nothing about when (or whether) a PUA world arrives. -/
theorem others_W1_V6 : Others vk poolId "alice.near" W1 V6 := by
  have h1 : Others vk poolId "alice.near" W1 V1 := Others.step (Others.refl _) (Step.advance _) (by decide)
  have h2 : Others vk poolId "alice.near" W1 V2 := Others.step h1 (step_reward _ _) (by decide)
  have h3 : Others vk poolId "alice.near" W1 V3 := Others.step h2 (Step.advance _) (by decide)
  have h4 : Others vk poolId "alice.near" W1 V4 :=
    Others.step h3 (step_runCall _ _ _ _ (by decide +kernel)) (by decide)
  have h5 : Others vk poolId "alice.near" W1 V5 := Others.step h4 (Step.advance _) (by decide)
  exact Others.step h5 (Step.advance _) (by decide)
theorem ep_V6 : w0.epoch + NUM_EPOCHS_TO_UNLOCK ≤ V6.epoch := by decide +kernel
theorem withdraw_fails_V6 : callOk V6 "alice.near" .withdrawAll 0 = false := by decide +kernel

/-! ## sanity: the concrete numbers (for the report) -/
#eval (claim w0.c "alice.near", (effOf W2 "alice.near" .withdrawAll 0).map (·.transfer),
       W2.epoch, W2.liquid, W2.locked, W2.c.s, W2.c.ltb)

end Review

#print axioms Review.exit_fires
