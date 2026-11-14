/-
  The pool together with its environment: the protocol (epochs, liquid and locked
  balance, rewards, stake locking/unlocking) and any number of other accounts calling
  the contract. Reachability, and the global invariant `WInv` of every reachable world.
-/
import StakingPool.Methods

namespace StakingPool

/-- The pool contract plus what the protocol keeps for the pool account.
`hist` and `ncalls` are ghost variables (never read by the contract). -/
structure World where
  c : Contract
  /-- current epoch height -/
  epoch : Nat
  /-- the pool account's liquid balance (`amount`) -/
  liquid : Nat
  /-- the pool account's locked (staked) balance -/
  locked : Nat
  /-- ghost: `hist j` bounds what the pool may still have locked because of the stake it
  requested in epoch `j` (the pool's books' total staked balance during epoch `j`, plus
  every reward distributed since, since rewards accrue on a stake still in force) -/
  hist : Nat → Nat
  /-- ghost: number of successful function calls so far -/
  ncalls : Nat

/-- What a function call by `pred` with attached deposit `d` reads. -/
def World.env (w : World) (self pred : AccountId) (d : Nat) : Env :=
  { self := self, pred := pred, epoch := w.epoch, balance := w.liquid + d, locked := w.locked,
    deposit := d }

/-- ghost update after a successful call in epoch `k`: the reward `rw` the call's ping
distributed accrues on every stake still in force (epochs `k-3 .. k`), and the new books'
total `s'` is the stake requested now. -/
def callHist (hist : Nat → Nat) (k rw s' : Nat) : Nat → Nat :=
  fun j =>
    let h := if j ≤ k ∧ k ≤ j + 3 then hist j + rw else hist j
    if j = k then max h s' else h

@[simp] theorem World.env_epoch (w : World) (self pred : AccountId) (d : Nat) :
    (w.env self pred d).epoch = w.epoch := rfl
@[simp] theorem World.env_balance (w : World) (self pred : AccountId) (d : Nat) :
    (w.env self pred d).balance = w.liquid + d := rfl
@[simp] theorem World.env_locked (w : World) (self pred : AccountId) (d : Nat) :
    (w.env self pred d).locked = w.locked := rfl
@[simp] theorem World.env_deposit (w : World) (self pred : AccountId) (d : Nat) :
    (w.env self pred d).deposit = d := rfl
@[simp] theorem World.env_pred (w : World) (self pred : AccountId) (d : Nat) :
    (w.env self pred d).pred = pred := rfl

def World.afterCall (w : World) (d : Nat) (c' : Contract) (eff : Eff) : World :=
  { w with c := c', liquid := w.liquid + d - eff.transfer,
           hist := callHist w.hist w.epoch eff.reward c'.s, ncalls := w.ncalls + 1 }

/-- an epoch boundary: the stake in force entering the new epoch is the books' total -/
def World.advance (w : World) : World :=
  { w with epoch := w.epoch + 1, hist := fun j => if j = w.epoch + 1 then w.c.s else w.hist j }

/-- Environment and other users. A failed call changes nothing (the runtime reverts it
and refunds the deposit), so only successful calls are steps. The protocol may move
balance between liquid and locked arbitrarily (stake actions, unlocking, kick-outs) and may
add income (validator rewards, plain transfers to the pool); it never removes balance —
the pool account has no access keys and its code sends NEAR only through `withdraw`. -/
inductive Step (vk : String → Bool) (self : AccountId) : Option AccountId → World → World → Prop
  | call {w : World} (p : AccountId) (m : Method) (d : Nat) {c' : Contract} {eff : Eff}
      (h : exec vk w.c (w.env self p d) m = .ok (c', eff)) :
      Step vk self (some p) w (w.afterCall d c' eff)
  | advance (w : World) : Step vk self none w w.advance
  | income (w : World) (a b : Nat) :
      Step vk self none w { w with liquid := w.liquid + a, locked := w.locked + b }
  | rebalance (w : World) (a b : Nat) (h : a + b = w.liquid + w.locked) :
      Step vk self none w { w with liquid := a, locked := b }

def World.init (c : Contract) (epoch bal : Nat) : World :=
  ⟨c, epoch, bal, 0, fun _ => c.s, 0⟩

/-- Worlds reachable from the pool's initialisation (`new` on an account holding `bal`
yocto with nothing staked; the factory requires 30 NEAR, we only need `bal > 10^12`) by any
sequence of successful calls by anybody and protocol steps. -/
inductive Reach (vk : String → Bool) (self : AccountId) : World → Prop
  | init (pred owner key : AccountId) (fee : Fee) (epoch bal : Nat) {c : Contract} {eff : Eff}
      (hbal : FUND < bal)
      (h : init vk { self := self, pred := pred, epoch := epoch, balance := bal, locked := 0,
                     deposit := 0 } owner key fee = .ok (c, eff)) :
      Reach vk self (World.init c epoch bal)
  | step {w w' : World} {a : Option AccountId} (hw : Reach vk self w) (hs : Step vk self a w w') :
      Reach vk self w'

/-- maximum of the ghost window over the last four epochs -/
def maxWin (hist : Nat → Nat) (k : Nat) : Nat :=
  max (hist k) (max (hist (k - 1)) (max (hist (k - 2)) (hist (k - 3))))

/-- **Protocol unlock assumption** (PUA), at a given moment: the pool's locked balance is
at most the largest stake the pool requested during the last four epochs (with the rewards
accrued on it since), plus income the contract has not yet distributed. This is what
NEAR's rule "a lowered stake is returned at the start of the third epoch after the epoch
the proposal counts in" gives, as long as the pool's stake receipts land at most one epoch
boundary after the call that issued them (`NUM_EPOCHS_TO_UNLOCK = 4 > 3`). -/
def PUA (w : World) : Prop :=
  w.locked ≤ maxWin w.hist w.epoch + (w.liquid + w.locked - w.c.ltb)

instance (w : World) : Decidable (PUA w) := inferInstanceAs (Decidable (_ ≤ _))

/-- The global invariant. -/
structure WInv (vk : String → Bool) (w : World) : Prop where
  c : CInv w.c
  key : w.c.paused = false → vk w.c.key = true
  /-- the price-guarantee fund: books' stake + all unstaked balances never exceed the books'
  total by more than one yocto per call made so far (it starts 10^12 yocto below) -/
  fund : w.c.s + w.c.sumU + FUND ≤ w.c.ltb + w.ncalls
  /-- the books' total never exceeds what the account really holds -/
  cons : w.c.ltb ≤ w.liquid + w.locked
  avail : ∀ k, (w.c.get k).availEpoch ≤ w.epoch + NUM_EPOCHS_TO_UNLOCK
  /-- the stake still in force from epoch `j` is covered by the books' stake plus the
  unstaked balances still in their unstaking delay -/
  win : ∀ j, j ≤ w.epoch → w.epoch ≤ j + 3 → w.hist j ≤ w.c.s + w.c.cool (j + 3)

theorem init_spec {vk : String → Bool} {e : Env} {owner key : AccountId} {fee : Fee} {c : Contract}
    {eff : Eff} (h : init vk e owner key fee = .ok (c, eff)) :
    FUND ≤ e.balance ∧ e.locked = 0 ∧ 0 < fee.den ∧ fee.num ≤ fee.den ∧ vk key = true ∧
    c = { owner := owner, key := key, lastEpoch := e.epoch, ltb := e.balance, ts := e.balance - FUND,
          s := e.balance - FUND, fee := fee, accts := Accts.empty, paused := false } := by
  unfold StakingPool.init at h
  simp only [bind_ok] at h
  obtain ⟨_, _, _, hf, _, _, s, hs, _, hl, st, hr, hfin⟩ := h
  obtain ⟨hd, hn⟩ := assertValid_ok.1 hf
  obtain ⟨hs, hseq⟩ := sub128_ok.1 hs
  have hl := ensure_ok.1 hl
  simp only [pure_ok, Prod.mk.injEq] at hfin
  obtain ⟨hc, _⟩ := hfin
  rcases restake_ok.1 hr with ⟨hp, _⟩ | ⟨_, hk, _⟩
  · simp at hp
  · refine ⟨hs, hl, Nat.pos_of_ne_zero hd, hn, hk, ?_⟩
    rw [← hc, hseq]

theorem cool_anti (c : Contract) {k t : Nat} (h : k ≤ t) : c.cool t ≤ c.cool k :=
  Accts.sum_le _ (fun a => by unfold gCool; split <;> split <;> omega)

theorem Reach.inv {vk : String → Bool} {self : AccountId} {w : World} (hw : Reach vk self w) :
    WInv vk w := by
  induction hw with
  | init pred owner key fee epoch bal hbal h =>
    obtain ⟨_, _, hd, hn, hk, rfl⟩ := init_spec h
    have hU : Accts.empty.sum gU = 0 := rfl
    have hS : Accts.empty.sum gSh = 0 := rfl
    exact { c := ⟨Accts.WF.empty, by simp only [Contract.sumSh, World.init] at *; rw [hS]; omega,
                  Nat.le_refl _, hd, hn⟩
            key := fun _ => hk
            fund := by simp only [Contract.sumU, World.init]; rw [hU]; omega
            cons := by simp only [World.init]; omega
            avail := fun k => Nat.zero_le _
            win := fun j _ _ => Nat.le_add_right _ _ }
  | step hw hs ih =>
    cases hs with
    | call p m d h =>
      obtain ⟨c1, pp, rest, key, books, tr⟩ := exec_facts ih.c ih.key h
      have f1 := ih.fund; have f2 := pp.ltb; have f3 := pp.sumU; have f4 := rest.fund
      have g1 := ih.cons
      exact {
        c := rest.inv
        key := key
        fund := by simp only [World.afterCall]; omega
        cons := by
          simp only [World.afterCall]
          simp only [World.env_deposit, World.env_balance, World.env_locked] at books tr
          rcases pp.books with hb | hb <;>
            (try simp only [World.env_deposit, World.env_balance, World.env_locked] at hb) <;> omega
        avail := fun k => by
          simp only [World.afterCall]
          have a1 := rest.avail k; have a2 := (pp.acct k).2; have a3 := ih.avail k
          simp only [World.env_epoch, Nat.max_def] at a1
          split at a1 <;> omega
        win := fun j hj1 hj2 => by
          simp only [World.afterCall] at hj1 hj2
          simp only [World.afterCall, callHist]
          have hw := ih.win j hj1 hj2
          have hm := rest.mono (j + 3) (by simp only [World.env_epoch]; omega)
            (by simp only [World.env_epoch]; omega)
          have hs1 := pp.s; have hc1 := pp.cool (j + 3)
          have hwin := And.intro hj1 hj2
          simp only [hwin, and_self, ite_true]
          split
          · exact Nat.max_le.2 ⟨by omega, Nat.le_add_right _ _⟩
          · omega }
    | advance w =>
      exact { c := ih.c, key := ih.key, fund := ih.fund, cons := ih.cons
              avail := fun k => by have := ih.avail k; simp only [World.advance]; omega
              win := fun j hj1 hj2 => by
                simp only [World.advance] at *
                split
                · exact Nat.le_add_right _ _
                · exact ih.win j (by omega) (by omega) }
    | income w a b =>
      exact { c := ih.c, key := ih.key, fund := ih.fund, cons := by have := ih.cons; simp only; omega
              avail := ih.avail, win := ih.win }
    | rebalance w a b h =>
      exact { c := ih.c, key := ih.key, fund := ih.fund, cons := by have := ih.cons; simp only; omega
              avail := ih.avail, win := ih.win }

/-- The window bound: everything the protocol may still keep locked is covered by the books'
stake plus balances still in their unstaking delay at the current epoch. -/
theorem WInv.maxWin_le {vk : String → Bool} {w : World} (hw : WInv vk w) :
    maxWin w.hist w.epoch ≤ w.c.s + w.c.cool w.epoch := by
  have h : ∀ i, i ≤ 3 → w.hist (w.epoch - i) ≤ w.c.s + w.c.cool w.epoch := by
    intro i hi
    have h1 := hw.win (w.epoch - i) (by omega) (by omega)
    have h2 := cool_anti w.c (show w.epoch ≤ w.epoch - i + 3 by omega)
    omega
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [Nat.sub_zero] at h0
  simp only [maxWin, Nat.max_def]
  split <;> split <;> split <;> omega

/-- unstaked balances split into "still cooling at epoch k" and "available at epoch k" -/
theorem sumU_split (c : Contract) (k : Nat) : c.sumU = c.cool k + c.accts.sum (gAvail k) := by
  simp only [Contract.sumU, Contract.cool]
  rw [← Accts.sum_add]
  unfold Accts.sum
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [gU, gCool, gAvail]; split <;> omega

/-- **Liquidity.** In every reachable world where the protocol-unlock assumption holds (and
fewer than 10^12 calls have consumed the price-guarantee fund), the pool's liquid balance
covers the unstaked balance of any account whose unstaking delay is over. -/
theorem liquid_covers {vk : String → Bool} {w : World} (hw : WInv vk w) (hpua : PUA w)
    (hn : w.ncalls ≤ FUND) (u : AccountId) (hu : (w.c.get u).availEpoch ≤ w.epoch) :
    (w.c.get u).unstaked ≤ w.liquid := by
  have hm := hw.maxWin_le
  have hsplit := sumU_split w.c w.epoch
  have hav : gAvail w.epoch (w.c.get u) ≤ w.c.accts.sum (gAvail w.epoch) :=
    Accts.le_sum hw.c.wf u (by simp [gAvail, Account.zero])
  have hav' : gAvail w.epoch (w.c.get u) = (w.c.get u).unstaked := by
    simp only [gAvail]; split <;> omega
  have := hw.fund; have := hw.cons
  unfold PUA at hpua
  omega

end StakingPool
