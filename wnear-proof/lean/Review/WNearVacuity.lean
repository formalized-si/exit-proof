/-
  Adversarial review: non-vacuity of `WNear.exit_always` / `T_exit` and the shape of
  `T_no_one_else`.

  * `E` uses mainnet numbers (minBal = 125 bytes * 1e19, entry = (61 + len) * 1e19). Note that
    `Env.Sane.entry_le : ∀ a, E.entry a ≤ E.minBal` quantifies over *all* strings, so the
    literal mainnet formula violates it for ids longer than 64 bytes; it has to be capped
    (`min … minBal`). Harmless (such ids can never be registered on NEAR), but `Sane` is not
    literally "the mainnet constants".
  * The reachable state is built by real steps: `new()`, alice `near_deposit`, bob
    `storage_deposit`, alice `ft_transfer_call` to bob (callback in flight), a third party's
    plain NEAR transfer to wrap.near (`nearIn`), the callback with bob's contract reporting
    1 NEAR unused (partial refund), carol registering and receiving tokens.
  * `exit_always` is then instantiated for bob with a positive balance.
  * Precision example: a callback still in flight for a transfer *to* bob can lower bob's
    balance, so `near_withdraw(b)` signed against the balance bob saw may fail when the
    refund lands first; the theorem is about the balance at execution time.
-/
import WNear
open WNear

namespace Review

def NEAR : Nat := 1000000000000000000000000
def BYTE : Nat := 10000000000000000000

def E : Env :=
  { self := "wrap.near", minBal := 125 * BYTE, base := 200000 * BYTE,
    entry := fun a => min ((61 + a.utf8ByteSize) * BYTE) (125 * BYTE),
    cap := 2 ^ 127 }

theorem sane : E.Sane :=
  ⟨by decide +kernel, fun _ => Nat.min_le_right _ _, by decide +kernel, by decide +kernel⟩

def S0 : Sys := ⟨⟨[], 0, 3 * NEAR⟩, [], []⟩
theorem reach0 : Reach E S0 := Reach.init _ (by decide +kernel) (by decide +kernel)

def S1 : Sys := sysStep E S0 (.call "alice.near" (10 * NEAR) .near_deposit [])
def S2 : Sys := sysStep E S1 (.call "bob.near" (125 * BYTE) (.storage_deposit none) [])
def S3 : Sys := sysStep E S2 (.call "alice.near" 1 (.ft_transfer_call "bob.near" (4 * NEAR)) [])
def S4 : Sys := sysStep E S3 (.nearIn (5 * NEAR))
def S5 : Sys := sysStep E S4 (.resolve 0 (.ok (some NEAR)))         -- bob's contract: 1 NEAR unused
def S6 : Sys := sysStep E S5 (.call "carol.near" (2 * NEAR) .near_deposit [])
def S7 : Sys := sysStep E S6 (.call "alice.near" 1 (.ft_transfer "carol.near" NEAR) [])

theorem reach7 : Reach E S7 :=
  Reach.step _ <| Reach.step _ <| Reach.step _ <| Reach.step _ <| Reach.step _ <| Reach.step _ <|
    Reach.step _ reach0

-- the steps really did something (no silent no-op): bob holds 3 NEAR of wNEAR
theorem bob_bal : get S7.c.accts "bob.near" = some (3 * NEAR) := by decide +kernel
theorem pending_empty : S7.pending = [] := by decide +kernel

/-- **Non-vacuity of the headline.** -/
theorem exit_fires :
    let S' := sysStep E S7 (.call "bob.near" 1 (.near_withdraw (3 * NEAR)) [])
    bal S'.c.accts "bob.near" = 0 ∧ S'.paid = S7.paid ++ [("bob.near", 3 * NEAR + 1)] := by
  obtain ⟨h1, _, h3⟩ := exit_always E sane S7 reach7 "bob.near" (by decide) (by decide +kernel)
    (3 * NEAR) bob_bal
  exact ⟨h1, h3⟩

/-! ## Precision: a pending refund can pre-empt the withdrawal the holder signed -/

def P3 : Sys := S3                                           -- alice → bob 4 NEAR, callback pending
theorem bob_sees : get P3.c.accts "bob.near" = some (4 * NEAR) := by decide +kernel
def P4 : Sys := sysStep E P3 (.resolve 0 .failed)            -- bob is a plain account: full refund
/-- bob's `near_withdraw(4 NEAR)` signed against what he saw fails if the refund lands first -/
theorem withdraw_preempted :
    (exec E P4.c ⟨"bob.near", 1, .near_withdraw (4 * NEAR), []⟩).isNone = true := by decide +kernel
/-- and `T_no_one_else` indeed reports this step only through its exception branch -/
theorem lowered : bal P4.c.accts "bob.near" < bal P3.c.accts "bob.near" := by decide +kernel

#eval (S7.c.accts, S7.c.supply, S7.c.near, S7.paid)

end Review

#print axioms Review.exit_fires
#print axioms Review.withdraw_preempted
