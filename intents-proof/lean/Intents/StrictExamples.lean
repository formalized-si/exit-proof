/-
  Non-vacuity for the statements of `Intents/StrictTheorems.lean`: concrete runs of the strict
  world on which their hypotheses hold and their conclusions say something. Nothing here is
  used by the theorems.

  The world is the one of `Intents/Examples.lean` (`alice.near` deposits 100). The public key
  `ed25519:A` is registered for `alice.near`; `root.near` is a super-admin; nobody holds a
  role. A signature is the name of the key it verifies under; `forged` verifies under none.
-/
import Intents.Examples
import Intents.StrictTheorems
import Intents.StrictKeys

namespace Intents.StrictExamples
open ProvedFT Intents Intents.Examples

def G : SCfg := { base := K, implicit := fun _ => "nobody", valid := fun k _ sig => sig == k }

def SS0 : SWorld :=
  { w := S0, auth := { keys := [("alice.near", "ed25519:A")] }, supers := ["root.near"] }

theorem sinit0 : SInit G SS0 := ⟨init0, rfl⟩

theorem sreach0 (l : List SStep) : SReach G SS0 (srun G (exec E) SS0 l) :=
  sreach_run (SReach.init SS0 sinit0) l

/-- The state after the deposit of 100 by `alice.near` and the steps `l`. -/
def after (l : List SStep) : SWorld := srun G (exec E) SS0 (deposit.map SStep.base ++ l)

/-- The balances of `alice.near` and `bob.near`, the transfer calls in flight, the used nonces. -/
def view (S : SWorld) : Nat × Nat × List Xc × List (Acct × Nonce) :=
  (bal S.w.L.bals "alice.near", bal S.w.L.bals "bob.near", S.calls, S.auth.nonces)

def roleView (S : SWorld) : List Acct × List (Acct × Role) × List (Acct × Role) :=
  (S.supers, S.admins, S.w.L.ctl.roles)

/-- A payload of `alice.near` signed with her registered key, deadline 10. -/
def pay (nonce : Nonce) (ops : List Op) : Payload :=
  { signer := "alice.near", key := "ed25519:A", contract := "intents.near", deadline := 10,
    nonce := nonce, ops := ops }

def send30 : List Op := [.move "bob.near" 30 false]

example : view (after []) = (100, 0, [], []) := by decide

/-! ### Refinement -/

/-- Every state of a strict run is a reachable state of the world of `Intents/World.lean`. -/
example (l : List SStep) : Reach K (srun G (exec E) SS0 l).w := strict_reach (sreach0 l)

/-- T1 on every strict run. -/
example (l : List SStep) :
    total (srun G (exec E) SS0 l).w.L.bals ≤ bal (srun G (exec E) SS0 l).w.c.accts "intents.near" :=
  strict_T1_ledger_covered (sreach0 l)

example (l : List SStep) := strict_T1_backing (sreach0 l)

/-- The three free steps of `Intents/World.lean` are not steps of the strict world: an intent
    without a payload, an internal move without a caller or a payload, a refund without a
    transfer call, a role table written from nowhere. -/
example :
    view (after [.base (.ftWithdraw .intent { owner := "alice.near", receiver := "alice.near", amount := 40 })])
      = (100, 0, [], []) ∧
    view (after [.base (.move .owner "alice.near" "bob.near" 30)]) = (100, 0, [], []) ∧
    view (after [.transfer "alice.near" "bob.near" 30 false,
      .base (.move .refund "bob.near" "alice.near" 30)]) = (70, 30, [], []) ∧
    roleView (after [.base (.admin (.acl [("mallory.near", .DAO)]))]) = (["root.near"], [], []) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### The refund of a transfer call (way 5 of `T4_authorised`, `T4_calls`) -/

def call30 : List SStep := [.transfer "alice.near" "bob.near" 30 true]

/-- `mt_transfer_call` by `alice.near`: 30 move, one refund is pending. -/
example : view (after call30) = (70, 30, [⟨"alice.near", "bob.near", 30⟩], []) := by decide

/-- The receiver asks to return 50 of a transfer of 30: the refund is 30, the entry is gone. -/
example : view (after (call30 ++ [.resolveTransfer 0 50])) = (100, 0, [], []) := by decide

/-- A refund of 10; a second `mt_resolve_transfer` finds no entry and takes nothing. -/
example :
    view (after (call30 ++ [.resolveTransfer 0 10])) = (80, 20, [], []) ∧
    view (after (call30 ++ [.resolveTransfer 0 10, .resolveTransfer 0 10])) = (80, 20, [], []) := by
  decide

/-- The receiver spent 25 before the callback: the refund is capped by its balance of 5. -/
example :
    view (after (call30 ++ [.transfer "bob.near" "carol.near" 25 false, .resolveTransfer 0 30]))
      = (75, 0, [], []) := by decide

/-- Without a transfer call there is nothing to refund: `bob.near` keeps what it received. -/
example :
    view (after [.transfer "alice.near" "bob.near" 30 false, .resolveTransfer 0 30])
      = (70, 30, [], []) := by decide

/-- A callback that fails before it runs uses the entry up as well. -/
example :
    view (after (call30 ++ [.resolveTransferFails 0, .resolveTransfer 0 30])) = (70, 30, [], []) := by
  decide

/-- The hypothesis of `T4_authorised` holds for the receiver of the transfer call, and the
    theorem gives way 5. -/
example :
    bal (sstd G (after call30) (.resolveTransfer 0 50)).w.L.bals "bob.near"
      < bal (after call30).w.L.bals "bob.near" := by decide

example := T4_authorised G (after call30) "bob.near" (.resolveTransfer 0 50) (by decide)

example := T4_calls G (after []) (.transfer "alice.near" "bob.near" 30 true)

/-! ### Authorisation (ways 1, 2 and 4 of `T4_authorised`) -/

/-- A signed payload with a `Transfer` that notifies the receiver: 30 leave, the nonce is
    used, a refund is pending. -/
example :
    view (after [.payload 5 (pay "n1" [.move "bob.near" 30 true]) "ed25519:A"])
      = (70, 30, [⟨"alice.near", "bob.near", 30⟩], [("alice.near", "n1")]) := by decide

/-- Rejected, each for one reason: a signature that does not verify; a key that is not
    registered for the signer; another verifying contract; a deadline that has passed. -/
example :
    view (after [.payload 5 (pay "n1" send30) "forged"]) = (100, 0, [], []) ∧
    view (after [.payload 5 { pay "n1" send30 with key := "ed25519:B" } "ed25519:B"])
      = (100, 0, [], []) ∧
    view (after [.payload 5 { pay "n1" send30 with contract := "other.near" } "ed25519:A"])
      = (100, 0, [], []) ∧
    view (after [.payload 11 (pay "n1" send30) "ed25519:A"]) = (100, 0, [], []) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The same payload a second time: the nonce is used, nothing moves. -/
example :
    view (after [.payload 5 (pay "n1" send30) "ed25519:A", .payload 5 (pay "n1" send30) "ed25519:A"])
      = (70, 30, [], [("alice.near", "n1")]) := by decide

/-- A payload whose second intent fails changes nothing, not even the nonce. -/
example :
    view (after [.payload 5 (pay "n1" [.move "bob.near" 30 false, .move "bob.near" 80 false])
      "ed25519:A"]) = (100, 0, [], []) := by decide

/-- A locked signer: the payload is refused. -/
example :
    view (after [.acl (.grantRole "root.near" .DAO "root.near"),
      .base (.admin (.lock "root.near" "alice.near")), .payload 5 (pay "n1" send30) "ed25519:A"])
      = (100, 0, [], []) := by decide

/-- Keys are steps. A key added by the account's own call signs; a removed key does not; a key
    can be added by a payload signed with a registered key. -/
example :
    view (after [.addKey "alice.near" "ed25519:B",
      .payload 5 { pay "n1" send30 with key := "ed25519:B" } "ed25519:B"])
      = (70, 30, [], [("alice.near", "n1")]) ∧
    view (after [.removeKey "alice.near" "ed25519:A", .payload 5 (pay "n1" send30) "ed25519:A"])
      = (100, 0, [], []) ∧
    view (after [.payload 5 (pay "n0" [.addKey "ed25519:B"]) "ed25519:A",
      .payload 5 { pay "n1" send30 with key := "ed25519:B" } "ed25519:B"])
      = (70, 30, [], [("alice.near", "n1"), ("alice.near", "n0")]) :=
  ⟨by decide, by decide, by decide⟩

/-- Direct calls: `mt_transfer` by the account moves; with authentication by predecessor
    switched off neither `mt_transfer` nor `add_public_key` does anything, and a signed
    payload still works. -/
example :
    view (after [.transfer "alice.near" "bob.near" 30 false]) = (70, 30, [], []) ∧
    view (after [.base (.admin (.authOffSelf "alice.near")), .transfer "alice.near" "bob.near" 30 false,
      .addKey "alice.near" "ed25519:B",
      .payload 5 { pay "n1" send30 with key := "ed25519:B" } "ed25519:B"]) = (100, 0, [], []) ∧
    view (after [.base (.admin (.authOffSelf "alice.near")), .payload 5 (pay "n1" send30) "ed25519:A"])
      = (70, 30, [], [("alice.near", "n1")]) :=
  ⟨by decide, by decide, by decide⟩

/-- `ft_withdraw` by the account itself is a step of the strict world (way 1). -/
example :
    view (after [.base (.ftWithdraw (.method "alice.near")
      { owner := "alice.near", receiver := "alice.near", amount := 40 })]) = (60, 0, [], []) := by
  decide

example := T4_authorised G (after []) "alice.near" (.payload 5 (pay "n1" send30) "ed25519:A")
  (by decide)

/-- `T4_key_power` on two steps of the run above: `ed25519:B` becomes a key of `alice.near` by
    her own call, and by an intent of a payload signed with `ed25519:A`. A call by anyone else
    cannot be written down: `addKey a k` is `a`'s own call. -/
example := T4_key_power G (after []) (.addKey "alice.near" "ed25519:B") "alice.near" "ed25519:B"
  (by decide) (by decide)

example := T4_key_power G (after []) (.payload 5 (pay "n0" [.addKey "ed25519:B"]) "ed25519:A")
  "alice.near" "ed25519:B" (by decide) (by decide)

/-- The assumption about signatures holds for this `valid` with "some signature verifies" as
    the meaning of "made by the holder"; `T4_signed_by_holder` applies. -/
theorem unforgeable0 : Unforgeable G (fun k p => ∃ sig, G.valid k p sig = true) :=
  fun _ _ sig h => ⟨sig, h⟩

example := T4_signed_by_holder G _ unforgeable0 (after []) "alice.near" 5 (pay "n1" send30)
  "ed25519:A" (by decide)

example (st : SStep) := T4_nonce_kept G (after [.payload 5 (pay "n1" send30) "ed25519:A"]) st
  ("alice.near", "n1") (by decide)

/-! ### The role table (ways 3 and 6, `T4_role_change`, `T4_roles_from_initial`) -/

/-- A grant by the super-admin makes a holder; a grant by anyone else changes nothing. -/
example :
    roleView (after [.acl (.grantRole "root.near" .UnrestrictedWithdrawer "ops.near")])
      = (["root.near"], [], [("ops.near", .UnrestrictedWithdrawer)]) ∧
    roleView (after [.acl (.grantRole "mallory.near" .UnrestrictedWithdrawer "mallory.near")])
      = (["root.near"], [], []) ∧
    roleView (after [.acl (.addAdmin "mallory.near" .DAO "mallory.near")]) = (["root.near"], [], []) ∧
    roleView (after [.acl (.addSuper "mallory.near" "mallory.near")]) = (["root.near"], [], []) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The power the statement names: the super-admin grants itself the role and forces a
    transfer out of `alice.near`'s balance. Without the grant the forced transfer does nothing. -/
example :
    view (after [.acl (.grantRole "root.near" .UnrestrictedWithdrawer "root.near"),
      .forceTransfer "root.near" "alice.near" "bob.near" 10 false]) = (90, 10, [], []) ∧
    view (after [.forceTransfer "root.near" "alice.near" "bob.near" 10 false]) = (100, 0, [], []) := by
  decide

example := T4_role_change G (after []) (.acl (.grantRole "root.near" .DAO "ops.near")) "ops.near"
  .DAO (by decide) (by decide)

example := T4_super_admin_can_take_any_role SS0.acl "root.near" "root.near" .DAO (by decide)

/-- The hypotheses of `T4_role_power`, `T4_admin_power` and `T4_super_power` hold for a call of
    the super-admin: an account that was no holder, no admin, no super-admin is one after it. -/
example := T4_role_power SS0.acl (.grantRole "root.near" .DAO "ops.near") "ops.near" .DAO
  (by decide) (by decide)

example := T4_admin_power SS0.acl (.addAdmin "root.near" .DAO "ops.near") "ops.near" .DAO
  (by decide) (by decide)

example := T4_super_power SS0.acl (.addSuper "root.near" "ops.near") "ops.near" (by decide)
  (by decide)

example := T4_super_power SS0.acl (.transferSuper "root.near" "ops.near") "ops.near" (by decide)
  (by decide)

/-- An admin of one role can grant that role and no other. -/
example :
    roleView (after [.acl (.addAdmin "root.near" .UnrestrictedWithdrawer "adm.near"),
      .acl (.grantRole "adm.near" .UnrestrictedWithdrawer "ops.near"),
      .acl (.grantRole "adm.near" .DAO "ops.near")])
      = (["root.near"], [("adm.near", .UnrestrictedWithdrawer)],
         [("ops.near", .UnrestrictedWithdrawer)]) := by decide

/-- A start without a super-admin and without admins: nobody ever holds a role. -/
def SSn : SWorld := { w := S0 }

theorem sinitn : SInit G SSn := ⟨init0, rfl⟩

example (l : List SStep) (a : Acct) (r : Role)
    (h : (srun G (exec E) SSn l).w.L.ctl.roles.contains (a, r) = true) : False := by
  have h0 := (T4_roles_from_initial (sreach_run (SReach.init SSn sinitn) l) r
    ⟨fun _ => rfl, fun _ => rfl⟩).2 a h
  cases h0

/-- With that start nobody can ever force a withdrawal or a transfer (`T4_force_from_initial`). -/
example (l : List SStep) (who : Acct)
    (h : (srun G (exec E) SSn l).w.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) : False := by
  have h0 := T4_force_from_initial (sreach_run (SReach.init SSn sinitn) l)
    ⟨fun _ => rfl, fun _ => rfl⟩ ⟨fun _ => rfl, fun _ => rfl⟩ who h
  cases h0

/-! ### The authentication flag -/

/-- The intent switches the flag of an unlocked account and not of a locked one. -/
example :
    (adminStep {} (.authIntent "alice.near" false)).authOff = ["alice.near"] ∧
    (adminStep { locked := ["alice.near"] } (.authIntent "alice.near" false)).authOff = [] := by
  decide

example := T4_auth_flag_power {} (.authIntent "alice.near" false) (by decide)

/-! ### The two guards that the invariant implies -/

example (l : List Step) (via : Via) (w : Wd) :=
  startWithdraw_amount_guard_redundant (reach0 l) via w

example (l : List Step) (amt : Nat) :=
  moveBal_destination_guard_redundant (reach0 l) "alice.near" "bob.near" amt (by decide)

/-- On a ledger that is not reachable (a supply above the `u128` range) the first guard is the
    only thing that stops the withdrawal. -/
example :
    (startWithdraw { bals := [("a.near", U128_MAX + 1)], supply := U128_MAX + 1 } (.method "a.near")
      { owner := "a.near", receiver := "a.near", amount := U128_MAX + 1 }).isNone = true ∧
    (debit { bals := [("a.near", U128_MAX + 1)], supply := U128_MAX + 1 } "a.near" (U128_MAX + 1)
      false).isSome = true := by decide

end Intents.StrictExamples
