/-
  UpgradeWindow.Example — the example contract (`contract/vault`): the plugin configured with
  four roles, a minimal access-control state, and the vault. This is what the conformance run
  executes against the wasm. The W-theorems do not depend on anything here. The two vault
  theorems at the end are the model-level facts behind the exit premise of the W5 corollaries
  for the example: in the model `withdraw` succeeds in every vault state, and nobody else's
  call changes a balance. They say nothing about time, nor about the NEAR balance of the
  account, which the model leaves out: on chain the same call fails when that balance cannot
  cover both the transfer and the storage stake, and staged code raises the stake (README, A5).
-/
import UpgradeWindow.Model

namespace UpgradeWindow

/-- The example's `Role` enum. -/
inductive Role where
  | dao | codeStager | codeDeployer | durationManager
  deriving DecidableEq, Repr

def Role.name : Role → String
  | .dao => "DAO"
  | .codeStager => "CodeStager"
  | .codeDeployer => "CodeDeployer"
  | .durationManager => "DurationManager"

def Role.ofName? : String → Option Role
  | "DAO" => some .dao
  | "CodeStager" => some .codeStager
  | "CodeDeployer" => some .codeDeployer
  | "DurationManager" => some .durationManager
  | _ => none

/-- The example's `#[upgradable(access_control_roles(..))]` attribute: which roles pass the
    `#[access_control_any]` check of each protected method. -/
def rolesFor {Code : Type} : Call Code → List Role
  | .stageCode _ => [.codeStager, .dao]
  | .deployCode _ _ => [.codeDeployer, .dao]
  | .initDur _ => [.durationManager, .dao]
  | .stageDur _ => [.durationManager, .dao]
  | .applyDur => [.durationManager, .dao]

/-- Access-control state as the example uses it: one super-admin fixed at init (the contract
    account), no role admins, and the set of (account, role) grants.
    `acl_has_any_role` looks at role grants only: a super-admin is not a grantee
    (near-plugins-derive/src/access_controllable.rs, `has_any_permission`). -/
structure Acl where
  superAdmin : String
  grants : List (String × Role) := []

def Acl.has (a : Acl) (who : String) (r : Role) : Bool :=
  a.grants.any fun g => g.1 == who && g.2 == r

/-- The `#[access_control_any(roles(..))]` check. -/
def Acl.allowed {Code : Type} (a : Acl) (who : String) (c : Call Code) : Bool :=
  (rolesFor c).any (a.has who)

/-- `acl_grant_role`: `None` unless the caller is an admin; else whether the role is new. -/
def Acl.grant (a : Acl) (caller : String) (r : Role) (who : String) : Acl × Option Bool :=
  if caller != a.superAdmin then (a, none)
  else if a.has who r then (a, some false)
  else ({ a with grants := a.grants ++ [(who, r)] }, some true)

def Acl.revokeUnchecked (a : Acl) (r : Role) (who : String) : Acl × Bool :=
  if a.has who r then
    ({ a with grants := a.grants.filter fun g => !(g.1 == who && g.2 == r) }, true)
  else (a, false)

/-- `acl_revoke_role`. -/
def Acl.revoke (a : Acl) (caller : String) (r : Role) (who : String) : Acl × Option Bool :=
  if caller != a.superAdmin then (a, none)
  else let (a', b) := a.revokeUnchecked r who; (a', some b)

/-- `acl_renounce_role`: the caller gives up its own role. -/
def Acl.renounce (a : Acl) (caller : String) (r : Role) : Acl × Bool :=
  a.revokeUnchecked r caller

/-! ### The vault -/

def U128_MAX : Nat := 340282366920938463463374607431768211455

/-- `balances`, newest entry first. -/
structure Vault where
  bal : List (String × Nat) := []

def lookupBal (who : String) : List (String × Nat) → Nat
  | [] => 0
  | (k, x) :: rest => if k = who then x else lookupBal who rest

def Vault.balanceOf (v : Vault) (who : String) : Nat := lookupBal who v.bal

def Vault.set (v : Vault) (who : String) (x : Nat) : Vault := { bal := (who, x) :: v.bal }

inductive VErr where
  /-- "Vault: overflow" -/
  | overflow
  /-- "Vault: insufficient balance" -/
  | insufficient
  deriving Repr, DecidableEq

/-- `deposit` (payable): credits the attached amount to the caller. -/
def Vault.deposit (v : Vault) (who : String) (amount : Nat) : Except VErr Vault :=
  if U128_MAX < v.balanceOf who + amount then .error .overflow
  else .ok (v.set who (v.balanceOf who + amount))

/-- `withdraw(amount)`: debits the caller and returns the transfer `(to, amount)`. -/
def Vault.withdraw (v : Vault) (who : String) (amount : Nat) :
    Except VErr (Vault × (String × Nat)) :=
  if v.balanceOf who < amount then .error .insufficient
  else .ok (v.set who (v.balanceOf who - amount), (who, amount))

/-- **Exit path of the example.** In every vault state a user's `withdraw` of its whole balance
    succeeds in that one call and returns the transfer of exactly that balance to the user. The
    vault has no pause, no owner and no role check on this path. (On chain the call also needs
    the account's NEAR balance to cover the transfer and the storage stake; that balance is
    not modelled.) -/
theorem vault_exit (v : Vault) (who : String) :
    v.withdraw who (v.balanceOf who) = .ok (v.set who 0, (who, v.balanceOf who)) := by
  simp [Vault.withdraw]

/-- **Nobody else touches a balance.** `deposit` and `withdraw` by another account leave a
    user's balance as it was (and the plugin's methods do not write the vault's state at all). -/
theorem vault_others (v : Vault) (who other : String) (hne : other ≠ who) (x : Nat) :
    (v.set other x).balanceOf who = v.balanceOf who := by
  simp [Vault.set, Vault.balanceOf, lookupBal, hne]

end UpgradeWindow
