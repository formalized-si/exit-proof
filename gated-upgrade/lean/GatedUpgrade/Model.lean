/-
  GatedUpgrade.Model — the gated vault (`contract/gated-vault/src/lib.rs`) as a state machine on
  top of the plugin model `UpgradeWindow.Model` (near-plugins v0.5.1 `Upgradable`).

  What is modelled
  * the plugin's storage, the code on the account and the deploy batches in flight: the kit's
    `Sys`, driven by the kit's `Sys.step` (nothing of the plugin is re-modelled here);
  * the access-control plugin as the vault configures it: three roles, exactly one per protected
    method, and every state-changing `acl_*` method of
    `near-plugins-derive/src/access_controllable.rs` with its permission check;
  * the gate: `deploy_certified` (reads the staged hash, checks the delay, asks the registry),
    the registry's answer on its way back, and the callback `on_certificates` (accepts an answer
    only if it holds a certificate that is not revoked, is for the asked hash and the accepted
    kind, and comes from an accepted attestor; then calls the plugin's `up_deploy_code(hash,
    None)` as the contract account);
  * the registry: a list of certificates that may change to anything at any moment (`regSet`),
    and its view `get_valid_kind`, which answers with the valid certificates it holds.

  What is a parameter
  * `Code`, `H : Code → String` — as in the kit (bs58 of sha256);
  * `Cfg` — the contract account, the registry account, the accepted kind and the accepted
    attestors; written once by `new`, never changed by the model;
  * the caller of every external receipt, the order of all events and their block timestamps,
    and whether the registry call and the callback succeed.

  Failed receipts: a failed call of a plugin method, of an `acl_*` method or of
  `deploy_certified` changes nothing and creates nothing — it is the event `other`. A failed
  registry call reaches the callback as a failed promise result (`regAnswer i false`); a failed
  callback consumes the answer and does nothing else (`callback j false`); a failed deploy batch
  leaves the code as it was (`batch i false`).
-/
import UpgradeWindow.Model

namespace GatedUpgrade
open UpgradeWindow

/-! ### Access control -/

/-- The vault's `Role` enum. -/
inductive Role where
  | codeStager
  | codeDeployer
  | durationManager
  deriving DecidableEq, Repr

/-- The vault's `#[upgradable(access_control_roles(..))]` attribute: the one role that passes the
    `#[access_control_any]` check of each protected method. -/
def roleFor {Code : Type} : Call Code → Role
  | .stageCode _ => .codeStager
  | .deployCode _ _ => .codeDeployer
  | .initDur _ => .durationManager
  | .stageDur _ => .durationManager
  | .applyDur => .durationManager

/-- The plugin's permission sets: the bearers of the super-admin flag, and per role the bearers of
    the admin flag and of the role flag (`access_controllable.rs`, `bearers`). -/
structure Acl where
  superAdmins : List String := []
  admins : Role → List String := fun _ => []
  grantees : Role → List String := fun _ => []

/-- Set insertion. -/
def addTo (l : List String) (x : String) : List String := if x ∈ l then l else l ++ [x]

/-- Set removal. -/
def removeFrom (l : List String) (x : String) : List String := l.filter fun y => decide (y ≠ x)

/-- Replaces the set of one role. -/
def setRole (f : Role → List String) (r : Role) (v : List String) : Role → List String :=
  fun r' => if r' = r then v else f r'

/-- `is_super_admin`. -/
def Acl.isSuperAdmin (a : Acl) (who : String) : Bool := decide (who ∈ a.superAdmins)

/-- `is_admin`: a super-admin, or an admin of the role. -/
def Acl.isAdmin (a : Acl) (r : Role) (who : String) : Bool :=
  decide (who ∈ a.superAdmins ∨ who ∈ a.admins r)

/-- `has_role`: role grants only; a super-admin is not a grantee. -/
def Acl.hasRole (a : Acl) (r : Role) (who : String) : Bool := decide (who ∈ a.grantees r)

/-- The `#[access_control_any(roles(..))]` check of a protected plugin method for `who` as the
    predecessor. -/
def Acl.allowed {Code : Type} (a : Acl) (who : String) (c : Call Code) : Bool :=
  a.hasRole (roleFor c) who

/-- The state-changing methods of `AccessControllable`. -/
inductive AclOp where
  /-- `acl_init_super_admin(account)`: `#[private]`; refused when a super-admin exists. -/
  | initSuperAdmin (account : String)
  /-- `acl_add_super_admin(account)`. -/
  | addSuperAdmin (account : String)
  /-- `acl_revoke_super_admin(account)`. -/
  | revokeSuperAdmin (account : String)
  /-- `acl_transfer_super_admin(account)`. -/
  | transferSuperAdmin (account : String)
  /-- `acl_add_admin(role, account)`. -/
  | addAdmin (r : Role) (account : String)
  /-- `acl_revoke_admin(role, account)`. -/
  | revokeAdmin (r : Role) (account : String)
  /-- `acl_renounce_admin(role)`: the caller's own admin permission. -/
  | renounceAdmin (r : Role)
  /-- `acl_grant_role(role, account)`. -/
  | grantRole (r : Role) (account : String)
  /-- `acl_revoke_role(role, account)`. -/
  | revokeRole (r : Role) (account : String)
  /-- `acl_renounce_role(role)`: the caller's own role. -/
  | renounceRole (r : Role)

/-- One call of an `acl_*` method by `caller` (the predecessor); `self` is the contract account.
    A call without the required permission returns `None` (or panics, for the private method)
    and leaves the permissions as they were. -/
def Acl.apply (self caller : String) (a : Acl) : AclOp → Acl
  | .initSuperAdmin x =>
    if caller = self ∧ a.superAdmins = [] then { a with superAdmins := [x] } else a
  | .addSuperAdmin x =>
    if a.isSuperAdmin caller then { a with superAdmins := addTo a.superAdmins x } else a
  | .revokeSuperAdmin x =>
    if a.isSuperAdmin caller then { a with superAdmins := removeFrom a.superAdmins x } else a
  | .transferSuperAdmin x =>
    if a.isSuperAdmin caller then
      if x = caller then a
      else { a with superAdmins := removeFrom (addTo a.superAdmins x) caller }
    else a
  | .addAdmin r x =>
    if a.isAdmin r caller then { a with admins := setRole a.admins r (addTo (a.admins r) x) } else a
  | .revokeAdmin r x =>
    if a.isAdmin r caller then { a with admins := setRole a.admins r (removeFrom (a.admins r) x) }
    else a
  | .renounceAdmin r => { a with admins := setRole a.admins r (removeFrom (a.admins r) caller) }
  | .grantRole r x =>
    if a.isAdmin r caller then { a with grantees := setRole a.grantees r (addTo (a.grantees r) x) }
    else a
  | .revokeRole r x =>
    if a.isAdmin r caller then
      { a with grantees := setRole a.grantees r (removeFrom (a.grantees r) x) }
    else a
  | .renounceRole r => { a with grantees := setRole a.grantees r (removeFrom (a.grantees r) caller) }

/-! ### The gate and the registry -/

/-- The fields of a registry certificate the gate reads. `attestor` is set by the registry to the
    account that called `attest`. -/
structure Cert where
  codeHash : String
  kind : String
  attestor : String
  revoked : Bool
  deriving DecidableEq, Repr

/-- What `new` writes and nothing changes: the contract account, and the gate (`Gate` in the
    contract: registry, accepted kind, accepted attestors). -/
structure Cfg where
  self : String
  registry : String
  kind : String
  attestors : List String

/-- The registry's view `get_valid_kind(code_hash, kind)`: the certificates it holds for that
    hash, not revoked, of that kind. -/
def Reg.answer (reg : List Cert) (h kind : String) : List Cert :=
  reg.filter fun c => decide (c.codeHash = h ∧ c.revoked = false ∧ c.kind = kind)

/-- The callback's test on one certificate of the answer, for the hash that was asked about. -/
def Cert.accepted (cfg : Cfg) (h : String) (c : Cert) : Prop :=
  c.revoked = false ∧ c.codeHash = h ∧ c.kind = cfg.kind ∧ c.attestor ∈ cfg.attestors

instance (cfg : Cfg) (h : String) (c : Cert) : Decidable (c.accepted cfg h) := by
  unfold Cert.accepted; infer_instance

/-- `on_certificates`: does the promise result let the deployment through? `none` is a failed
    registry call. -/
def accepts (cfg : Cfg) (h : String) : Option (List Cert) → Bool
  | none => false
  | some cs => cs.any fun c => decide (c.accepted cfg h)

/-- A registry state holds an accepted certificate for the hash `h`: not revoked, of the accepted
    kind, attested by an accepted attestor. -/
def Certified (cfg : Cfg) (reg : List Cert) (h : String) : Prop :=
  ∃ c ∈ reg, c.codeHash = h ∧ c.kind = cfg.kind ∧ c.revoked = false ∧ c.attestor ∈ cfg.attestors

/-! ### The system -/

/-- The gated vault and the registry. -/
structure GSys (Code : Type) where
  /-- Plugin storage, the code on the account, deploy batches in flight (the kit's model). -/
  sys : Sys Code
  /-- The vault's access-control state. -/
  acl : Acl
  /-- The registry's certificates. -/
  reg : List Cert := []
  /-- Registry calls created by `deploy_certified` and not executed yet: the hash asked about. -/
  queries : List String := []
  /-- Results of executed registry calls on their way to `on_certificates`: the hash asked about
      and the result (`none`: the call failed). -/
  answers : List (String × Option (List Cert)) := []

/-- What can happen. -/
inductive GEv (Code : Type) where
  /-- A receipt from `caller` calling one of the plugin's five protected methods. -/
  | plugin (caller : String) (c : Call Code)
  /-- A receipt from `caller` calling an `acl_*` method. -/
  | acl (caller : String) (op : AclOp)
  /-- A receipt from anyone calling `deploy_certified`. -/
  | deployCertified
  /-- The registry executes the `i`-th call in flight; `ok = false`: that receipt failed. -/
  | regAnswer (i : Nat) (ok : Bool)
  /-- The callback for the `j`-th answer executes; `ok = false`: it failed before doing anything
      (out of gas, for instance). -/
  | callback (j : Nat) (ok : Bool)
  /-- The `i`-th deploy batch in flight executes (the kit's event). -/
  | batch (i : Nat) (ok : Bool)
  /-- The registry's certificates become `r`: attestations and revocations by anyone, at any
      time. Nothing is assumed about them. -/
  | regSet (r : List Cert)
  /-- Anything else: views, the vault's own methods, receipts that fail without effect. -/
  | other

variable {Code : Type}

/-- The plugin-level event an event amounts to: this is what the kit's `Sys.step` sees.
    * a protected plugin method called from outside: the call, with the access-control outcome
      for that caller;
    * a successful callback on an accepted answer: `up_deploy_code(hash, None)` with the
      contract account as predecessor;
    * a deploy batch: itself;
    * everything else: nothing the plugin sees. -/
def GSys.evOf (cfg : Cfg) (s : GSys Code) : GEv Code → Ev Code
  | .plugin caller c => .call (s.acl.allowed caller c) c
  | .callback j ok =>
    match s.answers[j]? with
    | none => .other
    | some (h, res) =>
      if ok = true ∧ accepts cfg h res = true then
        .call (s.acl.allowed cfg.self (.deployCode h none : Call Code)) (.deployCode h none)
      else .other
  | .batch i ok => .batch i ok
  | _ => .other

/-- One event at block timestamp `now`. -/
def GSys.step (cfg : Cfg) (H : Code → String) (now : Nat) (s : GSys Code) : GEv Code → GSys Code
  | .plugin caller c => { s with sys := s.sys.step H now (.call (s.acl.allowed caller c) c) }
  | .acl caller op => { s with acl := s.acl.apply cfg.self caller op }
  | .deployCertified =>
    -- `deploy_certified`: panics unless code is staged and its staging timestamp has passed;
    -- otherwise creates the registry call for the staged hash (and the callback behind it)
    match s.sys.up.stagedCodeHash H, s.sys.up.stagingTs with
    | some h, some ts => if now < ts then s else { s with queries := s.queries ++ [h] }
    | _, _ => s
  | .regAnswer i ok =>
    match s.queries[i]? with
    | none => s
    | some h =>
      { s with queries := s.queries.eraseIdx i,
               answers := s.answers ++
                 [(h, if ok = true then some (Reg.answer s.reg h cfg.kind) else none)] }
  | .callback j ok =>
    -- `on_certificates(hash)`: the answer is consumed; on an accepted answer the plugin's
    -- `up_deploy_code(hash, None)` runs with the contract account as predecessor
    match s.answers[j]? with
    | none => s
    | some (h, res) =>
      if ok = true ∧ accepts cfg h res = true then
        { s with answers := s.answers.eraseIdx j,
                 sys := s.sys.step H now
                   (.call (s.acl.allowed cfg.self (.deployCode h none : Call Code))
                     (.deployCode h none)) }
      else { s with answers := s.answers.eraseIdx j }
  | .batch i ok => { s with sys := s.sys.step H now (.batch i ok) }
  | .regSet r => { s with reg := r }
  | .other => s

/-- A trace: events with their block timestamps. -/
abbrev GTrace (Code : Type) := List (Nat × GEv Code)

/-- Runs a trace. -/
def grun (cfg : Cfg) (H : Code → String) : GSys Code → GTrace Code → GSys Code
  | s, [] => s
  | s, (t, e) :: rest => grun cfg H (s.step cfg H t e) rest

/-- Block timestamps never decrease: the trace starts at or after `t0`. -/
def GMono : Nat → GTrace Code → Prop
  | _, [] => True
  | t, (t', _) :: rest => t ≤ t' ∧ GMono t' rest

/-- The plugin-level trace of a run: the kit's theorems are about this trace. -/
def projTrace (cfg : Cfg) (H : Code → String) : GSys Code → GTrace Code → Trace Code
  | _, [] => []
  | s, (t, e) :: rest => (t, s.evOf cfg e) :: projTrace cfg H (s.step cfg H t e) rest

/-- The caller of an external receipt is not the contract account. -/
def ExternalEv (cfg : Cfg) : GEv Code → Prop
  | .plugin caller _ => caller ≠ cfg.self
  | .acl caller _ => caller ≠ cfg.self
  | _ => True

/-- Hypothesis on a trace: no receipt calling a plugin method or an `acl_*` method has the
    contract account as predecessor. (The contract account has no access keys, and the vault's
    code calls itself only in the callback and in the deploy batch, which are separate events.) -/
def External (cfg : Cfg) (tr : GTrace Code) : Prop := ∀ x ∈ tr, ExternalEv cfg x.2

/-! ### States -/

/-- Nobody but the contract account is a super-admin, an admin of any role, a code deployer or a
    duration manager. Nothing is said about the code stagers. -/
def AclInv (cfg : Cfg) (a : Acl) : Prop :=
  (∀ x ∈ a.superAdmins, x = cfg.self) ∧
  (∀ r, ∀ x ∈ a.admins r, x = cfg.self) ∧
  (∀ x ∈ a.grantees .codeDeployer, x = cfg.self) ∧
  (∀ x ∈ a.grantees .durationManager, x = cfg.self)

/-- A quiet state with staging duration `D`: the access-control invariant, no deploy batch in
    flight, no registry answer on its way, nothing staged. Registry calls in flight, the
    registry's content and the code stagers are arbitrary. -/
structure Fresh (cfg : Cfg) (D : Nat) (s : GSys Code) : Prop where
  acl : AclInv cfg s.acl
  noBatch : s.sys.inflight = []
  noAnswer : s.answers = []
  nothingStaged : s.sys.up.stagingTs = none
  dur : s.sys.up.dur = some D

/-- The state right after `new(staging_duration = D, .., stagers)` on an account running `code`:
    the contract account is the only super-admin and the only code deployer, nobody is a duration
    manager, the listed accounts are code stagers; the registry holds `reg`. -/
def GSys.init (cfg : Cfg) (D : Nat) (code : Code) (stagers : List String) (reg : List Cert) :
    GSys Code :=
  { sys := { up := { dur := some D }, current := code },
    acl := { superAdmins := [cfg.self],
             admins := fun _ => [],
             grantees := fun r =>
               match r with
               | .codeStager => stagers
               | .codeDeployer => [cfg.self]
               | .durationManager => [] },
    reg := reg }

end GatedUpgrade
