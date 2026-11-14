/-
  Three parts of the Intents contract that decide who may lower a ledger balance, for the same
  token `T` as `Intents/Ledger.lean` (near/intents, commit
  16d04f6ec4401263f8914638710260da50bb46b0):

  * the refund of a transfer call: `mt_resolve_transfer`
    (contracts/defuse/src/contract/tokens/nep245/resolver.rs:16-122), scheduled only by
    `notify_and_resolve_transfer` (tokens/nep245/core.rs:219-270, intents/state.rs:243-262);
  * how an account authorises an operation: a direct call with authentication by predecessor
    enabled (`ensure_auth_predecessor_id`, accounts/mod.rs:79-85), or a signed payload
    (`execute_signed_intent`, core/src/engine/mod.rs:42-83) with a key registered for the signer
    (`has_public_key`, intents/state.rs:42-50; accounts/account/mod.rs:64-90);
  * the role table: near-plugins 0.5.3 `AccessControllable`
    (near-plugins-derive `access_controllable.rs:150-420, 598-660`).

  These functions are used by the strict world (`Intents/Strict.lean`) and by the replay
  (`Main.lean`). Nothing of `Intents/Ledger.lean` is changed.
-/
import Intents.Ledger

namespace Intents
open ProvedFT (Acct Accts get bal set total PR U128_MAX)

/-! ### The refund of a transfer call -/

/-- A transfer call whose `mt_resolve_transfer` callback is in flight: one row of
    `internal_mt_batch_transfer_call` for this token id. `amount` moved from `sender` to
    `receiver` when the entry was made. -/
structure Xc where
  sender : Acct
  receiver : Acct
  amount : Nat
  deriving Repr, DecidableEq

/-- The refund `mt_resolve_transfer` takes back for one row (resolver.rs:51, 72-74): what the
    receiver's answer asks for (`req`; the whole amount when the answer is unusable), capped by
    the amount of the transfer and by the receiver's balance. -/
def Xc.refund (L : Ledger) (x : Xc) (req : Nat) : Nat :=
  min (min req x.amount) (bal L.bals x.receiver)

/-- `mt_resolve_transfer` for one row (resolver.rs:40-96): nothing when the refund is zero,
    otherwise the refund moves from the receiver back to the sender. Locks are not tested. -/
def resolveTransfer (L : Ledger) (x : Xc) (req : Nat) : Option Ledger :=
  if x.refund L req = 0 then some L else moveBal L .refund x.receiver x.sender (x.refund L req)

/-! ### Direct calls -/

/-- The entry guard of `mt_transfer`, `mt_batch_transfer`, `mt_transfer_call`,
    `mt_batch_transfer_call` (tokens/nep245/core.rs:15-104): the pause key `mt_transfer` is not
    paused and authentication by predecessor is enabled for the caller. -/
def directOk (c : Ctl) (pred : Acct) : Bool :=
  !c.isPaused "mt_transfer" && !c.authOff.contains pred

/-! ### Public keys, nonces, signed payloads -/

/-- A public key, as the contract prints it (`ed25519:…`). -/
abbrev Key := String
/-- A nonce of a signed payload (base64 of 32 bytes). -/
abbrev Nonce := String

/-- The contract state that decides whether a signed payload is accepted. It holds no tokens. -/
structure AuthSt where
  /-- `Account.public_keys`: keys registered explicitly. -/
  keys : List (Acct × Key) := []
  /-- Accounts whose implicit public key was removed (`implicit_public_key_removed`). -/
  noImplicit : List Acct := []
  /-- Nonces committed by executed payloads (`commit_nonce`). -/
  nonces : List (Acct × Nonce) := []
  deriving Repr

/-- `has_public_key(account, key)` (intents/state.rs:42-50, accounts/account/mod.rs:86-90): the
    key is the implicit key of the account and was not removed, or it is registered.
    `implicit` is `PublicKey::to_implicit_account_id`. -/
def hasKey (implicit : Key → Acct) (A : AuthSt) (a : Acct) (k : Key) : Bool :=
  (!A.noImplicit.contains a && implicit k == a) || A.keys.contains (a, k)

/-- `State::add_public_key` (intents/state.rs:102-110, accounts/account/mod.rs:64-72): the
    account must not be locked; the implicit key can be added back only after it was removed,
    any other key only when it is not registered yet. -/
def addKey (implicit : Key → Acct) (c : Ctl) (A : AuthSt) (a : Acct) (k : Key) : Option AuthSt :=
  if c.locked.contains a then none
  else if implicit k == a then
    (if A.noImplicit.contains a then some { A with noImplicit := A.noImplicit.filter fun x => x != a }
     else none)
  else if A.keys.contains (a, k) then none
  else some { A with keys := (a, k) :: A.keys }

/-- `State::remove_public_key` (intents/state.rs:113-121, accounts/account/mod.rs:76-84): the
    account must not be locked and must have the key. -/
def removeKey (implicit : Key → Acct) (c : Ctl) (A : AuthSt) (a : Acct) (k : Key) : Option AuthSt :=
  if c.locked.contains a then none
  else if implicit k == a then
    (if A.noImplicit.contains a then none else some { A with noImplicit := a :: A.noImplicit })
  else if A.keys.contains (a, k) then some { A with keys := A.keys.filter fun e => e != (a, k) }
  else none

/-- One intent of a signed payload, as far as it concerns the ledger of this token and the keys
    of the signer. -/
inductive Op where
  /-- `FtWithdraw` of this token, debited from the signer. -/
  | withdraw (w : Wd)
  /-- `Transfer`, or the signer's negative side of a `TokenDiff`: `amt` leaves the signer for
      `dst`. `call`: a `Transfer` with a notification, after which `mt_resolve_transfer` follows
      (intents/state.rs:243-262). -/
  | move (dst : Acct) (amt : Nat) (call : Bool)
  /-- `AddPublicKey`. -/
  | addKey (k : Key)
  /-- `RemovePublicKey`. -/
  | removeKey (k : Key)
  /-- `SetAuthByPredecessorId`. -/
  | setAuth (enable : Bool)

/-- What an intent can take from the signer's balance of this token. -/
def Op.takes : Op → Nat
  | .withdraw w => w.amount
  | .move _ amt _ => amt
  | _ => 0

/-- A signed payload (`DefusePayload`, core/src/payload/mod.rs) as `execute_signed_intent` reads
    it. -/
structure Payload where
  signer : Acct
  /-- The public key `MultiPayload::verify` returns: the key the signature verifies under. -/
  key : Key
  /-- `verifying_contract`. -/
  contract : Acct
  /-- Nanoseconds, compared with the block time. -/
  deadline : Nat
  nonce : Nonce
  ops : List Op := []

/-- The most a payload can take from its signer's balance of this token. -/
def Payload.takes (p : Payload) : Nat := sumBy Op.takes p.ops

/-- What `execute_signed_intent` (core/src/engine/mod.rs:42-80) tests of a payload whose
    signature verifies under `p.key`, before its intents run: the verifying contract is this
    contract, the deadline has not passed, the key is one of the signer's, the nonce is not
    used, and the signer is not locked (`commit_nonce`, intents/state.rs:124-130). -/
def admit (implicit : Key → Acct) (me : Acct) (now : Nat) (c : Ctl) (A : AuthSt) (p : Payload) :
    Bool :=
  p.contract == me && !decide (p.deadline < now) && hasKey implicit A p.signer p.key
    && !A.nonces.contains (p.signer, p.nonce) && !c.locked.contains p.signer

/-- `commit_nonce`. -/
def commitNonce (A : AuthSt) (p : Payload) : AuthSt :=
  { A with nonces := (p.signer, p.nonce) :: A.nonces }

/-! ### The role table (near-plugins `AccessControllable`) -/

/-- Super-admins, admins of a role, and grantees of a role (the last is `Ctl.roles`). -/
structure Acl where
  supers : List Acct := []
  admins : List (Acct × Role) := []
  roles : List (Acct × Role) := []
  deriving Repr

/-- `is_admin(role, account)`: a super-admin, or an admin of the role. -/
def Acl.isAdmin (x : Acl) (r : Role) (a : Acct) : Bool :=
  x.supers.contains a || x.admins.contains (a, r)

/-- The `acl_*` methods that change the table, with their caller `who`. -/
inductive AclCall where
  | grantRole (who : Acct) (r : Role) (a : Acct)
  | revokeRole (who : Acct) (r : Role) (a : Acct)
  | renounceRole (who : Acct) (r : Role)
  | addAdmin (who : Acct) (r : Role) (a : Acct)
  | revokeAdmin (who : Acct) (r : Role) (a : Acct)
  | renounceAdmin (who : Acct) (r : Role)
  | addSuper (who : Acct) (a : Acct)
  | revokeSuper (who : Acct) (a : Acct)
  | transferSuper (who : Acct) (a : Acct)

/-- The rules of the table. A caller without the permission changes nothing. -/
def aclStep (x : Acl) : AclCall → Acl
  | .grantRole who r a =>
    if x.isAdmin r who && !x.roles.contains (a, r) then { x with roles := (a, r) :: x.roles } else x
  | .revokeRole who r a =>
    if x.isAdmin r who then { x with roles := x.roles.filter fun e => e != (a, r) } else x
  | .renounceRole who r => { x with roles := x.roles.filter fun e => e != (who, r) }
  | .addAdmin who r a =>
    if x.isAdmin r who && !x.admins.contains (a, r) then { x with admins := (a, r) :: x.admins } else x
  | .revokeAdmin who r a =>
    if x.isAdmin r who then { x with admins := x.admins.filter fun e => e != (a, r) } else x
  | .renounceAdmin who r => { x with admins := x.admins.filter fun e => e != (who, r) }
  | .addSuper who a =>
    if x.supers.contains who && !x.supers.contains a then { x with supers := a :: x.supers } else x
  | .revokeSuper who a =>
    if x.supers.contains who then { x with supers := x.supers.filter fun y => y != a } else x
  | .transferSuper who a =>
    if x.supers.contains who && a != who then
      { x with supers := (a :: x.supers).filter fun y => y != who }
    else x

/-- Somebody can change who holds role `r`: there is a super-admin, or an admin of `r`. -/
def Acl.authority (x : Acl) (r : Role) : Bool :=
  !x.supers.isEmpty || x.admins.any fun e => e.2 == r

end Intents
