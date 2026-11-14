/-
  The strict world: the two-contract world of `Intents/World.lean` with three things its step
  function leaves open decided by the contract's own rules.

  * A refund of a transfer call is no longer a free step. A transfer call puts an entry into
    `SWorld.calls`; the refund step takes one entry, computes the refund as
    `mt_resolve_transfer` does, and removes the entry.
  * An operation "of the owner" is no longer a label. It is either a direct call, guarded by the
    account's authentication-by-predecessor flag, or one signed payload: a signature that
    verifies under a key registered for the signer, the right verifying contract, a deadline not
    passed, a nonce not used. Keys are added and removed by steps.
  * The role table changes only by the rules of near-plugins `AccessControllable`.

  Every step of the strict world is zero or more steps of the world of `Intents/World.lean` on
  the part they share (`strict_refines` in `Intents/StrictTheorems.lean`), so every statement
  proved about that world holds here.
-/
import Intents.World
import Intents.Auth

namespace Intents
open ProvedFT (Acct Accts get bal set total PR Method Rcpt Out St Env Ret U128_MAX)

/-- A signature, as bytes the model does not look into. -/
abbrev Sig := String

structure SWorld where
  /-- The token, the ledger and everything in flight between them. -/
  w : World
  /-- `mt_resolve_transfer` callbacks in flight. -/
  calls : List Xc := []
  /-- Public keys and nonces. -/
  auth : AuthSt := {}
  /-- near-plugins super-admins. -/
  supers : List Acct := []
  /-- near-plugins admins of a role. The grantees are `w.L.ctl.roles`. -/
  admins : List (Acct × Role) := []

structure SCfg where
  base : Cfg
  /-- `PublicKey::to_implicit_account_id`. -/
  implicit : Key → Acct
  /-- `MultiPayload::verify`: the payload carries a signature that verifies under the key. The
      signature scheme is not modelled; see `Unforgeable` in `Intents/StrictTheorems.lean`. -/
  valid : Key → Payload → Sig → Bool

/-- The role table of a state. -/
def SWorld.acl (S : SWorld) : Acl := ⟨S.supers, S.admins, S.w.L.ctl.roles⟩

/-- The steps of `Intents/World.lean` that the strict world takes as they are: those that are
    not an operation on behalf of an owner without a stated authorisation, not an internal
    move, and not a free change of the role table. -/
def Step.free : Step → Bool
  | .ftWithdraw .intent _ => false
  | .move _ _ _ _ => false
  | .admin (.authIntent _ _) => false
  | .admin (.acl _) => false
  | _ => true

/-- A transfer call leaves an entry for its `mt_resolve_transfer`. -/
def pushCall (calls : List Xc) (call : Bool) (src dst : Acct) (amt : Nat) : List Xc :=
  if call then calls ++ [⟨src, dst, amt⟩] else calls

inductive SStep where
  /-- A step of `Intents/World.lean` with `Step.free`: the token's receipts, deposits, the
      callbacks of withdrawals, `ft_withdraw` called by the owner (`Via.method`: the caller is
      the owner and its authentication by predecessor is enabled), `ft_force_withdraw`, pauses,
      locks and the forced or self-made switch of the authentication flag. -/
  | base (st : Step)
  /-- `mt_transfer` / `mt_batch_transfer` (`call = false`) or `mt_transfer_call` /
      `mt_batch_transfer_call` (`call = true`) called by `src`: one row of this token id. -/
  | transfer (src dst : Acct) (amt : Nat) (call : Bool)
  /-- `mt_force_transfer*` called by `who`: one row of this token id. -/
  | forceTransfer (who src dst : Acct) (amt : Nat) (call : Bool)
  /-- `mt_resolve_transfer` for the `k`-th transfer call in flight; `req` is the refund the
      receiver's answer asks for (the whole amount when the answer is unusable). -/
  | resolveTransfer (k : Nat) (req : Nat)
  /-- That callback fails before it runs (out of gas). -/
  | resolveTransferFails (k : Nat)
  /-- `execute_signed_intent` for one signed payload at block time `now`: all of its intents,
      or nothing. -/
  | payload (now : Nat) (p : Payload) (sig : Sig)
  /-- `add_public_key(k)` called by `a`. -/
  | addKey (a : Acct) (k : Key)
  /-- `remove_public_key(k)` called by `a`. -/
  | removeKey (a : Acct) (k : Key)
  /-- An `acl_*` method. -/
  | acl (c : AclCall)

/-- One intent of a payload of `signer`. `none`: it fails, and with it the whole receipt. -/
def runOp (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) (S : SWorld) : Op → Option SWorld
  | .withdraw w =>
    if w.owner = signer ∧ (startWithdraw S.w.L .intent w).isSome = true then
      some { S with w := step G.base ex S.w (.ftWithdraw .intent w) }
    else none
  | .move dst amt call =>
    match moveBal S.w.L .owner signer dst amt with
    | none => none
    | some L' =>
      some { S with w := { S.w with L := L' }, calls := pushCall S.calls call signer dst amt }
  | .addKey k =>
    match addKey G.implicit S.w.L.ctl S.auth signer k with
    | none => none
    | some A => some { S with auth := A }
  | .removeKey k =>
    match removeKey G.implicit S.w.L.ctl S.auth signer k with
    | none => none
    | some A => some { S with auth := A }
  | .setAuth enable =>
    if S.w.L.ctl.locked.contains signer = true then none
    else some { S with w := step G.base ex S.w (.admin (.authIntent signer enable)) }

/-- The intents of a payload in order. -/
def runOps (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) : SWorld → List Op → Option SWorld
  | S, [] => some S
  | S, o :: t =>
    match runOp G ex signer S o with
    | none => none
    | some S' => runOps G ex signer S' t

/-- One step of the strict world. -/
def sstep (G : SCfg) (ex : St → Rcpt → Option Out) (S : SWorld) : SStep → SWorld
  | .base st => if st.free = true then { S with w := step G.base ex S.w st } else S
  | .transfer src dst amt call =>
    if directOk S.w.L.ctl src = true then
      match moveBal S.w.L .owner src dst amt with
      | none => S
      | some L' =>
        { S with w := { S.w with L := L' }, calls := pushCall S.calls call src dst amt }
    else S
  | .forceTransfer who src dst amt call =>
    match moveBal S.w.L (.force who) src dst amt with
    | none => S
    | some L' => { S with w := { S.w with L := L' }, calls := pushCall S.calls call src dst amt }
  | .resolveTransfer k req =>
    match S.calls[k]? with
    | none => S
    | some x =>
      match resolveTransfer S.w.L x req with
      | none => { S with calls := S.calls.eraseIdx k }
      | some L' => { S with w := { S.w with L := L' }, calls := S.calls.eraseIdx k }
  | .resolveTransferFails k => { S with calls := S.calls.eraseIdx k }
  | .payload now p sig =>
    if G.valid p.key p sig = true ∧ admit G.implicit G.base.me now S.w.L.ctl S.auth p = true then
      match runOps G ex p.signer { S with auth := commitNonce S.auth p } p.ops with
      | none => S
      | some S' => S'
    else S
  | .addKey a k =>
    if S.w.L.ctl.authOff.contains a = true then S
    else
      match addKey G.implicit S.w.L.ctl S.auth a k with
      | none => S
      | some A => { S with auth := A }
  | .removeKey a k =>
    if S.w.L.ctl.authOff.contains a = true then S
    else
      match removeKey G.implicit S.w.L.ctl S.auth a k with
      | none => S
      | some A => { S with auth := A }
  | .acl c =>
    { S with
      supers := (aclStep S.acl c).supers
      admins := (aclStep S.acl c).admins
      w := step G.base ex S.w (.admin (.acl (aclStep S.acl c).roles)) }

/-- The standard token. -/
abbrev sstd (G : SCfg) (S : SWorld) (st : SStep) : SWorld :=
  sstep G (ProvedFT.exec G.base.tok) S st

/-- The start: the start of `Intents/World.lean`, no transfer call in flight. The keys, the
    nonces and the role table (super-admins, admins, grantees) are whatever they are. -/
structure SInit (G : SCfg) (S : SWorld) : Prop where
  base : Init G.base S.w
  calls : S.calls = []

/-- `SReach G S0 S`: `S` is reached from the start `S0` by steps of the strict world. -/
inductive SReach (G : SCfg) : SWorld → SWorld → Prop
  | init (S : SWorld) (h : SInit G S) : SReach G S S
  | step {S0 S : SWorld} (st : SStep) : SReach G S0 S → SReach G S0 (sstd G S st)

/-- Run a list of strict steps. -/
def srun (G : SCfg) (ex : St → Rcpt → Option Out) (S : SWorld) (l : List SStep) : SWorld :=
  l.foldl (sstep G ex) S

end Intents
