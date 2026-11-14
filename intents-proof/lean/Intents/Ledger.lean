/-
  The token ledger of the NEAR Intents contract (near/intents, contracts/defuse, commit
  16d04f6ec4401263f8914638710260da50bb46b0, version 0.4.5) for one NEP-141 token `T`:
  the balances the contract keeps under the token id `nep141:T`, their total, and the
  switches that guard the deposit and withdrawal methods.

  Sources mirrored (paths under contracts/defuse/src/contract):
  * tokens/mod.rs               `deposit` (18-74), `withdraw` (76-128)
  * tokens/nep141/withdraw.rs   `ft_withdraw`, `internal_ft_withdraw`, `ft_resolve_withdraw`,
                                `ft_force_withdraw`
  * tokens/nep141/deposit.rs    `ft_on_transfer`
  * accounts/mod.rs, accounts/force.rs, lock.rs (core)   lock and auth-by-predecessor flags
  * mod.rs                      roles, `#[pausable(...)]`
  * crates/near/utils/src/promise.rs   `promise_result_checked_void`, `promise_result_checked_json`

  Amounts are natural numbers; every `checked_*` of the code is an explicit guard. `none` means
  the call fails, and a failed call changes nothing.
-/
import ProvedFT.Theorems
import Intents.Basic
import Intents.Json

namespace Intents
open ProvedFT (Acct Accts get bal set total PR Method Rcpt Out St Env Ret U128_MAX parseU128Json)

/-- `Role` (contract/mod.rs:51-71). -/
inductive Role where
  | DAO
  | FeesManager
  | RelayerKeysManager
  | UnrestrictedWithdrawer
  | PauseManager
  | Upgrader
  | UnpauseManager
  | UnrestrictedAccountLocker
  | UnrestrictedAccountUnlocker
  | SaltManager
  | GarbageCollector
  | UnrestrictedAccountManager
  deriving DecidableEq, Repr

/-- Access control and switches. None of them holds tokens. -/
structure Ctl where
  /-- near-plugins `AccessControllable`: which account holds which role. -/
  roles : List (Acct × Role) := []
  /-- near-plugins `Pausable`: paused feature keys (`"ft_on_transfer"`, `"ft_withdraw"`,
      `"intents"`, `"mt_transfer"`, …, `"ALL"`). -/
  paused : List String := []
  /-- Accounts locked with `force_lock_account`. -/
  locked : List Acct := []
  /-- Accounts with authentication by predecessor id disabled. -/
  authOff : List Acct := []
  deriving Repr

/-- `acl_has_any_role`. -/
def Ctl.any (c : Ctl) (a : Acct) (rs : List Role) : Bool := rs.any fun r => c.roles.contains (a, r)

/-- `pa_is_paused(key)`: the key or `"ALL"` is paused. -/
def Ctl.isPaused (c : Ctl) (key : String) : Bool :=
  c.paused.contains key || c.paused.contains "ALL"

/-- Calls that change the switches, with the role each one requires. -/
inductive Admin where
  /-- `pa_pause_feature(key)`: `DAO` or `PauseManager`. -/
  | pause (caller : Acct) (key : String)
  /-- `pa_unpause_feature(key)`: `DAO` or `UnpauseManager`. -/
  | unpause (caller : Acct) (key : String)
  /-- `force_lock_account`: `DAO`, `UnrestrictedAccountLocker` or `UnrestrictedAccountManager`. -/
  | lock (caller : Acct) (a : Acct)
  /-- `force_unlock_account`: `DAO`, `UnrestrictedAccountUnlocker` or
      `UnrestrictedAccountManager`. -/
  | unlock (caller : Acct) (a : Acct)
  /-- `disable_auth_by_predecessor_id` called by `a` itself. -/
  | authOffSelf (a : Acct)
  /-- A `SetAuthByPredecessorId` intent signed with a key of `a`. -/
  | authIntent (a : Acct) (enable : Bool)
  /-- `force_disable_auth_by_predecessor_ids` (locker roles) /
      `force_enable_auth_by_predecessor_ids` (unlocker roles). -/
  | authForce (caller : Acct) (a : Acct) (enable : Bool)
  /-- Any change of the role table through near-plugins `acl_*` methods (super-admins and role
      admins). The model does not restrict who makes it. -/
  | acl (roles : List (Acct × Role))

def setAuth (c : Ctl) (a : Acct) (enable : Bool) : Ctl :=
  if enable then { c with authOff := c.authOff.filter fun x => x != a }
  else { c with authOff := a :: c.authOff }

def adminStep (c : Ctl) : Admin → Ctl
  | .pause who key =>
    if c.any who [.DAO, .PauseManager] then { c with paused := key :: c.paused } else c
  | .unpause who key =>
    if c.any who [.DAO, .UnpauseManager] then
      { c with paused := c.paused.filter fun k => k != key }
    else c
  | .lock who a =>
    if c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager] then
      { c with locked := a :: c.locked }
    else c
  | .unlock who a =>
    if c.any who [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager] then
      { c with locked := c.locked.filter fun x => x != a }
    else c
  | .authOffSelf a =>
    if c.authOff.contains a || c.locked.contains a then c else setAuth c a false
  | .authIntent a enable => if c.locked.contains a then c else setAuth c a enable
  | .authForce who a enable =>
    if c.any who (if enable then [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager]
        else [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager]) then
      setAuth c a enable
    else c
  | .acl roles => { c with roles := roles }

/-- The ledger for the token: `accounts[a].token_balances[nep141:T]` (0 when absent),
    `total_supplies[nep141:T]`, and the switches. -/
structure Ledger where
  bals : Accts := []
  supply : Nat := 0
  ctl : Ctl := {}

/-- `Contract::deposit` (tokens/mod.rs:18-74) for one token: a zero amount is an error,
    `total_supplies.add` and `token_balances.add` are checked. Deposits to locked accounts are
    allowed. -/
def credit (L : Ledger) (a : Acct) (x : Nat) : Option Ledger :=
  if x = 0 then none
  else if L.supply + x ≤ U128_MAX ∧ bal L.bals a + x ≤ U128_MAX then
    some { L with bals := set L.bals a (bal L.bals a + x), supply := L.supply + x }
  else none

/-- `Contract::withdraw` (tokens/mod.rs:76-128) for one token: the account must not be locked
    unless `force`, a zero amount is an error, `token_balances.sub` and `total_supplies.sub`
    are checked. -/
def debit (L : Ledger) (a : Acct) (x : Nat) (force : Bool) : Option Ledger :=
  if x = 0 then none
  else if L.ctl.locked.contains a = true ∧ force = false then none
  else if x ≤ bal L.bals a ∧ x ≤ L.supply then
    some { L with bals := set L.bals a (bal L.bals a - x), supply := L.supply - x }
  else none

/-- The arguments of one withdrawal (`FtWithdraw`, core/src/intents/tokens.rs:139-168), with the
    account that is debited. -/
structure Wd where
  owner : Acct
  receiver : Acct
  amount : Nat
  memo : Option String := none
  /-- `some msg`: the contract sends `ft_transfer_call`; `none`: `ft_transfer`. -/
  msg : Option String := none
  /-- `storage_deposit` (yoctoNEAR): only an `FtWithdraw` intent can set it. -/
  sd : Option Nat := none
  deriving Repr, DecidableEq

/-- Who starts a withdrawal. -/
inductive Via where
  /-- `ft_withdraw` called by `pred` with 1 yoctoNEAR (withdraw.rs:25-50). -/
  | method (pred : Acct)
  /-- An `FtWithdraw` intent signed with a key registered for `w.owner`, run by
      `execute_intents` (signature checking is not modelled). -/
  | intent
  /-- `ft_force_withdraw` called by `caller` with 1 yoctoNEAR (withdraw.rs:199-225). -/
  | force (caller : Acct)

def Via.ok (c : Ctl) (w : Wd) : Via → Bool
  | .method p =>
    p == w.owner && w.sd.isNone && !c.isPaused "ft_withdraw" && !c.authOff.contains p
  | .intent => !c.isPaused "intents"
  | .force who => c.any who [.DAO, .UnrestrictedWithdrawer] && w.sd.isNone

def Via.forced : Via → Bool
  | .force _ => true
  | _ => false

/-- `internal_ft_withdraw`, the ledger part: guards of the entry point, then `withdraw`.
    `amount` is a `u128` argument. -/
def startWithdraw (L : Ledger) (via : Via) (w : Wd) : Option Ledger :=
  if via.ok L.ctl w = true ∧ w.amount ≤ U128_MAX then debit L w.owner w.amount via.forced
  else none

/-- `U128::max_json_length_root(())` (crates/near/utils/src/promise.rs:82-88). -/
def U128_JSON_MAX : Nat := 44

/-- An `ft_resolve_withdraw(token, sender_id = owner, amount, is_call)` callback that is ready to
    run: its arguments and the promise result it will read. -/
structure Rs where
  owner : Acct
  amount : Nat
  isCall : Bool
  res : PR
  /-- Bookkeeping only (no guard or effect of the model reads it): how much of `amount` has left
      the contract's token balance for good, measured on the token's state. -/
  left : Nat

/-- `used` in `ft_resolve_withdraw` (withdraw.rs:164-181).
    `is_call`: `promise_result_checked_json::<U128>(0)` — a failed or too long result counts as
    fully used, an unparsable one as nothing used, a number is capped by `amount`.
    Otherwise `promise_result_checked_void(0)`: used in full exactly when the promise succeeded
    with an empty value. -/
def Rs.used (r : Rs) : Nat :=
  if r.isCall then
    match r.res with
    | .failed => r.amount
    | .ok b =>
      if b.length ≤ U128_JSON_MAX then
        (match parseU128Json b with
         | some v => min v r.amount
         | none => 0)
      else r.amount
  else
    match r.res with
    | .ok [] => r.amount
    | _ => 0

/-- `refund = amount.saturating_sub(used)`. -/
def Rs.refund (r : Rs) : Nat := r.amount - r.used

/-- What is still owed for a ready callback: the part of `amount` that has not left. -/
def Rs.unsettled (r : Rs) : Nat := r.amount - r.left

/-- `ft_resolve_withdraw`: deposit the refund to the owner if it is positive. -/
def resolveWithdraw (L : Ledger) (r : Rs) : Option Ledger :=
  if r.refund = 0 then some L else credit L r.owner r.refund

/-- Who moves a balance inside the ledger. -/
inductive MoveAuth where
  /-- Authorised by the source account: `mt_transfer`, `mt_batch_transfer`, `mt_transfer_call`,
      `mt_batch_transfer_call` called by it, or a `Transfer` / `TokenDiff` intent signed with one
      of its keys (signature checking is not modelled). -/
  | owner
  /-- `mt_resolve_transfer`: the refund of an `mt_transfer_call`, taken back from its receiver. -/
  | refund
  /-- `mt_force_transfer`, `mt_force_batch_transfer`, `mt_force_transfer_call`,
      `mt_force_batch_transfer_call` called by `caller`. -/
  | force (caller : Acct)

def MoveAuth.ok (c : Ctl) (src : Acct) : MoveAuth → Bool
  | .owner => !c.locked.contains src
  | .refund => true
  | .force who => c.any who [.DAO, .UnrestrictedWithdrawer]

/-- An internal operation on the token's balances: `amt` moves from `src` to `dst`. The total
    is untouched (`internal_sub_balance` / `internal_add_balance` do not write
    `total_supplies`). -/
def moveBal (L : Ledger) (auth : MoveAuth) (src dst : Acct) (amt : Nat) : Option Ledger :=
  if src = dst ∨ amt = 0 then none
  else if auth.ok L.ctl src = true ∧ amt ≤ bal L.bals src ∧ bal L.bals dst + amt ≤ U128_MAX then
    some { L with bals := set (set L.bals src (bal L.bals src - amt)) dst (bal L.bals dst + amt) }
  else none

/-! ### Specifications of the ledger functions -/

theorem credit_some {L L' : Ledger} {a : Acct} {x : Nat} (h : credit L a x = some L') :
    0 < x ∧ L.supply + x ≤ U128_MAX ∧ bal L.bals a + x ≤ U128_MAX ∧
    L' = { L with bals := set L.bals a (bal L.bals a + x), supply := L.supply + x } := by
  unfold credit at h
  by_cases hx : x = 0
  · simp [hx] at h
  · rw [ifN hx] at h
    by_cases hc : L.supply + x ≤ U128_MAX ∧ bal L.bals a + x ≤ U128_MAX
    · rw [ifP hc] at h
      exact ⟨Nat.pos_of_ne_zero hx, hc.1, hc.2, (Option.some.inj h).symm⟩
    · rw [ifN hc] at h; exact absurd h (by simp)

theorem credit_of {L : Ledger} {a : Acct} {x : Nat} (hx : 0 < x) (h1 : L.supply + x ≤ U128_MAX)
    (h2 : bal L.bals a + x ≤ U128_MAX) :
    credit L a x = some { L with bals := set L.bals a (bal L.bals a + x), supply := L.supply + x } := by
  unfold credit
  rw [ifN (by omega), ifP ⟨h1, h2⟩]

theorem debit_some {L L' : Ledger} {a : Acct} {x : Nat} {f : Bool} (h : debit L a x f = some L') :
    0 < x ∧ ¬(L.ctl.locked.contains a = true ∧ f = false) ∧ x ≤ bal L.bals a ∧ x ≤ L.supply ∧
    L' = { L with bals := set L.bals a (bal L.bals a - x), supply := L.supply - x } := by
  unfold debit at h
  by_cases hx : x = 0
  · simp [hx] at h
  · rw [ifN hx] at h
    by_cases hl : L.ctl.locked.contains a = true ∧ f = false
    · rw [ifP hl] at h; exact absurd h (by simp)
    · rw [ifN hl] at h
      by_cases hc : x ≤ bal L.bals a ∧ x ≤ L.supply
      · rw [ifP hc] at h
        exact ⟨Nat.pos_of_ne_zero hx, hl, hc.1, hc.2, (Option.some.inj h).symm⟩
      · rw [ifN hc] at h; exact absurd h (by simp)

theorem startWithdraw_some {L L' : Ledger} {via : Via} {w : Wd}
    (h : startWithdraw L via w = some L') :
    via.ok L.ctl w = true ∧ w.amount ≤ U128_MAX ∧ debit L w.owner w.amount via.forced = some L' := by
  unfold startWithdraw at h
  by_cases hc : via.ok L.ctl w = true ∧ w.amount ≤ U128_MAX
  · rw [ifP hc] at h; exact ⟨hc.1, hc.2, h⟩
  · rw [ifN hc] at h; exact absurd h (by simp)

theorem moveBal_some {L L' : Ledger} {auth : MoveAuth} {src dst : Acct} {amt : Nat}
    (h : moveBal L auth src dst amt = some L') :
    src ≠ dst ∧ 0 < amt ∧ auth.ok L.ctl src = true ∧ amt ≤ bal L.bals src ∧
    bal L.bals dst + amt ≤ U128_MAX ∧
    L' = { L with bals := set (set L.bals src (bal L.bals src - amt)) dst (bal L.bals dst + amt) } := by
  unfold moveBal at h
  by_cases h0 : src = dst ∨ amt = 0
  · rw [ifP h0] at h; exact absurd h (by simp)
  · rw [ifN h0] at h
    by_cases hc : auth.ok L.ctl src = true ∧ amt ≤ bal L.bals src ∧ bal L.bals dst + amt ≤ U128_MAX
    · rw [ifP hc] at h
      refine ⟨fun e => h0 (Or.inl e), ?_, hc.1, hc.2.1, hc.2.2, (Option.some.inj h).symm⟩
      exact Nat.pos_of_ne_zero (fun e => h0 (Or.inr e))
    · rw [ifN hc] at h; exact absurd h (by simp)

theorem used_le (r : Rs) : r.used ≤ r.amount := by
  unfold Rs.used
  split
  · split
    · exact Nat.le_refl _
    · split
      · split
        · exact Nat.min_le_right _ _
        · exact Nat.zero_le _
      · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact Nat.zero_le _

theorem refund_le (r : Rs) : r.refund ≤ r.amount := Nat.sub_le _ _

/-- A failed `ft_transfer_call` promise: nothing is refunded. -/
theorem refund_call_failed (o : Acct) (a l : Nat) : (Rs.mk o a true .failed l).refund = 0 := by
  simp [Rs.refund, Rs.used]

/-- A failed `ft_transfer` promise: everything is refunded. -/
theorem refund_plain_failed (o : Acct) (a l : Nat) : (Rs.mk o a false .failed l).refund = a := by
  simp [Rs.refund, Rs.used]

/-- A successful `ft_transfer` (empty value): nothing is refunded. -/
theorem refund_plain_ok (o : Acct) (a l : Nat) : (Rs.mk o a false (.ok []) l).refund = 0 := by
  simp [Rs.refund, Rs.used]

/-- `ft_transfer_call` returned the number `u ≤ amount`, written by near-sdk: the refund is
    `amount - u`. -/
theorem refund_call_num (o : Acct) (a l u : Nat) (hu : u ≤ a) (ha : a ≤ U128_MAX) :
    (Rs.mk o a true (.ok (encU128 u)) l).refund = a - u := by
  have hl : (encU128 u).length ≤ U128_JSON_MAX := by
    have := enc_length u; unfold U128_JSON_MAX; omega
  have hp := parse_enc u (by omega)
  simp only [Rs.refund, Rs.used, hl, hp, ite_true]
  rw [Nat.min_eq_left hu]

end Intents
