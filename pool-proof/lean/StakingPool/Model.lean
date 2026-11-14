/-
  Executable model of the NEAR core staking pool contract
  (near/core-contracts, staking-pool, commit 1cacc9d, v0.4.0),
  deployed by poolv1.near with code hash J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY.

  Every method is a function `Contract → Env → Except String (Contract × Eff)`:
  * `Except.error msg` = the call panics (assert / overflow / host error); the runtime
    then reverts the whole function call, so the contract state is unchanged and an
    attached deposit is refunded.
  * Integers are `Nat` with explicit u128/u64 range checks, because the crate is built
    with `overflow-checks = true` (an overflow panics = method failure). U256
    intermediate products never overflow (u128 * u128 < 2^256), only `as_u128` can fail.
  * The environment values a call reads (`env::epoch_height`, `env::account_balance`
    incl. the attached deposit, `env::account_locked_balance`, `env::attached_deposit`,
    `env::predecessor_account_id`) are explicit inputs (`Env`).
  * Promises are returned as effects (`Eff`): the transfer to the predecessor, the stake
    action on the pool itself, the owner's vote call. A transfer larger than the
    account's liquid balance fails inside the call (`HostError::BalanceExceeded`); a
    stake action with a key the protocol rejects for staking fails receipt validation
    (`UnsuitableStakingKey`) and reverts the call, so it is modelled as a failure too.
-/
namespace StakingPool

abbrev AccountId := String

/-- `u128::MAX` -/
def U128_MAX : Nat := 340282366920938463463374607431768211455
/-- `u64::MAX` -/
def U64_MAX : Nat := 18446744073709551615
/-- `STAKE_SHARE_PRICE_GUARANTEE_FUND`: 10^12 yocto. -/
def FUND : Nat := 1000000000000
/-- `NUM_EPOCHS_TO_UNLOCK` -/
def NUM_EPOCHS_TO_UNLOCK : Nat := 4

abbrev M := Except String

/-! ## Rust integer semantics (overflow-checks = true) -/

def add128 (a b : Nat) : M Nat :=
  if a + b ≤ U128_MAX then pure (a + b) else throw "attempt to add with overflow"

def sub128 (a b : Nat) : M Nat :=
  if b ≤ a then pure (a - b) else throw "attempt to subtract with overflow"

def add64 (a b : Nat) : M Nat :=
  if a + b ≤ U64_MAX then pure (a + b) else throw "attempt to add with overflow"

/-- `U256::as_u128` panics when the value does not fit. -/
def asU128 (x : Nat) : M Nat :=
  if x ≤ U128_MAX then pure x else throw "Integer overflow when casting to u128"

/-- `assert!(p, msg)` -/
def ensure (p : Prop) [Decidable p] (msg : String) : M Unit :=
  if p then pure () else throw msg

/-! ## State -/

/-- `Account` (inner account of a delegator). -/
structure Account where
  unstaked : Nat := 0
  stakeShares : Nat := 0
  availEpoch : Nat := 0
deriving Repr, DecidableEq, Inhabited

def Account.zero : Account := {}

/-- `internal_save_account`: an entry with zero unstaked balance and zero shares is
removed from the map, so it reads back as `Account::default()`. -/
def Account.norm (a : Account) : Account :=
  if a.unstaked = 0 ∧ a.stakeShares = 0 then Account.zero else a

/-- The `accounts` map: a total function (missing entry = default account) plus the
list of every id ever written (the support; stored entries are the nonzero ones). -/
structure Accts where
  f : AccountId → Account
  keys : List AccountId

def Accts.empty : Accts := ⟨fun _ => Account.zero, []⟩

def Accts.get (a : Accts) (id : AccountId) : Account := a.f id

def Accts.save (a : Accts) (id : AccountId) (acc : Account) : Accts :=
  { f := fun k => if k = id then acc.norm else a.f k,
    keys := if id ∈ a.keys then a.keys else id :: a.keys }

/-- Sum of `g` over all accounts (over the support). -/
def Accts.sum (a : Accts) (g : Account → Nat) : Nat :=
  (a.keys.map (fun k => g (a.f k))).sum

structure Fee where
  num : Nat
  den : Nat
deriving Repr, DecidableEq, Inhabited

/-- `RewardFeeFraction::assert_valid` -/
def Fee.assertValid (f : Fee) : M Unit := do
  ensure (f.den ≠ 0) "Denominator must be a positive number"
  ensure (f.num ≤ f.den) "The reward fee must be less or equal to 1"

/-- `RewardFeeFraction::multiply`: `(U256(num) * U256(value) / U256(den)).as_u128()` -/
def Fee.multiply (f : Fee) (v : Nat) : M Nat :=
  if f.den = 0 then throw "division by zero" else asU128 (f.num * v / f.den)

/-- `StakingContract` -/
structure Contract where
  owner : AccountId
  key : String
  lastEpoch : Nat
  /-- `last_total_balance` -/
  ltb : Nat
  /-- `total_stake_shares` -/
  ts : Nat
  /-- `total_staked_balance` -/
  s : Nat
  fee : Fee
  accts : Accts
  paused : Bool

/-- What a function call reads from the runtime. -/
structure Env where
  /-- `env::current_account_id()` (the pool) -/
  self : AccountId
  /-- `env::predecessor_account_id()` -/
  pred : AccountId
  /-- `env::epoch_height()` -/
  epoch : Nat
  /-- `env::account_balance()` (liquid balance, already including the attached deposit) -/
  balance : Nat
  /-- `env::account_locked_balance()` -/
  locked : Nat
  /-- `env::attached_deposit()` -/
  deposit : Nat

/-- Promises a successful call leaves behind. -/
structure Eff where
  /-- NEAR transferred to the predecessor (`Promise::new(account_id).transfer`) -/
  transfer : Nat := 0
  /-- stake action on the pool itself with this amount -/
  stake : Option Nat := none
  /-- owner's `vote(is_vote)` call to a voting contract -/
  vote : Option (AccountId × Bool) := none
  /-- ghost: reward distributed by this call's `internal_ping` -/
  reward : Nat := 0

/-! ## Rounding helpers (exactly as in internal.rs) -/

def Contract.sharesDown (c : Contract) (amount : Nat) : M Nat := do
  ensure (c.s ≠ 0) "The total staked balance can't be 0"
  asU128 (c.ts * amount / c.s)

def Contract.sharesUp (c : Contract) (amount : Nat) : M Nat := do
  ensure (c.s ≠ 0) "The total staked balance can't be 0"
  asU128 ((c.ts * amount + (c.s - 1)) / c.s)

def Contract.amountDown (c : Contract) (shares : Nat) : M Nat := do
  ensure (c.ts ≠ 0) "The total number of stake shares can't be 0"
  asU128 (c.s * shares / c.ts)

def Contract.amountUp (c : Contract) (shares : Nat) : M Nat := do
  ensure (c.ts ≠ 0) "The total number of stake shares can't be 0"
  asU128 ((c.s * shares + (c.ts - 1)) / c.ts)

def Contract.get (c : Contract) (id : AccountId) : Account := c.accts.get id

def Contract.save (c : Contract) (id : AccountId) (a : Account) : Contract :=
  { c with accts := c.accts.save id a }

/-! ## Internal methods -/

/-- Owner's fee shares: `account.stake_shares += num_shares; total_stake_shares += num_shares`. -/
def Contract.payOwner (c : Contract) (n : Nat) : M Contract := do
  let a := c.get c.owner
  let sh ← add128 a.stakeShares n
  let c := c.save c.owner { a with stakeShares := sh }
  let ts ← add128 c.ts n
  pure { c with ts := ts }

/-- The reward-distribution part of `internal_ping` (`total_reward > 0`). -/
def Contract.distribute (c : Contract) (reward : Nat) : M Contract := do
  let ownersFee ← c.fee.multiply reward
  let remaining ← sub128 reward ownersFee
  let s1 ← add128 c.s remaining
  let c := { c with s := s1 }
  let n ← c.sharesDown ownersFee
  let c ← (if n > 0 then c.payOwner n else pure c)
  let s2 ← add128 c.s ownersFee
  pure { c with s := s2 }

/-- `internal_ping`: returns the new state and whether the epoch changed. -/
def Contract.ping (c : Contract) (e : Env) : M (Contract × Bool) :=
  if c.lastEpoch = e.epoch then pure (c, false) else do
  let c := { c with lastEpoch := e.epoch }
  let tb0 ← add128 e.locked e.balance
  let tb ← sub128 tb0 e.deposit
  ensure (c.ltb ≤ tb) "The new total balance should not be less than the old total balance"
  let reward := tb - c.ltb
  let c ← (if reward > 0 then c.distribute reward else pure c)
  pure ({ c with ltb := tb }, true)

/-- `internal_restake`: the stake action on the pool, unless paused. -/
def Contract.restake (c : Contract) (vk : String → Bool) : M (Option Nat) :=
  if c.paused then pure none
  else if vk c.key then pure (some c.s) else throw "UnsuitableStakingKey"

/-- `internal_deposit` -/
def Contract.depositInt (c : Contract) (e : Env) : M (Contract × Nat) := do
  let a := c.get e.pred
  let u ← add128 a.unstaked e.deposit
  let c := c.save e.pred { a with unstaked := u }
  let ltb ← add128 c.ltb e.deposit
  return ({ c with ltb := ltb }, e.deposit)

/-- `internal_withdraw` -/
def Contract.withdrawInt (c : Contract) (e : Env) (amount : Nat) : M Contract := do
  ensure (amount ≠ 0) "Withdrawal amount should be positive"
  let a := c.get e.pred
  ensure (amount ≤ a.unstaked) "Not enough unstaked balance to withdraw"
  ensure (a.availEpoch ≤ e.epoch)
    "The unstaked balance is not yet available due to unstaking delay"
  let c := c.save e.pred { a with unstaked := a.unstaked - amount }
  -- `Promise::new(account_id).transfer(amount)`: deducted from the liquid balance now
  -- (nearcore `HostError::BalanceExceeded`, displayed as "Exceeded the account balance.")
  ensure (amount ≤ e.balance) "Exceeded the account balance."
  let ltb ← sub128 c.ltb amount
  pure { c with ltb := ltb }

/-- `internal_stake` -/
def Contract.stakeInt (c : Contract) (e : Env) (amount : Nat) : M Contract := do
  ensure (amount ≠ 0) "Staking amount should be positive"
  let a := c.get e.pred
  let n ← c.sharesDown amount
  ensure (n ≠ 0)
    "The calculated number of \"stake\" shares received for staking should be positive"
  let charge ← c.amountDown n
  ensure (charge ≠ 0)
    "Invariant violation. Calculated staked amount must be positive, because \"stake\" share price should be at least 1"
  ensure (charge ≤ a.unstaked) "Not enough unstaked balance to stake"
  let sh ← add128 a.stakeShares n
  let c := c.save e.pred { a with unstaked := a.unstaked - charge, stakeShares := sh }
  let stakeAmt ← c.amountUp n
  let s ← add128 c.s stakeAmt
  let ts ← add128 c.ts n
  pure { c with s := s, ts := ts }

/-- `inner_unstake` -/
def Contract.unstakeInt (c : Contract) (e : Env) (amount : Nat) : M Contract := do
  ensure (amount ≠ 0) "Unstaking amount should be positive"
  let a := c.get e.pred
  ensure (c.s ≠ 0) "The contract doesn't have staked balance"
  let n ← c.sharesUp amount
  ensure (n ≠ 0)
    "Invariant violation. The calculated number of \"stake\" shares for unstaking should be positive"
  ensure (n ≤ a.stakeShares) "Not enough staked balance to unstake"
  let recv ← c.amountUp n
  ensure (recv ≠ 0)
    "Invariant violation. Calculated staked amount must be positive, because \"stake\" share price should be at least 1"
  let u ← add128 a.unstaked recv
  let av ← add64 e.epoch NUM_EPOCHS_TO_UNLOCK
  let c := c.save e.pred { a with stakeShares := a.stakeShares - n, unstaked := u, availEpoch := av }
  let unstakeAmt ← c.amountDown n
  let s ← sub128 c.s unstakeAmt
  let ts ← sub128 c.ts n
  pure { c with s := s, ts := ts }

/-! ## near-sdk 1.0.0 `env::is_valid_account_id` -/

def isSepChar (c : Char) : Bool := c = '-' || c = '_' || c = '.'
def isAlnumChar (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

/-- Scan with "last char was a separator" flag; `none` = invalid character / double separator. -/
def validScan : List Char → Bool → Option Bool
  | [], last => some last
  | c :: cs, last =>
    if isAlnumChar c then validScan cs false
    else if isSepChar c then (if last then none else validScan cs true)
    else none

def validAccountId (id : String) : Bool :=
  let n := id.utf8ByteSize
  if n < 2 || n > 64 then false
  else match validScan id.toList true with
    | some last => !last
    | none => false

/-! ## Public methods -/

inductive Method where
  | ping
  | deposit
  | depositAndStake
  | withdrawAll
  | withdraw (amount : Nat)
  | stakeAll
  | stake (amount : Nat)
  | unstakeAll
  | unstake (amount : Nat)
  | updateStakingKey (key : String)
  | updateFee (f : Fee)
  | vote (acct : AccountId) (isVote : Bool)
  | pauseStaking
  | resumeStaking
  | onStakeAction
  | reinit
deriving Repr, Inhabited

/-- `assert_owner` -/
def assertOwner (c : Contract) (e : Env) : M Unit :=
  ensure (e.pred = c.owner) "Can only be called by the owner"

/-- near-sdk 1.0.0 `#[near_bindgen]`: methods without `#[payable]` panic on an attached
deposit before running their body. -/
def Method.payable : Method → Bool
  | .deposit => true
  | .depositAndStake => true
  | _ => false

/-- The body of one function call of a public method. `vk` = which keys the protocol
accepts as staking keys (ED25519 keys that decode to a valid curve point).
`Eff.reward` records the reward the call's `internal_ping` distributed (ghost data
for the environment model; it does not influence the contract). -/
def execBody (vk : String → Bool) (c : Contract) (e : Env) : Method → M (Contract × Eff)
  | .ping => do
    let (c1, need) ← c.ping e
    let st ← (if need then c1.restake vk else pure none)
    return (c1, { stake := st, reward := c1.s - c.s })
  | .deposit => do
    let (c1, need) ← c.ping e
    let (c2, _) ← c1.depositInt e
    let st ← (if need then c2.restake vk else pure none)
    return (c2, { stake := st, reward := c1.s - c.s })
  | .depositAndStake => do
    let (c1, _) ← c.ping e
    let (c2, amount) ← c1.depositInt e
    let c3 ← c2.stakeInt e amount
    let st ← c3.restake vk
    return (c3, { stake := st, reward := c1.s - c.s })
  | .withdrawAll => do
    let (c1, need) ← c.ping e
    let amount := (c1.get e.pred).unstaked
    let c2 ← c1.withdrawInt e amount
    let st ← (if need then c2.restake vk else pure none)
    return (c2, { transfer := amount, stake := st, reward := c1.s - c.s })
  | .withdraw amount => do
    let (c1, need) ← c.ping e
    let c2 ← c1.withdrawInt e amount
    let st ← (if need then c2.restake vk else pure none)
    return (c2, { transfer := amount, stake := st, reward := c1.s - c.s })
  | .stakeAll => do
    let (c1, _) ← c.ping e
    let c2 ← c1.stakeInt e (c1.get e.pred).unstaked
    let st ← c2.restake vk
    return (c2, { stake := st, reward := c1.s - c.s })
  | .stake amount => do
    let (c1, _) ← c.ping e
    let c2 ← c1.stakeInt e amount
    let st ← c2.restake vk
    return (c2, { stake := st, reward := c1.s - c.s })
  | .unstakeAll => do
    let (c1, _) ← c.ping e
    let amount ← c1.amountDown (c1.get e.pred).stakeShares
    let c2 ← c1.unstakeInt e amount
    let st ← c2.restake vk
    return (c2, { stake := st, reward := c1.s - c.s })
  | .unstake amount => do
    let (c1, _) ← c.ping e
    let c2 ← c1.unstakeInt e amount
    let st ← c2.restake vk
    return (c2, { stake := st, reward := c1.s - c.s })
  | .updateStakingKey k => do
    assertOwner c e
    let (c1, _) ← c.ping e
    let c2 := { c1 with key := k }
    let st ← c2.restake vk
    return (c2, { stake := st, reward := c1.s - c.s })
  | .updateFee f => do
    assertOwner c e
    f.assertValid
    let (c1, need) ← c.ping e
    let c2 := { c1 with fee := f }
    let st ← (if need then c2.restake vk else pure none)
    return (c2, { stake := st, reward := c1.s - c.s })
  | .vote acct isVote => do
    assertOwner c e
    ensure (validAccountId acct = true) "Invalid voting account ID"
    return (c, { vote := some (acct, isVote) })
  | .pauseStaking => do
    assertOwner c e
    ensure (c.paused = false) "The staking is already paused"
    let (c1, _) ← c.ping e
    let c2 := { c1 with paused := true }
    -- `Promise::new(env::current_account_id()).stake(0, self.stake_public_key.clone())`
    ensure (vk c2.key = true) "UnsuitableStakingKey"
    return (c2, { stake := some 0, reward := c1.s - c.s })
  | .resumeStaking => do
    assertOwner c e
    ensure (c.paused = true) "The staking is not paused"
    let (c1, _) ← c.ping e
    let c2 := { c1 with paused := false }
    let st ← c2.restake vk
    return (c2, { stake := st, reward := c1.s - c.s })
  | .onStakeAction => do
    -- callable only by the pool itself as the callback of its own stake action;
    -- it never changes the contract state (it may only issue `stake(0)`).
    ensure (e.pred = e.self) "Can be called only as a callback"
    return (c, {})
  | .reinit => throw "Already initialized"

/-- One function call of a public method (payable check, then the body). -/
def exec (vk : String → Bool) (c : Contract) (e : Env) (m : Method) : M (Contract × Eff) := do
  ensure (m.payable = true ∨ e.deposit = 0) "Method doesn't accept deposit"
  execBody vk c e m

/-- `new` (the `#[init]` method), on an account without contract state. -/
def init (vk : String → Bool) (e : Env) (owner key : String) (fee : Fee) : M (Contract × Eff) := do
  ensure (e.deposit = 0) "Method doesn't accept deposit"
  fee.assertValid
  ensure (validAccountId owner = true) "The owner account ID is invalid"
  let s ← sub128 e.balance FUND
  ensure (e.locked = 0) "The staking pool shouldn't be staking at the initialization"
  let c : Contract :=
    { owner := owner, key := key, lastEpoch := e.epoch, ltb := e.balance, ts := s, s := s,
      fee := fee, accts := Accts.empty, paused := false }
  let st ← c.restake vk
  return (c, { stake := st })

/-! ## View methods -/

/-- `get_account`: (unstaked_balance, staked_balance rounded down, can_withdraw). -/
def viewAccount (c : Contract) (epoch : Nat) (id : AccountId) : M (Nat × Nat × Bool) := do
  let a := c.get id
  let st ← c.amountDown a.stakeShares
  return (a.unstaked, st, decide (a.availEpoch ≤ epoch))

/-- Stored (nonzero) accounts, as `get_number_of_accounts` counts them. -/
def storedIds (c : Contract) : List AccountId :=
  (c.accts.keys.eraseDups).filter (fun k => c.get k != Account.zero)

end StakingPool
