/-
  Model of the deployed wrap.near contract (code hash DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1,
  near/core-contracts 54f8267 `w-near/`, near-sdk 3.1.0, near-contract-standards 3.1.0).

  Sources mirrored (line references are to the 3.1.0 crates):
  * `w-near/src/w_near.rs`             near_deposit, near_withdraw
  * `fungible_token/core_impl.rs`      internal_deposit / internal_withdraw / internal_transfer,
                                       ft_transfer, ft_transfer_call, internal_ft_resolve_transfer
  * `fungible_token/storage_impl.rs`   storage_deposit, storage_withdraw, internal_storage_unregister
  * `fungible_token/macros.rs`         `#[private]` on ft_resolve_transfer, `#[payable]` wrappers
  * near-sdk-core 3.1.0 code generator: `#[private]` = `current_account_id == predecessor_account_id`,
    a non-payable non-view method panics on a deposit, `#[init]` panics when state exists,
    view methods accept deposits.

  Every amount is a natural number; u128 arithmetic is exact because the release profile has
  `overflow-checks = true`: an overflow panics, i.e. the call fails and changes nothing. The model
  returns `none` for a failed call.
-/
import WNear.Map

namespace WNear

def U128_MAX : Nat := 340282366920938463463374607431768211455

/-- Parameters of the deployment. -/
structure Env where
  /-- The contract account (`wrap.near`). -/
  self : Acct
  /-- `storage_balance_bounds().min` = `account_storage_usage * storage_byte_cost`
      (1.25e21 yoctoNEAR on mainnet: 125 bytes at 1e19). -/
  minBal : Nat
  /-- Storage stake of everything except the account entries: code, the `STATE` record,
      the account record (yoctoNEAR). -/
  base : Nat
  /-- Storage stake of one entry of `accounts` (yoctoNEAR): `(61 + len id) * 1e19` on mainnet. -/
  entry : Acct → Nat
  /-- An upper bound on any NEAR balance: the total NEAR supply (< 2^127 yocto). -/
  cap : Nat

/-- Assumptions on the parameters (all hold on mainnet: minBal = 1.25e21, entry ≤ 125 bytes
    because account ids have at most 64 characters, total NEAR supply ≈ 1.25e33 yocto). -/
structure Env.Sane (E : Env) : Prop where
  min_pos : 0 < E.minBal
  entry_le : ∀ a, E.entry a ≤ E.minBal
  cap_lt : E.cap + 1 ≤ U128_MAX
  min_lt : E.minBal + 1 ≤ U128_MAX

/-- Contract state: the `accounts` LookupMap, `total_supply`, and the contract's NEAR balance. -/
structure St where
  accts : Accts
  supply : Nat
  near : Nat

/-- The promise result `ft_resolve_transfer` reads (`env::promise_result(0)`).
    `ok parsed`: `Successful(bytes)`; `parsed` is `serde_json::from_slice::<U128>(bytes)`
    (`none` when the bytes are not a JSON string holding a u128). -/
inductive PR where
  | failed
  | ok (parsed : Option Nat)

inductive Method where
  | new
  | near_deposit
  | near_withdraw (amount : Nat)
  | ft_transfer (receiver : Acct) (amount : Nat)
  | ft_transfer_call (receiver : Acct) (amount : Nat)
  | ft_resolve_transfer (sender receiver : Acct) (amount : Nat)
  | storage_deposit (account : Option Acct)
  | storage_withdraw (amount : Option Nat)
  | storage_unregister (force : Option Bool)
  /-- ft_total_supply, ft_balance_of, ft_metadata, storage_balance_bounds,
      storage_balance_of, storage_minimum_balance called as a transaction. -/
  | view
  /-- A method the wasm does not export, or arguments that fail to deserialize. -/
  | bad

/-- One receipt executed on the contract. -/
structure Rcpt where
  pred : Acct
  deposit : Nat
  m : Method
  results : List PR

/-- Effects of a successful call. -/
structure Out where
  st : St
  /-- `Promise::new(to).transfer(amount)` actions, in order. -/
  transfers : List (Acct × Nat)
  /-- `ft_on_transfer` + `ft_resolve_transfer` promise pairs: (sender, receiver, amount). -/
  calls : List (Acct × Acct × Nat)
  /-- `ft_resolve_transfer`'s return value (the used amount). -/
  ret : Option Nat

/-! ### FungibleToken internals (core_impl.rs) -/

/-- `internal_withdraw`: panics if unregistered, if the balance is short, or on supply underflow. -/
def iWithdraw (l : Accts) (sup : Nat) (a : Acct) (x : Nat) : Option (Accts × Nat) :=
  match get l a with
  | none => none
  | some b => if x ≤ b then (if x ≤ sup then some (set l a (b - x), sup - x) else none) else none

/-- `internal_deposit`: panics if unregistered or on u128 overflow. -/
def iDeposit (l : Accts) (sup : Nat) (a : Acct) (x : Nat) : Option (Accts × Nat) :=
  match get l a with
  | none => none
  | some b =>
    if b + x ≤ U128_MAX then (if sup + x ≤ U128_MAX then some (set l a (b + x), sup + x) else none)
    else none

/-- `internal_transfer`: sender ≠ receiver, amount > 0, withdraw then deposit. -/
def iTransfer (l : Accts) (sup : Nat) (s r : Acct) (x : Nat) : Option (Accts × Nat) :=
  if s = r then none
  else if x = 0 then none
  else match iWithdraw l sup s x with
    | none => none
    | some (l1, sup1) => iDeposit l1 sup1 r x

/-- The unused amount `internal_ft_resolve_transfer` derives from the promise result:
    `min(amount, parsed)` if it parses, else the whole amount. -/
def unusedOf (amt : Nat) : PR → Nat
  | .failed => amt
  | .ok none => amt
  | .ok (some v) => min amt v

/-- The refund `ft_resolve_transfer` moves back from the receiver: `min(receiver balance,
    unused)` when both are positive, else 0. -/
def refundOf (l : Accts) (r : Acct) (amt : Nat) (res : PR) : Nat :=
  if 0 < unusedOf amt res ∧ 0 < bal l r then min (bal l r) (unusedOf amt res) else 0

/-- `internal_ft_resolve_transfer`: returns (accounts, supply, used amount).
    The receiver is debited first; the sender's balance is read afterwards. -/
def iResolve (l : Accts) (sup : Nat) (s r : Acct) (amt : Nat) (res : PR) :
    Option (Accts × Nat × Nat) :=
  if 0 < unusedOf amt res then
    if 0 < bal l r then
      let refund := min (bal l r) (unusedOf amt res)
      let l1 := set l r (bal l r - refund)
      match get l1 s with
      | some sb =>
        -- `sender_balance + refund_amount` (overflow-checked)
        if sb + refund ≤ U128_MAX then some (set l1 s (sb + refund), sup, amt - refund) else none
      | none =>
        -- sender unregistered: `self.total_supply -= refund_amount` (burn)
        if refund ≤ sup then some (l1, sup - refund, amt) else none
    else some (l, sup, amt)
  else some (l, sup, amt)

/-- The contract code: what a receipt does to the contract state (NEAR accounting is the
    runtime's, in `exec`). -/
def method (E : Env) (s : St) (r : Rcpt) : Option Out :=
  let l := s.accts
  let sup := s.supply
  let p := r.pred
  let d := r.deposit
  match r.m with
  | .new => none          -- #[init]: "The contract has already been initialized"
  | .bad => none
  | .view => some ⟨s, [], [], none⟩
  | .near_deposit =>
    if d = 0 then none    -- "Requires positive attached deposit"
    else match get l p with
      | some _ =>
        match iDeposit l sup p d with
        | none => none
        | some (l', sup') => some ⟨⟨l', sup', s.near⟩, [], [], none⟩
      | none =>
        if d < E.minBal then none   -- "ERR_DEPOSIT_TOO_SMALL"
        else match iDeposit (set l p 0) sup p (d - E.minBal) with
          | none => none
          | some (l', sup') => some ⟨⟨l', sup', s.near⟩, [], [], none⟩
  | .near_withdraw x =>
    if d ≠ 1 then none    -- assert_one_yocto
    else match iWithdraw l sup p x with
      | none => none
      | some (l', sup') =>
        if x + 1 ≤ U128_MAX then some ⟨⟨l', sup', s.near⟩, [(p, x + 1)], [], none⟩ else none
  | .ft_transfer rc x =>
    if d ≠ 1 then none
    else match iTransfer l sup p rc x with
      | none => none
      | some (l', sup') => some ⟨⟨l', sup', s.near⟩, [], [], none⟩
  | .ft_transfer_call rc x =>
    if d ≠ 1 then none
    else match iTransfer l sup p rc x with
      | none => none
      | some (l', sup') => some ⟨⟨l', sup', s.near⟩, [], [(p, rc, x)], none⟩
  | .ft_resolve_transfer sn rc amt =>
    if p ≠ E.self then none   -- #[private]: "Method ft_resolve_transfer is private"
    else if d ≠ 0 then none   -- not #[payable]
    else match r.results with
      | [res] =>
        match iResolve l sup sn rc amt res with
        | none => none
        | some (l', sup', used) => some ⟨⟨l', sup', s.near⟩, [], [], some used⟩
      | _ => none
  | .storage_deposit acc =>
    let a := acc.getD p
    match get l a with
    | some _ => some ⟨s, (if 0 < d then [(p, d)] else []), [], none⟩
    | none =>
      if d < E.minBal then none
      else some ⟨⟨set l a 0, sup, s.near⟩,
        (if 0 < d - E.minBal then [(p, d - E.minBal)] else []), [], none⟩
  | .storage_withdraw amt =>
    if d ≠ 1 then none
    else match get l p with
      | none => none
      | some _ =>
        match amt with
        | some a => if 0 < a then none else some ⟨s, [], [], none⟩
        | none => some ⟨s, [], [], none⟩
  | .storage_unregister force =>
    if d ≠ 1 then none
    else match get l p with
      | none => some ⟨s, [], [], none⟩      -- logs "not registered", returns false
      | some b =>
        if b = 0 ∨ force = some true then
          if b ≤ sup ∧ E.minBal + 1 ≤ U128_MAX then
            some ⟨⟨erase l p, sup - b, s.near⟩, [(p, E.minBal + 1)], [], none⟩
          else none
        else none   -- "Can't unregister the account with the positive balance without force"

def sumT : List (Acct × Nat) → Nat
  | [] => 0
  | (_, x) :: t => x + sumT t

/-- The runtime around the code: the attached deposit is credited, the transfer actions'
    amounts are debited (`BalanceExceeded` if short), and the account must still cover its
    storage stake (`LackBalanceForState`). A failed receipt changes nothing. -/
def exec (E : Env) (s : St) (r : Rcpt) : Option Out :=
  match method E s r with
  | none => none
  | some o =>
    if s.near + r.deposit ≤ E.cap ∧ sumT o.transfers ≤ s.near + r.deposit ∧
        E.base + stor E.entry o.st.accts ≤ s.near + r.deposit - sumT o.transfers then
      some { o with st := { o.st with near := s.near + r.deposit - sumT o.transfers } }
    else none

/-! ### The whole system: interleavings and arbitrary receivers -/

/-- Contract state, the `ft_resolve_transfer` callbacks still in flight, and every NEAR
    transfer the contract has sent. -/
structure Sys where
  c : St
  pending : List (Acct × Acct × Nat)
  paid : List (Acct × Nat)

/-- One event. Everything a receiver's `ft_on_transfer` can do is covered: its calls back into
    the contract are `call` steps (with the receiver as predecessor, in any order), and what it
    returns (any value, garbage, a panic, running out of gas) is the `res` of `resolve`. -/
inductive Step where
  /-- A receipt from another account: a signed transaction, a call from another contract, or
      another contract's `promise_then` callback carrying promise results `rs` of its choice. -/
  | call (pred : Acct) (deposit : Nat) (m : Method) (rs : List PR)
  /-- The `i`-th callback in flight runs with promise result `res`. -/
  | resolve (i : Nat) (res : PR)
  /-- The `i`-th callback fails before running (e.g. out of gas): dropped. -/
  | resolveFails (i : Nat)
  /-- NEAR arrives: a plain transfer, or the refund of a failed outgoing transfer. -/
  | nearIn (x : Nat)

def sysStep (E : Env) (S : Sys) : Step → Sys
  | .call p d m rs =>
    -- wrap.near has no access keys and its code makes no other calls to itself,
    -- so no outside receipt has the contract as predecessor.
    if p = E.self then S
    else match exec E S.c ⟨p, d, m, rs⟩ with
      | none => S
      | some o => ⟨o.st, S.pending ++ o.calls, S.paid ++ o.transfers⟩
  | .resolve i res =>
    match S.pending[i]? with
    | none => S
    | some (sn, rc, amt) =>
      match exec E S.c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ with
      | none => ⟨S.c, S.pending.eraseIdx i, S.paid⟩
      | some o => ⟨o.st, S.pending.eraseIdx i ++ o.calls, S.paid ++ o.transfers⟩
  | .resolveFails i => ⟨S.c, S.pending.eraseIdx i, S.paid⟩
  | .nearIn x =>
    if S.c.near + x ≤ E.cap then ⟨{ S.c with near := S.c.near + x }, S.pending, S.paid⟩ else S

/-- States reachable from `new()` (empty map, zero supply, balance covering the base stake). -/
inductive Reach (E : Env) : Sys → Prop
  | init (n : Nat) (h1 : E.base ≤ n) (h2 : n ≤ E.cap) : Reach E ⟨⟨[], 0, n⟩, [], []⟩
  | step {S : Sys} (st : Step) : Reach E S → Reach E (sysStep E S st)

end WNear
