/-
  Model of near-contract-standards 5.29.0 `FungibleToken` (NEP-141 core) and its
  `StorageManagement` (NEP-145) implementation, inside a token contract that exposes them the way
  the official near-sdk-rs example does (examples/fungible-token/ft at tag near-sdk-v5.29.0,
  commit 1aac824): `#[payable]` ft_transfer / ft_transfer_call / storage_deposit /
  storage_withdraw / storage_unregister, `#[private]` ft_resolve_transfer, `&self` views.

  Sources mirrored (near-contract-standards 5.29.0, line by line):
  * fungible_token/core_impl.rs     internal_deposit / internal_withdraw / internal_transfer,
                                    ft_transfer, ft_transfer_call, internal_ft_resolve_transfer,
                                    GAS_FOR_RESOLVE_TRANSFER, MAX_RESULT_LENGTH
  * fungible_token/storage_impl.rs  storage_deposit, storage_withdraw, internal_storage_unregister,
                                    storage_balance_bounds, storage_balance_of
  * fungible_token/events.rs        FtTransfer / FtBurn (NEP-297 `EVENT_JSON` logs), as data
  * near-sdk 5.29.0 code generation: `#[private]` = predecessor == current account (panics
    otherwise), a non-payable `&mut self` method panics on any deposit, `#[init]` panics when the
    state exists, `&self` methods accept deposits; `env::promise_result_checked` returns
    `Failed` / `TooLong` errors, both of which the resolver treats as "nothing used".

  Amounts are natural numbers. u128 arithmetic is exact: `checked_*` panics explicitly and the
  release profile has `overflow-checks = true`, so an overflow fails the call, which changes
  nothing. `NearToken::saturating_*` is saturating. `none` = the call failed.
-/
import ProvedFT.Map

namespace ProvedFT

def U128_MAX : Nat := 340282366920938463463374607431768211455

/-- `GAS_FOR_RESOLVE_TRANSFER` (core_impl.rs): static gas of the settlement callback. Its
    unused-gas weight is 0, so the callback receipt carries exactly this much gas. -/
def GAS_FOR_RESOLVE_TRANSFER : Nat := 5000000000000

/-- `MAX_RESULT_LENGTH` in `internal_ft_resolve_transfer`:
    `"\"+340282366920938463463374607431768211455\"".len()`. -/
def MAX_RESULT_LENGTH : Nat := 42

/-- `NearToken::saturating_add`. -/
def satAdd (a b : Nat) : Nat := min (a + b) U128_MAX

/-- Parameters of a deployment. -/
structure Env where
  /-- The token contract's account. -/
  self : Acct
  /-- `storage_balance_bounds().min` = `account_storage_usage * storage_byte_cost`, where
      `account_storage_usage` is what inserting a 64-character account id costs
      (`measure_account_storage_usage`). -/
  minBal : Nat
  /-- Storage stake of everything except the `accounts` entries (code, contract state record,
      account record, metadata), in yoctoNEAR. -/
  base : Nat
  /-- Storage stake of one `accounts` entry, in yoctoNEAR. -/
  entry : Acct → Nat
  /-- An upper bound on any NEAR balance (the total NEAR supply). -/
  cap : Nat

/-- Assumptions on the parameters. They hold on mainnet: an account id has at most 64
    characters, so an entry never costs more than the measured 64-character entry; the total
    NEAR supply is far below u128::MAX. -/
structure Env.Sane (E : Env) : Prop where
  entry_le : ∀ a, E.entry a ≤ E.minBal
  cap_lt : E.cap + 1 ≤ U128_MAX
  min_lt : E.minBal + 1 ≤ U128_MAX

/-- Contract state: the `accounts` LookupMap, `total_supply`, and the contract's NEAR balance. -/
structure St where
  accts : Accts
  supply : Nat
  near : Nat

/-! ### The promise result the resolver reads -/

def isWs (b : Nat) : Bool := b == 0x20 || b == 0x09 || b == 0x0a || b == 0x0d

def hexVal? (b : Nat) : Option Nat :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b - 0x30)
  else if 0x61 ≤ b ∧ b ≤ 0x66 then some (b - 0x61 + 10)
  else if 0x41 ≤ b ∧ b ≤ 0x46 then some (b - 0x41 + 10)
  else none

/-- Single-character JSON escapes. -/
def esc1 (e : Nat) : Option Nat :=
  if e = 0x22 then some 0x22 else if e = 0x5c then some 0x5c else if e = 0x2f then some 0x2f
  else if e = 0x62 then some 8 else if e = 0x66 then some 12 else if e = 0x6e then some 10
  else if e = 0x72 then some 13 else if e = 0x74 then some 9 else none

/-- A JSON string body after its opening quote: its characters (escapes decoded to code points)
    and the bytes after the closing quote; `none` if it is not valid JSON. Raw bytes ≥ 0x80 are
    kept as they are: they are never digits, and serde_json's UTF-8 / surrogate checks can only
    turn a non-numeric string into an error, which ends the same way (no number). -/
def strBody : List Nat → Option (List Nat × List Nat)
  | [] => none
  | 0x22 :: rest => some ([], rest)
  | 0x5c :: 0x75 :: a :: b :: c :: d :: rest =>
    match hexVal? a, hexVal? b, hexVal? c, hexVal? d with
    | some x, some y, some z, some w =>
      (strBody rest).map fun q => ((((x * 16 + y) * 16 + z) * 16 + w) :: q.1, q.2)
    | _, _, _, _ => none
  | 0x5c :: e :: rest =>
    match esc1 e with
    | some c => (strBody rest).map fun q => (c :: q.1, q.2)
    | none => none
  | b :: rest => if b < 0x20 then none else (strBody rest).map fun q => (b :: q.1, q.2)

def isDigitB (c : Nat) : Bool := 0x30 ≤ c && c ≤ 0x39

def digitsVal (cs : List Nat) : Nat := cs.foldl (fun a c => a * 10 + (c - 0x30)) 0

/-- Rust `str::parse::<u128>`: an optional `+`, then one or more ASCII digits, value ≤ u128::MAX. -/
def parseU128Str (cs : List Nat) : Option Nat :=
  let ds := match cs with
    | 0x2b :: rest => rest
    | _ => cs
  if ds.isEmpty then none
  else if ds.all isDigitB then
    (if digitsVal ds ≤ U128_MAX then some (digitsVal ds) else none)
  else none

/-- `serde_json::from_slice::<U128>(bytes)`: JSON whitespace, one JSON string, JSON whitespace;
    the string's content parsed by `str::parse::<u128>` (near-sdk-core 4.2.3 `U128`). -/
def parseU128Json (bytes : List Nat) : Option Nat :=
  match bytes.dropWhile isWs with
  | 0x22 :: rest =>
    match strBody rest with
    | some (cs, after) => if after.all isWs then parseU128Str cs else none
    | none => none
  | _ => none

/-- The promise result `ft_resolve_transfer` reads with `env::promise_result_checked(0, ..)`:
    the receiver's `ft_on_transfer` failed (panic, out of gas, missing method, …), or it
    returned these bytes. -/
inductive PR where
  | failed
  | ok (bytes : List Nat)

/-! ### Calls -/

inductive Method where
  /-- The token's `#[init]` method called again. -/
  | reinit
  | ft_transfer (receiver : Acct) (amount : Nat) (memo : Option String)
  | ft_transfer_call (receiver : Acct) (amount : Nat) (memo : Option String) (msg : String)
  | ft_resolve_transfer (sender receiver : Acct) (amount : Nat)
  | storage_deposit (account : Option Acct) (registrationOnly : Option Bool)
  | storage_withdraw (amount : Option Nat)
  | storage_unregister (force : Option Bool)
  | ft_total_supply
  | ft_balance_of (account : Acct)
  | storage_balance_bounds
  | storage_balance_of (account : Acct)
  /-- A method the token does not export, or arguments that fail to deserialize. -/
  | bad

/-- One receipt executed on the token contract. -/
structure Rcpt where
  pred : Acct
  deposit : Nat
  m : Method
  results : List PR

/-- NEP-297 events the standard emits, as data. -/
inductive Ev where
  | transfer (oldOwner newOwner : Acct) (amount : Nat) (memo : Option String)
  | burn (owner : Acct) (amount : Nat) (memo : Option String)

/-- A method's return value. -/
inductive Ret where
  | unit
  /-- `ft_transfer_call` returns the promise of its callback. -/
  | promise
  | u128 (n : Nat)
  | bool (b : Bool)
  /-- `StorageBalance { total, available }`. -/
  | storageBalance (total available : Nat)
  | storageBalanceOpt (sb : Option (Nat × Nat))
  /-- `StorageBalanceBounds { min, max }`. -/
  | bounds (min : Nat) (max : Option Nat)

/-- Effects of a successful call. -/
structure Out where
  st : St
  /-- `Promise::new(to).transfer(amount)` actions, in order. -/
  transfers : List (Acct × Nat)
  /-- `ft_on_transfer` + `ft_resolve_transfer` promise pairs: (sender, receiver, amount); the
      callback carries `GAS_FOR_RESOLVE_TRANSFER`. -/
  calls : List (Acct × Acct × Nat)
  events : List Ev
  ret : Ret

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
    `promise_result_checked(0, MAX_RESULT_LENGTH).ok().and_then(parse).unwrap_or(amount).min(amount)`. -/
def unusedOf (amt : Nat) : PR → Nat
  | .failed => amt
  | .ok b =>
    if b.length ≤ MAX_RESULT_LENGTH then
      (match parseU128Json b with
       | some v => min v amt
       | none => amt)
    else amt

/-- The refund `ft_resolve_transfer` moves back from the receiver: `min(receiver balance,
    unused)` when both are positive, else 0. -/
def refundOf (l : Accts) (r : Acct) (amt : Nat) (res : PR) : Nat :=
  if 0 < unusedOf amt res ∧ 0 < bal l r then min (bal l r) (unusedOf amt res) else 0

/-- `internal_ft_resolve_transfer`: (accounts, supply, used amount, events). The receiver is
    debited first; the sender's entry is read afterwards. `amount - refund` cannot underflow
    (refund ≤ unused ≤ amount). -/
def iResolve (l : Accts) (sup : Nat) (s r : Acct) (amt : Nat) (res : PR) :
    Option (Accts × Nat × Nat × List Ev) :=
  if 0 < unusedOf amt res then
    if 0 < bal l r then
      let refund := min (bal l r) (unusedOf amt res)
      let l1 := set l r (bal l r - refund)
      match get l1 s with
      | some sb =>
        -- `sender_balance.checked_add(refund_amount)`, else "Sender balance overflow"
        if sb + refund ≤ U128_MAX then
          some (set l1 s (sb + refund), sup, amt - refund, [.transfer r s refund (some "refund")])
        else none
      | none =>
        -- sender unregistered meanwhile: `total_supply.checked_sub(refund_amount)` (burn)
        if refund ≤ sup then some (l1, sup - refund, amt, [.burn r refund (some "refund")])
        else none
    else some (l, sup, amt, [])
  else some (l, sup, amt, [])

/-- The token code: what a receipt does to the contract state (NEAR accounting is the
    runtime's, in `exec`). -/
def method (E : Env) (s : St) (r : Rcpt) : Option Out :=
  let l := s.accts
  let sup := s.supply
  let p := r.pred
  let d := r.deposit
  match r.m with
  | .reinit => none        -- "The contract has already been initialized"
  | .bad => none
  | .ft_total_supply => some ⟨s, [], [], [], .u128 sup⟩
  | .ft_balance_of a => some ⟨s, [], [], [], .u128 (bal l a)⟩
  | .storage_balance_bounds => some ⟨s, [], [], [], .bounds E.minBal (some E.minBal)⟩
  | .storage_balance_of a =>
    some ⟨s, [], [], [], .storageBalanceOpt ((get l a).map fun _ => (E.minBal, 0))⟩
  | .ft_transfer rc x memo =>
    if d ≠ 1 then none     -- assert_one_yocto
    else match iTransfer l sup p rc x with
      | none => none
      | some (l', sup') => some ⟨⟨l', sup', s.near⟩, [], [], [.transfer p rc x memo], .unit⟩
  | .ft_transfer_call rc x memo _ =>
    if d ≠ 1 then none
    else match iTransfer l sup p rc x with
      | none => none
      | some (l', sup') =>
        some ⟨⟨l', sup', s.near⟩, [], [(p, rc, x)], [.transfer p rc x memo], .promise⟩
  | .ft_resolve_transfer sn rc amt =>
    if p ≠ E.self then none   -- #[private]: "Method ft_resolve_transfer is private"
    else if d ≠ 0 then none   -- not #[payable]: "doesn't accept deposit"
    else match r.results with
      | res :: _ =>
        match iResolve l sup sn rc amt res with
        | none => none
        | some (l', sup', used, evs) => some ⟨⟨l', sup', s.near⟩, [], [], evs, .u128 used⟩
      | [] => none            -- promise_result(0) without results: host error
  | .storage_deposit acc _ =>
    let a := acc.getD p
    match get l a with
    | some _ =>
      -- "The account is already registered, refunding the deposit"
      some ⟨s, (if 0 < d then [(p, d)] else []), [], [], .storageBalance E.minBal 0⟩
    | none =>
      if d < E.minBal then none
      else some ⟨⟨set l a 0, sup, s.near⟩,
        (if 0 < d - E.minBal then [(p, d - E.minBal)] else []), [], [],
        .storageBalance E.minBal 0⟩
  | .storage_withdraw amt =>
    if d ≠ 1 then none
    else match get l p with
      | none => none          -- "The account … is not registered"
      | some _ =>
        match amt with
        | some a => if 0 < a then none else some ⟨s, [], [], [], .storageBalance E.minBal 0⟩
        | none => some ⟨s, [], [], [], .storageBalance E.minBal 0⟩
  | .storage_unregister force =>
    if d ≠ 1 then none
    else match get l p with
      | none => some ⟨s, [], [], [], .bool false⟩   -- logs "not registered", returns false
      | some b =>
        if b = 0 ∨ force = some true then
          -- `self.total_supply -= balance` (overflow-checked)
          if b ≤ sup then
            some ⟨⟨erase l p, sup - b, s.near⟩, [(p, satAdd E.minBal 1)], [], [], .bool true⟩
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

/-- Contract state, the settlement callbacks still in flight, and every NEAR transfer the
    contract has sent. -/
structure Sys where
  c : St
  pending : List (Acct × Acct × Nat)
  paid : List (Acct × Nat)

/-- One event. Everything a receiver's `ft_on_transfer` can do is covered: its calls back into
    the token are `call` steps (with the receiver or anyone else as predecessor, in any order),
    and what it returns (any bytes, a panic, running out of gas) is the `res` of `resolve`. -/
inductive Step where
  /-- A receipt from `pred`: a signed transaction, a call from another contract, or another
      contract's `promise_then` callback carrying promise results `rs` of its choice. -/
  | call (pred : Acct) (deposit : Nat) (m : Method) (rs : List PR)
  /-- The `i`-th settlement callback in flight runs with promise result `res`. -/
  | resolve (i : Nat) (res : PR)
  /-- The `i`-th settlement callback fails before it runs (e.g. out of gas): dropped. -/
  | resolveFails (i : Nat)
  /-- NEAR arrives: a plain transfer, or the refund of a failed outgoing transfer. -/
  | nearIn (x : Nat)

/-- Promise results a `call` receipt carries. A receipt whose predecessor is the token itself
    is either the token's own settlement callback (that is `Step.resolve`) or a transaction
    signed with the token account's key (if it keeps one), and transactions carry none. -/
def resultsFor (E : Env) (p : Acct) (rs : List PR) : List PR := if p = E.self then [] else rs

def sysStep (E : Env) (S : Sys) : Step → Sys
  | .call p d m rs =>
    match exec E S.c ⟨p, d, m, resultsFor E p rs⟩ with
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

/-- Structural facts of a contract state: no repeated keys, `total_supply` = sum of balances,
    supply fits u128. -/
structure Pre (s : St) : Prop where
  nodup : Nodup s.accts
  cons : s.supply = total s.accts
  bound : s.supply ≤ U128_MAX

/-- What the token's own `#[init]` method must leave (checked by the certification kit on the
    deployed wasm): the structural facts, and NEAR covering the base storage stake plus one
    storage deposit per account it registered. -/
def InitOK (E : Env) (s : St) : Prop :=
  Pre s ∧ s.accts.length * E.minBal + E.base ≤ s.near ∧ s.near ≤ E.cap

/-- States reachable from an initial state of the token. -/
inductive Reach (E : Env) : Sys → Prop
  | init (s : St) (h : InitOK E s) : Reach E ⟨s, [], []⟩
  | step {S : Sys} (st : Step) : Reach E S → Reach E (sysStep E S st)

end ProvedFT
