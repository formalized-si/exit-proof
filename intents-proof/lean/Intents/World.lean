/-
  The two-contract world: the token (the proved model of near-contract-standards 5.29.0
  `FungibleToken`, `ProvedFT`) and the Intents ledger for that token, with every receipt and
  callback in flight between them.

  One `Step` is one receipt executed on one of the two contracts, or one callback that fails
  before it runs. Any account may call anything at any time; the receiver of an
  `ft_transfer_call` sent by the contract is an arbitrary contract (its answer is the `res` of
  `Step.tokResolve`); any callback may be dropped for lack of gas.

  What ties the two contracts together is NEAR's promise semantics, and nothing else:
  * the token's settlement callback for a transfer *to the contract* reads the outcome of the
    contract's own `ft_on_transfer` (`Ann.dep`), and cannot run before it;
  * the contract's `ft_resolve_withdraw` reads the outcome of the token receipt it is chained
    to: of `ft_transfer`, or of `ft_transfer_call`, which is the value the token's
    `ft_resolve_transfer` returned (`Rs.res`).
-/
import Intents.Ledger

namespace Intents
open ProvedFT (Acct Accts get bal set total PR Method Rcpt Out St Env Ret U128_MAX parseU128Json)

/-- What the model remembers about a settlement callback in flight on the token. -/
inductive Ann where
  /-- A transfer between two other accounts. -/
  | other
  /-- A transfer to the contract. `none`: its `ft_on_transfer` has not run yet;
      `some true`: it ran, credited the ledger and returned `"0"`; `some false`: it failed. -/
  | dep (st : Option Bool)
  /-- An `ft_transfer_call` the contract sent for a withdrawal debited from `owner`. -/
  | wd (owner : Acct)
  deriving DecidableEq, Repr

/-- A settlement callback `ft_resolve_transfer(sender, receiver, amount)` in flight on the token. -/
structure Pend where
  sender : Acct
  receiver : Acct
  amount : Nat
  ann : Ann
  deriving Repr

def Pend.raw (e : Pend) : Acct × Acct × Nat := (e.sender, e.receiver, e.amount)

structure World where
  /-- The token contract's state. -/
  c : St
  /-- The token's settlement callbacks in flight. -/
  pend : List Pend := []
  /-- NEAR transfers the token has sent (so that the token part is exactly `ProvedFT.Sys`). -/
  paid : List (Acct × Nat) := []
  /-- The Intents ledger for this token. -/
  L : Ledger := {}
  /-- Withdrawals with a storage deposit, debited, waiting for wNEAR `near_withdraw` and the
      contract's `do_ft_withdraw`. -/
  unwrap : List Wd := []
  /-- Withdrawals debited whose token receipt (`ft_transfer` / `ft_transfer_call`) has not
      executed yet. -/
  outbox : List Wd := []
  /-- `ft_resolve_withdraw` callbacks ready to run. -/
  resolves : List Rs := []

structure Cfg where
  /-- The token deployment; `tok.self` is the token's account. -/
  tok : Env
  /-- The Intents contract's account. -/
  me : Acct

/-- Callbacks started by a call of an account other than the contract. -/
def annThird (me : Acct) (calls : List (Acct × Acct × Nat)) : List Pend :=
  calls.map fun q => ⟨q.1, q.2.1, q.2.2, if q.2.1 = me then .dep none else .other⟩

/-- Callbacks started by the contract's own `ft_transfer_call`. -/
def annWd (owner : Acct) (calls : List (Acct × Acct × Nat)) : List Pend :=
  calls.map fun q => ⟨q.1, q.2.1, q.2.2, .wd owner⟩

/-- What the token's settlement callback reads after the contract's `ft_on_transfer`:
    `PromiseOrValue::Value(U128(0))`, i.e. the bytes `"0"`, or a failure. -/
def depRes : Bool → PR
  | true => .ok [0x22, 0x30, 0x22]
  | false => .failed

/-- A token method's return value as the promise result the contract reads: `()` is the empty
    value, a `U128` its JSON string. (The contract chains only on `ft_transfer`, which returns
    `()`, and on `ft_transfer_call`, whose result is `ft_resolve_transfer`'s `U128`.) -/
def retPR : Ret → PR
  | .u128 n => .ok (encU128 n)
  | _ => .ok []

/-- The promise result the settlement callback of `e` reads: the contract's own answer for a
    transfer to the contract (not available before `ft_on_transfer` ran), anything for a
    transfer to another receiver. -/
def resOf (e : Pend) (res : PR) : Option PR :=
  match e.ann with
  | .dep none => none
  | .dep (some cr) => some (depRes cr)
  | _ => some res

/-- When the settlement of the contract's own `ft_transfer_call` is over, its
    `ft_resolve_withdraw` becomes ready with the result `res`. -/
def wdDone (e : Pend) (res : PR) (left : Nat) : List Rs :=
  match e.ann with
  | .wd owner => [⟨owner, e.amount, true, res, left⟩]
  | _ => []

/-- The token call of a withdrawal (`do_ft_withdraw`, withdraw.rs:118-151). -/
def xferMethod (w : Wd) : Method :=
  match w.msg with
  | none => .ft_transfer w.receiver w.amount w.memo
  | some m => .ft_transfer_call w.receiver w.amount w.memo m

/-- The receipt `do_ft_withdraw` sends to the token: `ft_transfer` / `ft_transfer_call` with
    1 yoctoNEAR, preceded in the same receipt by `storage_deposit(receiver)` when a storage
    deposit was requested. A receipt is atomic: if either action fails, nothing changes. -/
def xferBatch (ex : St → Rcpt → Option Out) (me : Acct) (c : St) (w : Wd) : Option Out :=
  match w.sd with
  | none => ex c ⟨me, 1, xferMethod w, []⟩
  | some d =>
    match ex c ⟨me, d, .storage_deposit (some w.receiver) none, []⟩ with
    | none => none
    | some o1 =>
      match ex o1.st ⟨me, 1, xferMethod w, []⟩ with
      | none => none
      | some o2 =>
        some ⟨o2.st, o1.transfers ++ o2.transfers, o1.calls ++ o2.calls, o1.events ++ o2.events,
          o2.ret⟩

inductive Step where
  /-- A receipt on the token from any account other than the contract: any method, any
      deposit, any promise results. -/
  | tokCall (p : Acct) (d : Nat) (m : Method) (rs : List PR)
  /-- The token's `i`-th settlement callback runs. `res` is what an arbitrary receiver
      answered; for a transfer to the contract the contract's own answer is used instead. -/
  | tokResolve (i : Nat) (res : PR)
  /-- The token's `i`-th settlement callback fails before it runs (out of gas). -/
  | tokResolveFails (i : Nat)
  /-- NEAR arrives at the token. -/
  | tokNearIn (x : Nat)
  /-- The contract's `ft_on_transfer` for the token's `i`-th callback in flight (a transfer to
      the contract). `recv` is the account named by `msg` (the sender when `msg` is empty);
      `ok = false`: the receipt fails for a reason outside the model (unparsable `msg`, failing
      intents with `refund_if_fails`, out of gas). -/
  | onTransfer (i : Nat) (recv : Acct) (ok : Bool)
  /-- A withdrawal starts: `ft_withdraw`, an `FtWithdraw` intent, or `ft_force_withdraw`. -/
  | ftWithdraw (via : Via) (w : Wd)
  /-- `do_ft_withdraw` for the `j`-th withdrawal with a storage deposit; `ok`: the wNEAR
      `near_withdraw` before it succeeded and the callback had enough gas. -/
  | doFtWithdraw (j : Nat) (ok : Bool)
  /-- The token receipt of the `j`-th withdrawal executes on the token. -/
  | tokXfer (j : Nat)
  /-- The token receipt of the `j`-th withdrawal fails before any effect (out of gas). -/
  | tokXferFails (j : Nat)
  /-- `storage_deposit(acc)` sent by the contract to the token (a `StorageDeposit` intent,
      `do_storage_deposit`). -/
  | meStorageDeposit (acc : Acct) (d : Nat)
  /-- The `k`-th ready `ft_resolve_withdraw` runs. -/
  | resolveWd (k : Nat)
  /-- The `k`-th ready `ft_resolve_withdraw` fails before it runs (out of gas, log too long). -/
  | resolveWdFails (k : Nat)
  /-- An internal operation: `amt` moves from `src` to `dst` inside the ledger. -/
  | move (auth : MoveAuth) (src dst : Acct) (amt : Nat)
  /-- A change of the switches. -/
  | admin (a : Admin)

/-- One step of the world. `ex` is the token: `ProvedFT.exec K.tok` for the standard token. -/
def step (K : Cfg) (ex : St → Rcpt → Option Out) (S : World) : Step → World
  | .tokCall p d m rs =>
    if p = K.me then S
    else
      match ex S.c ⟨p, d, m, ProvedFT.resultsFor K.tok p rs⟩ with
      | none => S
      | some o =>
        { S with c := o.st, pend := S.pend ++ annThird K.me o.calls, paid := S.paid ++ o.transfers }
  | .tokResolve i res =>
    match S.pend[i]? with
    | none => S
    | some e =>
      match resOf e res with
      | none => S
      | some r =>
        match ex S.c ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [r]⟩ with
        | none =>
          { S with pend := S.pend.eraseIdx i, resolves := S.resolves ++ wdDone e .failed e.amount }
        | some o =>
          { S with
            c := o.st
            pend := S.pend.eraseIdx i ++ annThird K.me o.calls
            paid := S.paid ++ o.transfers
            resolves := S.resolves ++
              wdDone e (retPR o.ret) (e.amount - (bal o.st.accts K.me - bal S.c.accts K.me)) }
  | .tokResolveFails i =>
    match S.pend[i]? with
    | none => S
    | some e =>
      match resOf e .failed with
      | none => S
      | some _ =>
        { S with pend := S.pend.eraseIdx i, resolves := S.resolves ++ wdDone e .failed e.amount }
  | .tokNearIn x =>
    if S.c.near + x ≤ K.tok.cap then { S with c := { S.c with near := S.c.near + x } } else S
  | .onTransfer i recv ok =>
    match S.pend[i]? with
    | none => S
    | some e =>
      if e.receiver = K.me ∧ e.ann = .dep none then
        match (if ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false then
            credit S.L recv e.amount else none) with
        | some L' => { S with L := L', pend := S.pend.set i { e with ann := .dep (some true) } }
        | none => { S with pend := S.pend.set i { e with ann := .dep (some false) } }
      else S
  | .ftWithdraw via w =>
    match startWithdraw S.L via w with
    | none => S
    | some L' =>
      if w.sd.isSome then { S with L := L', unwrap := S.unwrap ++ [w] }
      else { S with L := L', outbox := S.outbox ++ [w] }
  | .doFtWithdraw j ok =>
    match S.unwrap[j]? with
    | none => S
    | some w =>
      if ok then { S with unwrap := S.unwrap.eraseIdx j, outbox := S.outbox ++ [w] }
      else
        { S with
          unwrap := S.unwrap.eraseIdx j
          resolves := S.resolves ++ [⟨w.owner, w.amount, w.msg.isSome, .failed, 0⟩] }
  | .tokXfer j =>
    match S.outbox[j]? with
    | none => S
    | some w =>
      match xferBatch ex K.me S.c w with
      | none =>
        { S with
          outbox := S.outbox.eraseIdx j
          resolves := S.resolves ++ [⟨w.owner, w.amount, w.msg.isSome, .failed, 0⟩] }
      | some o =>
        { S with
          c := o.st
          outbox := S.outbox.eraseIdx j
          paid := S.paid ++ o.transfers
          pend := S.pend ++ annWd w.owner o.calls
          resolves := S.resolves ++
            (if w.msg.isSome then []
             else [⟨w.owner, w.amount, false, retPR o.ret,
                    bal S.c.accts K.me - bal o.st.accts K.me⟩]) }
  | .tokXferFails j =>
    match S.outbox[j]? with
    | none => S
    | some w =>
      { S with
        outbox := S.outbox.eraseIdx j
        resolves := S.resolves ++ [⟨w.owner, w.amount, w.msg.isSome, .failed, 0⟩] }
  | .meStorageDeposit acc d =>
    match ex S.c ⟨K.me, d, .storage_deposit (some acc) none, []⟩ with
    | none => S
    | some o =>
      { S with c := o.st, pend := S.pend ++ annThird K.me o.calls, paid := S.paid ++ o.transfers }
  | .resolveWd k =>
    match S.resolves[k]? with
    | none => S
    | some r =>
      match resolveWithdraw S.L r with
      | none => { S with resolves := S.resolves.eraseIdx k }
      | some L' => { S with L := L', resolves := S.resolves.eraseIdx k }
  | .resolveWdFails k => { S with resolves := S.resolves.eraseIdx k }
  | .move auth src dst amt =>
    match moveBal S.L auth src dst amt with
    | none => S
    | some L' => { S with L := L' }
  | .admin a => { S with L := { S.L with ctl := adminStep S.L.ctl a } }

/-- The standard token. -/
abbrev stdStep (K : Cfg) (S : World) (st : Step) : World := step K (ProvedFT.exec K.tok) S st

/-- The start: a token in an initial state of the proved model, an empty ledger, nothing in
    flight. -/
structure Init (K : Cfg) (S : World) : Prop where
  tok : ProvedFT.InitOK K.tok S.c
  pend : S.pend = []
  paid : S.paid = []
  bals : S.L.bals = []
  supply : S.L.supply = 0
  unwrap : S.unwrap = []
  outbox : S.outbox = []
  resolves : S.resolves = []

/-- States reachable with the standard token. -/
inductive Reach (K : Cfg) : World → Prop
  | init (S : World) (h : Init K S) : Reach K S
  | step {S : World} (st : Step) : Reach K S → Reach K (stdStep K S st)

/-- Run a list of steps. -/
def run (K : Cfg) (ex : St → Rcpt → Option Out) (S : World) (l : List Step) : World :=
  l.foldl (step K ex) S

theorem reach_run {K : Cfg} {S : World} (h : Reach K S) (l : List Step) :
    Reach K (run K (ProvedFT.exec K.tok) S l) := by
  induction l generalizing S with
  | nil => exact h
  | cons st t ih => exact ih (Reach.step st h)

/-! ### What is in flight -/

/-- A transfer to the contract that the token may still take back: its `ft_on_transfer` has not
    credited it. -/
def depW (e : Pend) : Nat :=
  match e.ann with
  | .dep (some true) => 0
  | .dep _ => e.amount
  | _ => 0

/-- Tokens the contract holds against obligations that are not ledger balances yet (or any
    more): debited withdrawals whose tokens have not left, and incoming transfers that are not
    credited. -/
def owed (S : World) : Nat :=
  sumBy Wd.amount S.unwrap + sumBy Wd.amount S.outbox + sumBy Rs.unsettled S.resolves +
    sumBy depW S.pend

end Intents
