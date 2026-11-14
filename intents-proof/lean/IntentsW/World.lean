/-
  The two-contract world with wNEAR as the token: the proved model of the wNEAR contract
  (`WNear`: near-contract-standards 3.1.0 `FungibleToken` plus `near_deposit` /
  `near_withdraw`) and the Intents ledger for the token id `nep141:<wNEAR>`, with every receipt
  and callback in flight between them.

  The contract side is the one of `Intents/Ledger.lean`, unchanged: `credit`, `debit`,
  `startWithdraw`, `Rs.used`, `resolveWithdraw`, `moveBal`, `adminStep`. The token side is
  `WNear.exec`, unchanged. This file only composes them.

  What is new compared with `Intents/World.lean` (a token that is exactly the 5.29.0 standard):
  * the contract calls `near_withdraw` on the token itself. Every such call follows a debit of
    the same amount from a ledger balance of this token id (`Job`); the `do_*` callback chained
    to it sends the unwrapped NEAR on (`Step.doJob`);
  * an `FtWithdraw` intent with `storage_deposit` debits this ledger twice (the amount and the
    storage deposit), `contract/tokens/nep141/withdraw.rs:59-73`;
  * NEAR bookkeeping of the unwrap paths (`uDebited` … `nFwd`), written by the steps and read
    by no guard.

  One `Step` is one receipt executed on one of the two contracts, or one receipt that fails
  before it runs. Any account may call anything at any time.
-/
import WNear.Theorems
import Intents.Theorems

namespace IntentsW
open ProvedFT (Acct Accts bal set total U128_MAX parseU128Json)
open Intents

/-- What the `do_*` callback does with the unwrapped NEAR when `near_withdraw` succeeded. -/
inductive Fwd where
  /-- `NativeWithdraw` → `do_native_withdraw` (`nep141/native.rs:11-19`): a NEAR transfer to
      `receiver`. -/
  | native (receiver : Acct)
  /-- `StorageDeposit` → `do_storage_deposit` (`nep141/storage_deposit.rs:13-26`):
      `contract.storage_deposit(account)` with the NEAR attached. -/
  | storage (contract account : Acct)
  /-- `AuthCall` with `attached_deposit` → `do_auth_call` (`intents/auth_call.rs:17-38`):
      `contract.on_auth(signer, msg)` with the NEAR attached. -/
  | auth (contract : Acct)
  /-- `FtWithdraw` of another token, `NftWithdraw` or `MtWithdraw` with `storage_deposit` →
      `do_ft_withdraw` / `do_nft_withdraw` / `do_mt_withdraw`: `token.storage_deposit(receiver)`
      with the NEAR attached and the transfer, in one receipt. -/
  | other (token receiver : Acct)
  /-- `FtWithdraw` of wNEAR itself with `storage_deposit` → `do_ft_withdraw`
      (`nep141/withdraw.rs:117-151`): wNEAR `storage_deposit(w.receiver)` with the NEAR attached
      and `ft_transfer` / `ft_transfer_call` of `w.amount` in one receipt, then
      `ft_resolve_withdraw`. -/
  | ftw (w : Wd)
  deriving Repr, DecidableEq

def Fwd.isWd : Fwd → Bool
  | .ftw _ => true
  | _ => false

/-- The wNEAR of the withdrawal itself that a job still has to send (0 unless `ftw`). -/
def Fwd.wdAmount : Fwd → Nat
  | .ftw w => w.amount
  | _ => 0

/-- After the callback ran on a successful unwrap: the token receipt of the withdrawal. -/
def Fwd.sent : Fwd → List Wd
  | .ftw w => [w]
  | _ => []

/-- After the callback failed: the `ft_resolve_withdraw` chained to `do_ft_withdraw` reads a
    failure. The other callbacks are detached; nothing follows them. -/
def Fwd.failedRs : Fwd → List Rs
  | .ftw w => [⟨w.owner, w.amount, w.msg.isSome, .failed, 0⟩]
  | _ => []

/-- An unwrap in flight: `amount` was debited from `owner`'s ledger balance of this token id
    and the contract sent `near_withdraw(amount)` with 1 yoctoNEAR to wNEAR
    (`NEAR_WITHDRAW_GAS` = 10 Tgas, `crates/near/wnear/src/lib.rs:7`). -/
structure Job where
  owner : Acct
  amount : Nat
  fwd : Fwd
  deriving Repr, DecidableEq

/-- A `do_*` callback ready to run. `ok`: the promise result it reads is a success with an
    empty value, i.e. `near_withdraw` succeeded and the NEAR transfer it returned has arrived
    (`promise_result_checked_void`, `crates/near/utils/src/promise.rs:67-72`). -/
structure Ready where
  job : Job
  ok : Bool
  deriving Repr, DecidableEq

/-- wNEAR a job in flight still stands for: the amount to burn and, for a withdrawal of wNEAR
    itself, the amount to send. -/
def Job.owedTok (u : Job) : Nat := u.amount + u.fwd.wdAmount

def Ready.owedTok (r : Ready) : Nat := r.job.fwd.wdAmount

/-- NEAR the callback will send on if it runs. -/
def Ready.live (r : Ready) : Nat := if r.ok then r.job.amount else 0

structure World where
  /-- The wNEAR contract's state. -/
  c : WNear.St
  /-- wNEAR's settlement callbacks in flight. -/
  pend : List Pend := []
  /-- NEAR transfers wNEAR has sent (so that the token part is exactly `WNear.Sys`). -/
  paid : List (Acct × Nat) := []
  /-- The Intents ledger for the token id `nep141:<wNEAR>`. -/
  L : Ledger := {}
  /-- Unwraps debited whose `near_withdraw` receipt has not executed yet. -/
  jobs : List Job := []
  /-- `do_*` callbacks ready to run. -/
  ready : List Ready := []
  /-- Withdrawals of wNEAR debited whose token receipt (`ft_transfer` / `ft_transfer_call`)
      has not executed yet. -/
  outbox : List Wd := []
  /-- `ft_resolve_withdraw` callbacks ready to run. -/
  resolves : List Rs := []
  /-- Bookkeeping: wNEAR debited from ledger balances for unwrapping. -/
  uDebited : Nat := 0
  /-- Bookkeeping: wNEAR the contract's `near_withdraw` calls burned, measured on the token's
      state (the contract's balance before minus after). -/
  uBurned : Nat := 0
  /-- Bookkeeping: wNEAR debited for an unwrap whose `near_withdraw` receipt failed. -/
  uKept : Nat := 0
  /-- Bookkeeping: NEAR wNEAR sent to the contract in those `near_withdraw` receipts. -/
  nGot : Nat := 0
  /-- Bookkeeping: NEAR the `do_*` callbacks sent on. -/
  nFwd : Nat := 0

structure Cfg where
  /-- The wNEAR deployment; `tok.self` is the wNEAR account. -/
  tok : WNear.Env
  /-- The Intents contract's account. -/
  me : Acct

/-- What wNEAR's `ft_resolve_transfer` gets from a promise result given as bytes:
    `env::promise_result(0)`, then `serde_json::from_slice::<U128>` (`WNear.PR.ok` carries the
    parsed value). -/
def prW : ProvedFT.PR → WNear.PR
  | .failed => .failed
  | .ok b => .ok (parseU128Json b)

/-- What wNEAR's settlement callback reads after the contract's `ft_on_transfer`: the bytes
    `"0"`, or a failure. -/
def depResW (b : Bool) : WNear.PR := prW (depRes b)

/-- A wNEAR method's return value as the promise result the contract reads: `ft_transfer`
    returns nothing (the empty value); the result of `ft_transfer_call` is the `U128` its
    `ft_resolve_transfer` returned, as a JSON string. -/
def retPRW : Option Nat → ProvedFT.PR
  | some n => .ok (encU128 n)
  | none => .ok []

/-- The promise result the settlement callback of `e` reads: the contract's own answer for a
    transfer to the contract (not available before `ft_on_transfer` ran), anything for a
    transfer to another receiver. -/
def resOfW (e : Pend) (res : WNear.PR) : Option WNear.PR :=
  match e.ann with
  | .dep none => none
  | .dep (some cr) => some (depResW cr)
  | _ => some res

/-- The token call of a withdrawal (`do_ft_withdraw`, withdraw.rs:117-151). -/
def xferMethodW (w : Wd) : WNear.Method :=
  match w.msg with
  | none => .ft_transfer w.receiver w.amount
  | some _ => .ft_transfer_call w.receiver w.amount

/-- The receipt `do_ft_withdraw` sends to wNEAR: `ft_transfer` / `ft_transfer_call` with
    1 yoctoNEAR, preceded in the same receipt by `storage_deposit(receiver)` when a storage
    deposit was requested. A receipt is atomic: if either action fails, nothing changes. -/
def xferBatchW (E : WNear.Env) (me : Acct) (c : WNear.St) (w : Wd) : Option WNear.Out :=
  match w.sd with
  | none => WNear.exec E c ⟨me, 1, xferMethodW w, []⟩
  | some d =>
    match WNear.exec E c ⟨me, d, .storage_deposit (some w.receiver), []⟩ with
    | none => none
    | some o1 =>
      match WNear.exec E o1.st ⟨me, 1, xferMethodW w, []⟩ with
      | none => none
      | some o2 => some ⟨o2.st, o1.transfers ++ o2.transfers, o1.calls ++ o2.calls, o2.ret⟩

/-- `internal_ft_withdraw` for the token wNEAR, the ledger part (withdraw.rs:53-73): the guards
    of the entry point, then `withdraw` of the amount and, for a storage deposit, of that amount
    too — the same token id twice in one call of `Contract::withdraw`. -/
def startWithdrawW (L : Ledger) (via : Via) (w : Wd) : Option Ledger :=
  match startWithdraw L via w with
  | none => none
  | some L1 =>
    match w.sd with
    | none => some L1
    | some d => if d ≤ U128_MAX then debit L1 w.owner d via.forced else none

/-- The debit of `NativeWithdraw`, `StorageDeposit`, `AuthCall` and of the `storage_deposit` of
    a withdrawal of another token id (`contract/intents/state.rs:212-339`): they exist only as
    intents (pause key `intents`), `Contract::withdraw` is not forced, the amount is a
    `NearToken` (`u128`). -/
def startUnwrap (L : Ledger) (owner : Acct) (x : Nat) : Option Ledger :=
  if L.ctl.isPaused "intents" = false ∧ x ≤ U128_MAX then debit L owner x false else none

inductive Step where
  /-- A receipt on wNEAR from any account other than the contract and wNEAR itself: any
      method, any deposit, any promise results. -/
  | tokCall (p : Acct) (d : Nat) (m : WNear.Method) (rs : List WNear.PR)
  /-- wNEAR's `i`-th settlement callback runs. `res` is what an arbitrary receiver answered;
      for a transfer to the contract the contract's own answer is used instead. -/
  | tokResolve (i : Nat) (res : WNear.PR)
  /-- wNEAR's `i`-th settlement callback fails before it runs (out of gas). -/
  | tokResolveFails (i : Nat)
  /-- NEAR arrives at wNEAR (a plain transfer, also one sent by the contract). -/
  | tokNearIn (x : Nat)
  /-- The contract's `ft_on_transfer` for wNEAR's `i`-th callback in flight (a transfer to the
      contract). `ok = false`: the receipt fails for a reason outside the model. -/
  | onTransfer (i : Nat) (recv : Acct) (ok : Bool)
  /-- A withdrawal of wNEAR starts: `ft_withdraw`, an `FtWithdraw` intent, `ft_force_withdraw`. -/
  | ftWithdraw (via : Via) (w : Wd)
  /-- An intent that unwraps starts: the debit, and `near_withdraw(x)` sent to wNEAR. -/
  | unwrap (owner : Acct) (x : Nat) (f : Fwd)
  /-- The `near_withdraw` receipt of the `j`-th job executes on wNEAR. -/
  | nearWithdraw (j : Nat)
  /-- The `near_withdraw` receipt of the `j`-th job fails before any effect (out of gas). -/
  | nearWithdrawFails (j : Nat)
  /-- The `do_*` callback of the `k`-th ready job; `ok = false`: it fails before it runs. -/
  | doJob (k : Nat) (ok : Bool)
  /-- The token receipt of the `j`-th withdrawal executes on wNEAR. -/
  | tokXfer (j : Nat)
  /-- The token receipt of the `j`-th withdrawal fails before any effect (out of gas). -/
  | tokXferFails (j : Nat)
  /-- `storage_deposit(acc)` sent by the contract to wNEAR (a `StorageDeposit` intent whose
      `contract_id` is wNEAR). -/
  | meStorageDeposit (acc : Acct) (d : Nat)
  /-- The `k`-th ready `ft_resolve_withdraw` runs. -/
  | resolveWd (k : Nat)
  /-- The `k`-th ready `ft_resolve_withdraw` fails before it runs. -/
  | resolveWdFails (k : Nat)
  /-- An internal operation: `amt` moves from `src` to `dst` inside the ledger. -/
  | move (auth : MoveAuth) (src dst : Acct) (amt : Nat)
  /-- A change of the switches. -/
  | admin (a : Admin)

/-- One step of the world. -/
def step (K : Cfg) (S : World) : Step → World
  | .tokCall p d m rs =>
    if p = K.me ∨ p = K.tok.self then S
    else
      match WNear.exec K.tok S.c ⟨p, d, m, rs⟩ with
      | none => S
      | some o =>
        { S with c := o.st, pend := S.pend ++ annThird K.me o.calls, paid := S.paid ++ o.transfers }
  | .tokResolve i res =>
    match S.pend[i]? with
    | none => S
    | some e =>
      match resOfW e res with
      | none => S
      | some r =>
        match WNear.exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [r]⟩ with
        | none =>
          { S with pend := S.pend.eraseIdx i, resolves := S.resolves ++ wdDone e .failed e.amount }
        | some o =>
          { S with
            c := o.st
            pend := S.pend.eraseIdx i ++ annThird K.me o.calls
            paid := S.paid ++ o.transfers
            resolves := S.resolves ++
              wdDone e (retPRW o.ret)
                (e.amount - (WNear.bal o.st.accts K.me - WNear.bal S.c.accts K.me)) }
  | .tokResolveFails i =>
    match S.pend[i]? with
    | none => S
    | some e =>
      match resOfW e .failed with
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
    match startWithdrawW S.L via w with
    | none => S
    | some L' =>
      match w.sd with
      | some d =>
        { S with L := L', jobs := S.jobs ++ [⟨w.owner, d, .ftw w⟩], uDebited := S.uDebited + d }
      | none => { S with L := L', outbox := S.outbox ++ [w] }
  | .unwrap owner x f =>
    if f.isWd then S
    else
      match startUnwrap S.L owner x with
      | none => S
      | some L' =>
        { S with L := L', jobs := S.jobs ++ [⟨owner, x, f⟩], uDebited := S.uDebited + x }
  | .nearWithdraw j =>
    match S.jobs[j]? with
    | none => S
    | some u =>
      match WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ with
      | none =>
        { S with
          jobs := S.jobs.eraseIdx j
          ready := S.ready ++ [⟨u, false⟩]
          uKept := S.uKept + u.amount }
      | some o =>
        { S with
          c := o.st
          pend := S.pend ++ annThird K.me o.calls
          paid := S.paid ++ o.transfers
          jobs := S.jobs.eraseIdx j
          ready := S.ready ++ [⟨u, true⟩]
          uBurned := S.uBurned + (WNear.bal S.c.accts K.me - WNear.bal o.st.accts K.me)
          nGot := S.nGot + WNear.sumT o.transfers }
  | .nearWithdrawFails j =>
    match S.jobs[j]? with
    | none => S
    | some u =>
      { S with
        jobs := S.jobs.eraseIdx j
        ready := S.ready ++ [⟨u, false⟩]
        uKept := S.uKept + u.amount }
  | .doJob k ok =>
    match S.ready[k]? with
    | none => S
    | some r =>
      if r.ok = true ∧ ok = true then
        { S with
          ready := S.ready.eraseIdx k
          outbox := S.outbox ++ r.job.fwd.sent
          nFwd := S.nFwd + r.job.amount }
      else
        { S with ready := S.ready.eraseIdx k, resolves := S.resolves ++ r.job.fwd.failedRs }
  | .tokXfer j =>
    match S.outbox[j]? with
    | none => S
    | some w =>
      match xferBatchW K.tok K.me S.c w with
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
             else [⟨w.owner, w.amount, false, retPRW o.ret,
                    WNear.bal S.c.accts K.me - WNear.bal o.st.accts K.me⟩]) }
  | .tokXferFails j =>
    match S.outbox[j]? with
    | none => S
    | some w =>
      { S with
        outbox := S.outbox.eraseIdx j
        resolves := S.resolves ++ [⟨w.owner, w.amount, w.msg.isSome, .failed, 0⟩] }
  | .meStorageDeposit acc d =>
    match WNear.exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc), []⟩ with
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

/-- The token's side of the world, as a state of the proved wNEAR model. -/
def toSys (S : World) : WNear.Sys := ⟨S.c, S.pend.map Pend.raw, S.paid⟩

/-- The start: wNEAR in any state that satisfies the invariant of its proved model
    (conservation, solvency), with any settlement callbacks in flight that do not involve the
    contract; an empty ledger; nothing of the contract in flight. The contract may already hold
    wNEAR. -/
structure Init (K : Cfg) (S : World) : Prop where
  tok : WNear.Inv K.tok (toSys S)
  pend : ∀ e ∈ S.pend, e.ann = .other ∧ e.sender ≠ K.me ∧ e.receiver ≠ K.me
  bals : S.L.bals = []
  supply : S.L.supply = 0
  jobs : S.jobs = []
  ready : S.ready = []
  outbox : S.outbox = []
  resolves : S.resolves = []
  uDebited : S.uDebited = 0
  uBurned : S.uBurned = 0
  uKept : S.uKept = 0
  nGot : S.nGot = 0
  nFwd : S.nFwd = 0

/-- Reachable states. -/
inductive Reach (K : Cfg) : World → Prop
  | init (S : World) (h : Init K S) : Reach K S
  | step {S : World} (st : Step) : Reach K S → Reach K (step K S st)

/-- Run a list of steps. -/
def run (K : Cfg) (S : World) (l : List Step) : World := l.foldl (step K) S

theorem reach_run {K : Cfg} {S : World} (h : Reach K S) (l : List Step) :
    Reach K (run K S l) := by
  induction l generalizing S with
  | nil => exact h
  | cons st t ih => exact ih (Reach.step st h)

/-! ### What is in flight -/

/-- wNEAR the contract holds against obligations that are not ledger balances yet (or any
    more): unwraps not burned yet, debited withdrawals whose tokens have not left, and incoming
    transfers that are not credited. -/
def owed (S : World) : Nat :=
  sumBy Job.owedTok S.jobs + sumBy Ready.owedTok S.ready + sumBy Wd.amount S.outbox +
    sumBy Rs.unsettled S.resolves + sumBy depW S.pend

end IntentsW
