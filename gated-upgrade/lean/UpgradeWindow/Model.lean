/-
  UpgradeWindow.Model — the `Upgradable` plugin of near-plugins v0.5.1
  (commit 312e016e0574d5756f6eba37acc82d9a237b2e3e), as a state machine.

  Source: `near-plugins-derive/src/upgradable.rs` (the code the `#[derive(Upgradable)]` macro
  generates). Line numbers in the comments refer to that file.

  What is modelled
  * the five storage slots under the `__up__` prefix (l. 97-103);
  * the five protected methods, statement by statement, with their panics (l. 167-273);
  * u64 arithmetic: `saturating_add` in `up_stage_code` (l. 177), plain `+` in
    `up_stage_update_staging_duration` (l. 250), which panics on overflow when the contract is
    built with `overflow-checks = true` (the near-sdk template, and the example contract). A
    build without overflow checks wraps instead: `Up.stageDurUnchecked`, `W3_unchecked_shortcut`;
  * the promise `up_deploy_code` returns (l. 221-233): a batch on the contract's own account
    `[DeployContract(code), FunctionCall(args)?, FunctionCall(up_verify_state)]`, executed by a
    later receipt, all-or-nothing.

  What is a parameter
  * `Code` — the bytes of a contract; `H : Code → String` — bs58(sha256(code)) (l. 145-149, 210);
  * `allowed : Bool` on every call — the outcome of the `#[access_control_any(roles(..))]` check
    for the caller (the first statement of each protected method). The theorems hold for every
    value of it: they do not depend on who holds which role.
-/
namespace UpgradeWindow

/-- `u64::MAX`. Block timestamps and durations are `u64` nanoseconds. -/
def U64_MAX : Nat := 18446744073709551615

/-- `u64::saturating_add`. -/
def satAdd (a b : Nat) : Nat := min (a + b) U64_MAX

/-- `FunctionCallArgs` (near-plugins/src/upgradable.rs l. 212-221): the function call that
    `up_deploy_code` can attach to the deployment. Chosen by the deployer at deploy time. -/
structure FnCall where
  name : String
  args : List Nat
  amount : Nat
  gas : Nat
  deriving Repr, DecidableEq

/-- The plugin's storage: one optional value per `__UpgradableStorageKey` (l. 97-103). -/
structure Up (Code : Type) where
  /-- `Code`: the staged code. -/
  code : Option Code := none
  /-- `StagingTimestamp`: earliest block timestamp at which the staged code may be deployed. -/
  stagingTs : Option Nat := none
  /-- `StagingDuration`. -/
  dur : Option Nat := none
  /-- `NewStagingDuration`: the staged update of the duration. -/
  newDur : Option Nat := none
  /-- `NewStagingDurationTimestamp`: earliest block timestamp at which it may be applied. -/
  newDurTs : Option Nat := none

/-- The protected methods. -/
inductive Call (Code : Type) where
  /-- `up_stage_code`, the input bytes being the code; `none` = empty input. -/
  | stageCode (code : Option Code)
  /-- `up_deploy_code(hash, function_call_args)`. -/
  | deployCode (hash : String) (fc : Option FnCall)
  /-- `up_init_staging_duration(staging_duration)`. -/
  | initDur (d : Nat)
  /-- `up_stage_update_staging_duration(staging_duration)`. -/
  | stageDur (d : Nat)
  /-- `up_apply_update_staging_duration()`. -/
  | applyDur

/-- The panics of the protected methods. -/
inductive Err where
  /-- "Insufficient permissions for method … restricted by access control." -/
  | noPermission
  /-- "Upgradable: staging timestamp isn't set" (l. 197) -/
  | tsNotSet
  /-- "Upgradable: Deploy code too early: staging ends on {ts}" (l. 199-207) -/
  | tooEarly (ts : Nat)
  /-- "Upgradable: No staged code" (l. 209) -/
  | noCode
  /-- "Upgradable: Cannot deploy due to wrong hash: expected hash: {expected}" (l. 211-219) -/
  | wrongHash (expected : String)
  /-- "Upgradable: staging duration was already initialized" (l. 240) -/
  | alreadyInit
  /-- "Upgradable: staging duration isn't initialized" (l. 247) -/
  | notInit
  /-- "attempt to add with overflow" (l. 250, `overflow-checks = true`) -/
  | overflow
  /-- "Upgradable: No staged update" (l. 257) -/
  | noStagedUpdate
  /-- "Upgradable: Update duration too early: staging ends on {ts}" (l. 259-267) -/
  | durTooEarly (ts : Nat)
  /-- "Upgradable: No staged duration update" (l. 270) -/
  | noStagedDur
  deriving Repr, DecidableEq

/-- The promise a successful `up_deploy_code` returns: the code it read from storage, the
    attached function call, and the block timestamp of the call that created it. -/
structure Deploy (Code : Type) where
  code : Code
  fc : Option FnCall
  calledAt : Nat

variable {Code : Type}

/-- `up_stage_code` (l. 168-183). Empty input removes the staged code and its timestamp;
    otherwise the code is stored (replacing any staged code) with timestamp
    `block_timestamp.saturating_add(staging_duration.unwrap_or(0))`. -/
def Up.stageCode (now : Nat) (s : Up Code) : Option Code → Up Code
  | none => { s with code := none, stagingTs := none }
  | some c => { s with code := some c, stagingTs := some (satAdd now (s.dur.getD 0)) }

/-- `up_deploy_code` (l. 195-219), up to the creation of the promise: the code to deploy. -/
def Up.deployCode (H : Code → String) (now : Nat) (s : Up Code) (hash : String) : Except Err Code :=
  match s.stagingTs with
  | none => .error .tsNotSet
  | some ts =>
    if now < ts then .error (.tooEarly ts)
    else match s.code with
      | none => .error .noCode
      | some c => if hash = H c then .ok c else .error (.wrongHash (H c))

/-- `up_init_staging_duration` (l. 239-242). -/
def Up.initDur (s : Up Code) (d : Nat) : Except Err (Up Code) :=
  match s.dur with
  | some _ => .error .alreadyInit
  | none => .ok { s with dur := some d }

/-- `up_stage_update_staging_duration` (l. 245-252). -/
def Up.stageDur (now : Nat) (s : Up Code) (d : Nat) : Except Err (Up Code) :=
  match s.dur with
  | none => .error .notInit
  | some cur =>
    if U64_MAX < now + cur then .error .overflow
    else .ok { s with newDur := some d, newDurTs := some (now + cur) }

/-- `up_stage_update_staging_duration` as it behaves when the contract is built WITHOUT overflow
    checks (cargo's default release profile): the `+` of l. 250 wraps modulo 2^64. Not used by
    the model; see `stageDurUnchecked_eq` and `W3_unchecked_shortcut`. -/
def Up.stageDurUnchecked (now : Nat) (s : Up Code) (d : Nat) : Except Err (Up Code) :=
  match s.dur with
  | none => .error .notInit
  | some cur => .ok { s with newDur := some d, newDurTs := some ((now + cur) % (U64_MAX + 1)) }

/-- `up_apply_update_staging_duration` (l. 255-273). The staged update stays in storage. -/
def Up.applyDur (now : Nat) (s : Up Code) : Except Err (Up Code) :=
  match s.newDurTs with
  | none => .error .noStagedUpdate
  | some t =>
    if now < t then .error (.durTooEarly t)
    else match s.newDur with
      | none => .error .noStagedDur
      | some nd => .ok { s with dur := some nd }

/-- One call of a protected method at block timestamp `now`. `allowed` is the outcome of the
    access-control check for the caller. A panic leaves the storage as it was. -/
def Up.call (H : Code → String) (now : Nat) (allowed : Bool) (s : Up Code) (c : Call Code) :
    Except Err (Up Code × Option (Deploy Code)) :=
  if allowed = false then .error .noPermission
  else match c with
    | .stageCode x => .ok (s.stageCode now x, none)
    | .deployCode h fc =>
      match s.deployCode H now h with
      | .error e => .error e
      | .ok code => .ok (s, some ⟨code, fc, now⟩)
    | .initDur d =>
      match s.initDur d with
      | .error e => .error e
      | .ok s' => .ok (s', none)
    | .stageDur d =>
      match s.stageDur now d with
      | .error e => .error e
      | .ok s' => .ok (s', none)
    | .applyDur =>
      match s.applyDur now with
      | .error e => .error e
      | .ok s' => .ok (s', none)

/-- The view `up_staged_code_hash` (l. 189-192). -/
def Up.stagedCodeHash (H : Code → String) (s : Up Code) : Option String := s.code.map H

/-! ### The account: plugin storage, the code that runs, deploy receipts in flight -/

/-- The contract account as far as upgrades are concerned. -/
structure Sys (Code : Type) where
  up : Up Code
  /-- The code deployed on the account. -/
  current : Code
  /-- Deploy batches created by `up_deploy_code` and not executed yet. -/
  inflight : List (Deploy Code) := []

/-- What can happen to the account. -/
inductive Ev (Code : Type) where
  /-- A receipt calling a protected method. -/
  | call (allowed : Bool) (c : Call Code)
  /-- The `i`-th deploy batch in flight executes; `ok`: every action of the batch succeeded
      (a failed function call rolls the deployment back). -/
  | batch (i : Nat) (ok : Bool)
  /-- Anything else: a view, a method of the host contract, a failed receipt. It does not
      write the plugin's storage slots (assumption A2 in the README). -/
  | other

/-- One event at block timestamp `now`. -/
def Sys.step (H : Code → String) (now : Nat) (s : Sys Code) : Ev Code → Sys Code
  | .call a c =>
    match s.up.call H now a c with
    | .error _ => s
    | .ok (u, none) => { s with up := u }
    | .ok (u, some d) => { s with up := u, inflight := s.inflight ++ [d] }
  | .batch i ok =>
    match s.inflight[i]? with
    | none => s
    | some d => { s with inflight := s.inflight.eraseIdx i,
                         current := if ok then d.code else s.current }
  | .other => s

/-- A trace: events with their block timestamps. -/
abbrev Trace (Code : Type) := List (Nat × Ev Code)

/-- Runs a trace. -/
def run (H : Code → String) : Sys Code → Trace Code → Sys Code
  | s, [] => s
  | s, (t, e) :: rest => run H (s.step H t e) rest

/-- Block timestamps never decrease: `Mono t0 tr` — the trace starts at or after `t0`. -/
def Mono : Nat → Trace Code → Prop
  | _, [] => True
  | t, (t', _) :: rest => t ≤ t' ∧ Mono t' rest

/-- The timestamp of the last event (`t0` for the empty trace). -/
def endTime : Nat → Trace Code → Nat
  | t, [] => t
  | _, (t', _) :: rest => endTime t' rest

/-! ### What a watcher computes from the views -/

/-- The earliest block timestamp at which an `up_deploy_code` call can succeed, computed from
    `up_get_delay_status` and the current time (theorem `W3_no_deploy_before`):
    the minimum of
    * `now + staging_duration` — code staged from now on waits the current duration;
    * `staging_timestamp`, if code is staged;
    * `max(now, new_staging_duration_timestamp) + new_staging_duration`, if a duration update is
      staged — it can be applied at its timestamp, and code staged then waits the new duration.
    All sums saturate at `u64::MAX`. With no duration set the first term is `now`. -/
def safeUntil (u : Up Code) (now : Nat) : Nat :=
  let a := satAdd now (u.dur.getD 0)
  let b := match u.stagingTs with
    | some ts => min a ts
    | none => a
  match u.newDur, u.newDurTs with
  | some nd, some ndt => min b (satAdd (max now ndt) nd)
  | _, _ => b

/-- The visible warning: code is staged, or a staged duration update is below the current
    duration. Both are readable from `up_get_delay_status`. -/
def alarm (u : Up Code) : Bool :=
  u.stagingTs.isSome ||
  (match u.newDur, u.newDurTs, u.dur with
   | some nd, some _, some d => decide (nd < d)
   | _, _, _ => false)

end UpgradeWindow
