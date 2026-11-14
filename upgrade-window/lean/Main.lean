/-
  uwmodel: replays the receipts a near-contract-sim trace executed on the example vault through
  the Lean model (`UpgradeWindow.Up.call`, `Sys.step`, the example's ACL and vault) and prints
  the model's verdict on every receipt and its view of the state after every observed block.

  `uwmodel --unchecked` replays through the model of a build without overflow checks
  (`Up.callU`, `Sys.stepU` of `UpgradeWindow/Unchecked.lean`).

  stdin:  one trace per line (written by `uw-gen traces`)
  stdout: one line per trace:
    {"id", "steps": [{"ok","err","ret","eff"}...], "obs": [{...}...]}

  The decode layer below (JSON arguments as near-sdk 5.26.1 deserializes them, the deposit
  check of non-payable methods, `#[private]`, method names) is not part of the proved model; it
  is checked only by conformance on the inputs the harness generates. Contract code is
  identified by a label; the label → bs58(sha256) table comes from the trace header.
-/
import Lean.Data.Json
import UpgradeWindow.Example
import UpgradeWindow.Unchecked

open Lean UpgradeWindow

/-- Label of the code that keeps none of the contract: only `up_verify_state` is exported. -/
def stubLabel : String := "stub"

structure St where
  self : String
  sys : Sys String
  acl : Acl
  vault : Vault
  /-- Receipt ids of the deploy batches in flight, parallel to `sys.inflight`. -/
  rids : List String

/-! ### Decode layer -/

def jstr (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok (.str s) => s
  | _ => ""

def decNat? (s : String) : Option Nat :=
  if s.isEmpty then none else if s.all Char.isDigit then s.toNat? else none

/-- A number the harness wrote as a decimal string or a JSON number. -/
def jnat (j : Json) (k : String) : Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => (decNat? s).getD 0
  | .ok v => (v.getNat?.toOption).getD 0
  | _ => 0

/-- `u64` argument: a non-negative JSON integer within range. -/
def u64Field (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.num n) =>
    if n.exponent == 0 && n.mantissa ≥ 0 && n.mantissa.toNat ≤ U64_MAX then some n.mantissa.toNat
    else none
  | _ => none

/-- `U128` / `NearToken`: a JSON string holding a decimal u128. -/
def u128StrField (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => (decNat? s).bind fun n => if n ≤ U128_MAX then some n else none
  | _ => none

/-- `Gas`: a JSON string holding a decimal u64. -/
def gasField (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => (decNat? s).bind fun n => if n ≤ U64_MAX then some n else none
  | _ => none

def bytesField (j : Json) (k : String) : Option (List Nat) :=
  match j.getObjVal? k with
  | .ok (.arr xs) => xs.toList.mapM fun x =>
      match x.getNat? with
      | .ok n => if n ≤ 255 then some n else none
      | .error _ => none
  | _ => none

def roleField (j : Json) : Option Role :=
  match j.getObjVal? "role" with
  | .ok (.str s) => Role.ofName? s
  | _ => none

/-- near-account-id `validate`: 2..64 bytes of `a-z 0-9 - _ .`, separators not at the ends and
    not adjacent. -/
def validAccountId (s : String) : Bool :=
  let rec go : List Char → Bool → Bool
    | [], last => !last
    | c :: rest, last =>
      let sep := c == '-' || c == '_' || c == '.'
      let ok := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
      if !(sep || ok) then false
      else if sep && last then false
      else go rest sep
  s.utf8ByteSize ≥ 2 && s.utf8ByteSize ≤ 64 && go s.toList true

def acctField (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => if validAccountId s then some s else none
  | _ => none

/-- `up_deploy_code` arguments: `hash: String`, `function_call_args: Option<FunctionCallArgs>`. -/
def deployArgs (j : Json) : Option (String × Option FnCall) :=
  match j.getObjVal? "hash" with
  | .ok (.str h) =>
    match j.getObjVal? "function_call_args" with
    | .error _ => some (h, none)
    | .ok .null => some (h, none)
    | .ok f =>
      match f.getObjVal? "function_name", bytesField f "arguments", u128StrField f "amount", gasField f "gas" with
      | .ok (.str n), some a, some amt, some g => some (h, some ⟨n, a, amt, g⟩)
      | _, _, _, _ => none
  | _ => none

/-! ### Output -/

def errText : Err → String
  | .noPermission => "Insufficient permissions for method"
  | .tsNotSet => "Upgradable: staging timestamp isn't set"
  | .tooEarly ts => s!"Upgradable: Deploy code too early: staging ends on {ts}"
  | .noCode => "Upgradable: No staged code"
  | .wrongHash e => s!"Upgradable: Cannot deploy due to wrong hash: expected hash: {e}"
  | .alreadyInit => "Upgradable: staging duration was already initialized"
  | .notInit => "Upgradable: staging duration isn't initialized"
  | .overflow => "attempt to add with overflow"
  | .noStagedUpdate => "Upgradable: No staged update"
  | .durTooEarly ts => s!"Upgradable: Update duration too early: staging ends on {ts}"
  | .noStagedDur => "Upgradable: No staged duration update"

def retNone : Json := Json.mkObj [("kind", "none")]
def retPromise : Json := Json.mkObj [("kind", "promise")]
def retVal (v : Json) : Json := Json.mkObj [("kind", "value"), ("json", v)]

def okOut (ret : Json := retNone) (eff : Json := Json.null) : Json :=
  Json.mkObj [("ok", true), ("err", Json.null), ("ret", ret), ("eff", eff)]

def failOut (msg : String) : Json :=
  Json.mkObj [("ok", false), ("err", msg), ("ret", Json.null), ("eff", Json.null)]

def optNat : Option Nat → Json
  | some n => Json.str (toString n)
  | none => Json.null

def optBool : Option Bool → Json
  | some b => Json.bool b
  | none => Json.null

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
def hexOf (bs : List Nat) : String := String.ofList (bs.flatMap fun b => [hexDigit (b / 16), hexDigit (b % 16)])

/-! ### Dispatch -/

/-- `&mut self` methods without `#[payable]`: near-sdk refuses an attached deposit first. -/
def nonPayable : List String :=
  ["up_stage_code", "up_deploy_code", "up_init_staging_duration", "up_stage_update_staging_duration",
   "up_apply_update_staging_duration", "acl_grant_role", "acl_revoke_role", "acl_renounce_role",
   "acl_add_super_admin", "acl_add_admin", "acl_revoke_admin", "acl_revoke_super_admin",
   "acl_transfer_super_admin", "acl_renounce_admin", "acl_init_super_admin", "withdraw",
   "migrate_ok", "migrate_fail", "new"]

/-- `#[private]` methods: near-sdk checks the predecessor before the deposit. -/
def privateMethods : List String := ["acl_init_super_admin", "migrate_ok", "migrate_fail"]

/-- `&self` methods the harness calls as transactions. -/
def readOnly : List String :=
  ["up_get_delay_status", "up_staged_code_hash", "up_verify_state", "version"]

def deserFail : Json := failOut "Failed to deserialize input from JSON."

def upCall (unchecked : Bool) (hashOf : String → String) (st : St) (t : Nat) (pred : String)
    (c : Call String) (deployRid : String) : St × Json :=
  let allowed := st.acl.allowed pred c
  let res := if unchecked then st.sys.up.callU hashOf t allowed c else st.sys.up.call hashOf t allowed c
  match res with
  | .error e => (st, failOut (errText e))
  | .ok (_, eff) =>
    let sys' := if unchecked then st.sys.stepU hashOf t (.call allowed c)
                else st.sys.step hashOf t (.call allowed c)
    match eff with
    | none => ({ st with sys := sys' }, okOut)
    | some d =>
      let methods := (match d.fc with | some f => [f.name] | none => []) ++ ["up_verify_state"]
      let e := Json.mkObj [
        ("deploy", d.code),
        ("methods", Json.arr (methods.map Json.str).toArray),
        ("fc_args", match d.fc with | some f => Json.str (hexOf f.args) | none => Json.null),
        ("fc_amount", match d.fc with | some f => Json.str (toString f.amount) | none => Json.str "0"),
        ("gas", Json.str (toString ((match d.fc with | some f => f.gas | none => 0) + 2000000000000)))]
      ({ st with sys := sys', rids := st.rids ++ [deployRid] }, okOut retPromise e)

def stepCall (unchecked : Bool) (hashOf : String → String) (st : St) (j : Json) : St × Json :=
  let t := jnat j "t"
  let pred := jstr j "pred"
  let method := jstr j "method"
  let deposit := jnat j "deposit"
  if st.sys.current == stubLabel then
    (st, if method == "up_verify_state" then okOut else failOut "MethodNotFound")
  else if privateMethods.contains method && pred != st.self then
    (st, failOut "is private")
  else if deposit > 0 && nonPayable.contains method then
    (st, failOut "doesn't accept deposit")
  else
    let args : Option Json := (Json.parse (jstr j "args")).toOption
    match method with
    | "up_stage_code" =>
      let code := jstr j "code"
      upCall unchecked hashOf st t pred (.stageCode (if code.isEmpty then none else some code)) ""
    | "up_deploy_code" =>
      match args.bind deployArgs with
      | none => (st, deserFail)
      | some (h, fc) => upCall unchecked hashOf st t pred (.deployCode h fc) (jstr j "deploy_rid")
    | "up_init_staging_duration" =>
      match args.bind (u64Field · "staging_duration") with
      | none => (st, deserFail)
      | some d => upCall unchecked hashOf st t pred (.initDur d) ""
    | "up_stage_update_staging_duration" =>
      match args.bind (u64Field · "staging_duration") with
      | none => (st, deserFail)
      | some d => upCall unchecked hashOf st t pred (.stageDur d) ""
    | "up_apply_update_staging_duration" => upCall unchecked hashOf st t pred .applyDur ""
    | "acl_grant_role" | "acl_revoke_role" =>
      match args.bind (acctField · "account_id"), args.bind (fun a => a.getObjVal? "role" |>.toOption) with
      | some who, some (.str _) =>
        match args.bind roleField with
        | none => (st, failOut "Value does not correspond to a role")
        | some r =>
          let (acl', res) := if method == "acl_grant_role" then st.acl.grant pred r who
                             else st.acl.revoke pred r who
          ({ st with acl := acl' }, okOut (retVal (optBool res)))
      | _, _ => (st, deserFail)
    | "acl_renounce_role" =>
      match args.bind (fun a => a.getObjVal? "role" |>.toOption) with
      | some (.str _) =>
        match args.bind roleField with
        | none => (st, failOut "Value does not correspond to a role")
        | some r =>
          let (acl', res) := st.acl.renounce pred r
          ({ st with acl := acl' }, okOut (retVal (Json.bool res)))
      | _ => (st, deserFail)
    | "acl_add_super_admin" | "acl_revoke_super_admin" | "acl_transfer_super_admin"
    | "acl_add_admin" | "acl_revoke_admin" =>
      -- admin-only methods; the harness calls them from accounts that are not admins: `None`
      if pred == st.acl.superAdmin then (st, failOut "not modelled: admin method by the super-admin")
      else (st, okOut (retVal Json.null))
    | "acl_renounce_admin" => (st, okOut (retVal (Json.bool false)))
    | "acl_init_super_admin" =>
      if pred == st.self then (st, okOut (retVal (Json.bool false)))
      else (st, failOut "is private")
    | "deposit" =>
      match st.vault.deposit pred deposit with
      | .error _ => (st, failOut "Vault: overflow")
      | .ok v => ({ st with vault := v }, okOut)
    | "withdraw" =>
      match args.bind (u128StrField · "amount") with
      | none => (st, deserFail)
      | some amount =>
        match st.vault.withdraw pred amount with
        | .error _ => (st, failOut "Vault: insufficient balance")
        | .ok (v, (to, amt)) =>
          ({ st with vault := v },
            okOut retPromise (Json.mkObj [("transfer", Json.arr #[Json.str to, Json.str (toString amt)])]))
    | "migrate_ok" => (st, if pred == st.self then okOut else failOut "is private")
    | "migrate_fail" =>
      (st, if pred == st.self then failOut "Vault: migration refused" else failOut "is private")
    | "new" => (st, failOut "The contract has already been initialized")
    | m =>
      if readOnly.contains m then (st, okOut (Json.mkObj [("kind", "any")]))
      else (st, failOut "MethodNotFound")

def stepBatch (hashOf : String → String) (st : St) (j : Json) : St × Json :=
  let rid := jstr j "rid"
  let ok := match j.getObjVal? "ok" with | .ok (.bool b) => b | _ => false
  match st.rids.idxOf? rid with
  | none => (st, Json.mkObj [("unexpected_batch", true)])
  | some i =>
    let code := match st.sys.inflight[i]? with | some d => d.code | none => "?"
    let sys' := st.sys.step hashOf (jnat j "t") (.batch i ok)
    ({ st with sys := sys', rids := st.rids.eraseIdx i },
      Json.mkObj [("batch", code), ("ok", ok), ("current", sys'.current)])

def obsOf (hashOf : String → String) (st : St) (users : List String) : Json :=
  let u := st.sys.up
  let roles := st.acl.grants.map fun g => g.1 ++ ":" ++ g.2.name
  Json.mkObj [
    ("status", Json.mkObj [
      ("staging_duration", optNat u.dur),
      ("staging_timestamp", optNat u.stagingTs),
      ("new_staging_duration", optNat u.newDur),
      ("new_staging_duration_timestamp", optNat u.newDurTs)]),
    ("staged", match u.code with | some c => Json.str c | none => Json.null),
    ("staged_hash", match u.stagedCodeHash hashOf with | some h => Json.str h | none => Json.null),
    ("code", st.sys.current),
    ("code_hash", hashOf st.sys.current),
    ("roles", Json.arr (roles.toArray.qsort (· < ·) |>.map Json.str)),
    ("bal", Json.mkObj (users.map fun x => (x, Json.str (toString (st.vault.balanceOf x))))),
    ("inflight", st.sys.inflight.length)]

def processTrace (unchecked : Bool) (line : String) : String :=
  match Json.parse line with
  | .error e => (Json.mkObj [("error", e)]).compress
  | .ok j =>
    let self := jstr j "self"
    let codes : List (String × String) := match j.getObjVal? "codes" with
      | .ok (.obj kvs) => kvs.toList.map fun (k, v) => (k, match v with | .str s => s | _ => "")
      | _ => []
    let hashOf : String → String := fun l => (codes.lookup l).getD ("?" ++ l)
    let users : List String := match j.getObjVal? "users" with
      | .ok (.arr xs) => xs.toList.map fun x => match x with | .str s => s | _ => ""
      | _ => []
    let initDur : Option Nat := match j.getObjVal? "init_dur" with
      | .ok (.str s) => decNat? s
      | _ => none
    let st0 : St := {
      self := self,
      sys := { up := { dur := initDur }, current := jstr j "init_code" },
      acl := { superAdmin := self },
      vault := {},
      rids := [] }
    let steps : List Json := match j.getObjVal? "steps" with | .ok (.arr xs) => xs.toList | _ => []
    let obs : List Json := match j.getObjVal? "obs" with | .ok (.arr xs) => xs.toList | _ => []
    -- Each observation is the state after block `h`: first apply the receipts of blocks ≤ h.
    let rec go (st : St) (steps : List Json) (obs : List Json) (outS outO : Array Json) (fuel : Nat) :
        Array Json × Array Json :=
      match fuel with
      | 0 => (outS, outO)
      | fuel + 1 =>
        match obs with
        | [] =>
          match steps with
          | [] => (outS, outO)
          | s :: rest =>
            let (st', o) := if jstr s "k" == "batch" then stepBatch hashOf st s else stepCall unchecked hashOf st s
            go st' rest [] (outS.push o) outO fuel
        | ob :: obsRest =>
          match steps with
          | s :: rest =>
            if jnat s "h" ≤ jnat ob "h" then
              let (st', o) := if jstr s "k" == "batch" then stepBatch hashOf st s else stepCall unchecked hashOf st s
              go st' rest obs (outS.push o) outO fuel
            else go st steps obsRest outS (outO.push (obsOf hashOf st users)) fuel
          | [] => go st [] obsRest outS (outO.push (obsOf hashOf st users)) fuel
    let (outS, outO) := go st0 steps obs #[] #[] (steps.length + obs.length + 1)
    (Json.mkObj [("id", (j.getObjVal? "id").toOption.getD Json.null),
                 ("steps", Json.arr outS), ("obs", Json.arr outO)]).compress

partial def loop (unchecked : Bool) (hin hout : IO.FS.Stream) : IO Unit := do
  let line ← hin.getLine
  if line.isEmpty then return
  let l := String.ofList ((line.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r' || c == ' ')).reverse)
  if !l.isEmpty then
    hout.putStrLn (processTrace unchecked l)
  loop unchecked hin hout

def main (args : List String) : IO Unit := do
  let hin ← IO.getStdin
  let hout ← IO.getStdout
  loop (args.contains "--unchecked") hin hout
