/-
  intentsmodel: replays the receipts a simulator trace executed on the Intents contract through
  the Lean model of its ledger and prints the model's observable state after every receipt.

  stdin:  traces in the format of ../FORMAT.md, one JSON object per line
  stdout: one line per trace
    {"id", "mock",
     "steps": [{"i", "method", "pred", "verdict", "why", "model_ok", "trace_ok", "wnear", "state"}...],
     "summary": {"contract_steps", "agree", "disagree", "skipped", "env", "auth", "not_compared": {reason: n},
                 "wnear", "wnear_agree", "wnear_disagree", "unwrap_callbacks"}}
  and a last line {"total": {...}}. See OBSERVABLE.md.

  For every receipt on the contract the replay takes from the trace only its inputs
  (predecessor, method, arguments, deposit, promise results) and computes with the model
  functions of `Intents/Ledger.lean` (`credit`, `startWithdraw`, `Rs.used`, `resolveWithdraw`,
  `moveBal`, `adminStep`) and of `Intents/Auth.lean` (`Xc.refund`, `resolveTransfer`, `directOk`,
  `admit`, `commitNonce`, `aclStep`) whether it succeeds and the ledger after it.

  A guard that the model has inside one of these functions (a role, a pause, a lock, the
  auth-by-predecessor flag) is evaluated by that function and nowhere else: the decode layer does
  not repeat it. Where the contract tests a guard once per call and the model tests it per
  ledger function (the pause of `intents`, the lock of a signer), the decode layer tests it only
  for the calls that reach no such function.

  The decode layer below (JSON arguments as near-sdk deserializes them, account-id and
  token-id syntax, which methods are views, the guarded methods outside the ledger) is not part
  of the proved model; it is checked only by this comparison. Four sets of rules that used to be
  decode-layer code are the model's now: the refund of `mt_resolve_transfer` (`Xc.refund`,
  `resolveTransfer`), the entry guard of `mt_transfer*` (`directOk`), what is tested of a signed
  payload before its intents run (`admit`: verifying contract, deadline, key of the signer,
  nonce, lock of the signer; the signature itself is not checked), and the near-plugins rules of
  the role table (`aclStep`).
-/
import Lean.Data.Json
import Intents
import IntentsW

open Lean ProvedFT Intents

/-! ### Decode layer -/

/-- near-account-id `validate`: 2..64 bytes of `a-z 0-9 - _ .`, separators not at the ends and
    not adjacent. -/
def validAccountId (s : String) : Bool :=
  let cs := s.toList
  let rec go : List Char → Bool → Bool
    | [], last => !last
    | c :: rest, last =>
      let sep := c == '-' || c == '_' || c == '.'
      let ok := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
      if !(sep || ok) then false
      else if sep && last then false
      else go rest sep
  s.utf8ByteSize ≥ 2 && s.utf8ByteSize ≤ 64 && go cs true

def parseU128S (s : String) : Option Nat := parseU128Str (s.toList.map Char.toNat)

def u128Field (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => parseU128S s
  | _ => none

def acctField (j : Json) (k : String) : Option Acct :=
  match j.getObjVal? k with
  | .ok (.str s) => if validAccountId s then some s else none
  | _ => none

def strField (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def boolField (j : Json) (k : String) : Option Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => some b
  | _ => none

/-- `Option<String>`: absent or null → `some none`; a non-string → `none` (deserialization
    error). -/
def optStrField (j : Json) (k : String) : Option (Option String) :=
  match j.getObjVal? k with
  | .error _ => some none
  | .ok .null => some none
  | .ok (.str s) => some (some s)
  | .ok _ => none

/-- An optional field that must be absent or null (`approval`, `approvals`). `some true`:
    absent; `some false`: present (the method panics "approvals are not supported"). -/
def absentField (j : Json) (k : String) : Bool :=
  match j.getObjVal? k with
  | .error _ => true
  | .ok .null => true
  | .ok _ => false

def strArrField (j : Json) (k : String) : Option (List String) :=
  match j.getObjVal? k with
  | .ok (.arr a) => a.toList.mapM fun x => match x with
    | .str s => some s
    | _ => none
  | _ => none

def u128ArrField (j : Json) (k : String) : Option (List Nat) :=
  (strArrField j k).bind fun l => l.mapM parseU128S

/-- `TokenId::from_str` (crates/primitives/token-id): `<standard>:<data>`. -/
def validTokenId (s : String) : Bool :=
  match s.splitOn ":" with
  | ["nep141", a] => validAccountId a
  | "nep171" :: a :: _ :: _ => validAccountId a
  | "nep245" :: a :: _ :: _ => validAccountId a
  | _ => false

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexBytes : List Char → Option (List Nat)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexVal a
    let y ← hexVal b
    let t ← hexBytes rest
    pure ((x * 16 + y) :: t)
  | _ => none

/-- A promise result as the trace records it. -/
def decodeResult (j : Json) : Option PR :=
  match j.getObjVal? "ok" with
  | .ok (.bool false) => some .failed
  | .ok (.bool true) =>
    match j.getObjVal? "hex" with
    | .ok (.str h) => (hexBytes h.toList).map .ok
    | _ => none
  | _ => none

def decodeResults (j : Json) : List PR :=
  match j.getObjVal? "results" with
  | .ok (.arr a) => a.toList.filterMap decodeResult
  | _ => []

def objPairs (j : Json) : List (String × Json) :=
  match j with
  | .obj kvs => kvs.toList
  | _ => []

/-! ### The replay state: one ledger per token id, shared switches -/

structure RS where
  led : List (String × Accts × Nat) := []
  ctl : Ctl := {}
  /-- near-plugins `AccessControllable`: super-admins and admins of a role (the accounts that may
      change the role table; `ctl.roles` holds the grantees). -/
  supers : List Acct := []
  admins : List (Acct × Role) := []
  /-- Public keys (`world.keys` at the start, then what `add_public_key` and `remove_public_key`
      make of them) and the nonces committed by executed signed payloads, as the model keeps them
      (`Intents.AuthSt`). -/
  auth : AuthSt := {}
  /-- The trace lists no keys (a trace written before `world.keys` existed): keys are not tested. -/
  noKeys : Bool := false
  /-- State outside the ledger that decides whether three guarded methods succeed (`set_fee`,
      `set_fee_collector`, the relayer keys). `world.fees` gives the first two at the start. -/
  fee : Nat := 0
  feeCollector : String := ""
  relayKeys : List String := []

def RS.get (s : RS) (tid : String) : Ledger :=
  match s.led.find? (fun e => e.1 == tid) with
  | some (_, b, sup) => ⟨b, sup, s.ctl⟩
  | none => ⟨[], 0, s.ctl⟩

def RS.put (s : RS) (tid : String) (L : Ledger) : RS :=
  { s with led := (tid, L.bals, L.supply) :: s.led.filter (fun e => e.1 != tid) }

/-- The role table of the replay state, as the model's `Acl`. -/
def RS.acl (s : RS) : Acl := ⟨s.supers, s.admins, s.ctl.roles⟩

/-- `PublicKey::to_implicit_account_id` for the replay: a string that is no account id. The
    traces register every key explicitly for a named account (`world.keys`), so no key of a
    trace is the implicit key of an account of the trace, and the implicit half of
    `Intents.hasKey` is never true on a trace. -/
def replayImplicit : Key → Acct := fun k => "implicit:" ++ k

/-- The strict world as far as the key steps read it: no token, no contract account. -/
def keyCfg : SCfg :=
  { base := { tok := { self := "", minBal := 0, base := 0, entry := fun _ => 0, cap := 0 }, me := "" }
    implicit := replayImplicit, valid := fun _ _ _ => true }

/-- A state of the strict world with the given switches and keys and nothing else. -/
def keyWorld (c : Ctl) (A : AuthSt) : SWorld :=
  { w := { c := { accts := [], supply := 0, near := 0 }, L := { ctl := c } }, auth := A }

/-- A string that is no public key of a trace. -/
def keyProbe : Key := "?"

/-- Whether the strict world's step lets `pred` call `add_public_key` / `remove_public_key` at
    all (the auth-by-predecessor flag). `sstep` returns the state unchanged for a caller it
    refuses, so the question is put to it on a state with the same flags, no lock, and keys chosen
    so that the call shows: no key for an addition, the key present for a removal. Nothing but
    `sstep` decides. -/
def keyCallAllowed (c : Ctl) (pred : Acct) (add : Bool) : Bool :=
  let c0 : Ctl := { authOff := c.authOff }
  if add then
    !(sstep keyCfg (fun _ _ => none) (keyWorld c0 {}) (.addKey pred keyProbe)).auth.keys.isEmpty
  else
    (sstep keyCfg (fun _ _ => none) (keyWorld c0 { keys := [(pred, keyProbe)] })
      (.removeKey pred keyProbe)).auth.keys.isEmpty

def roleNames : List (String × Role) :=
  [("DAO", .DAO), ("FeesManager", .FeesManager), ("RelayerKeysManager", .RelayerKeysManager),
   ("UnrestrictedWithdrawer", .UnrestrictedWithdrawer), ("PauseManager", .PauseManager),
   ("Upgrader", .Upgrader), ("UnpauseManager", .UnpauseManager),
   ("UnrestrictedAccountLocker", .UnrestrictedAccountLocker),
   ("UnrestrictedAccountUnlocker", .UnrestrictedAccountUnlocker), ("SaltManager", .SaltManager),
   ("GarbageCollector", .GarbageCollector),
   ("UnrestrictedAccountManager", .UnrestrictedAccountManager)]

/-- `Role::try_from(&str)` (near-plugins `AccessControlRole`): the variant names. -/
def roleOfString (s : String) : Option Role := (roleNames.find? (fun e => e.1 == s)).map (·.2)

def roleName (r : Role) : String := ((roleNames.find? (fun e => e.2 == r)).map (·.1)).getD "?"

/-- Whether the model's `adminStep` lets the caller make this change. `adminStep` returns the
    state unchanged when the caller lacks the role (or the account is locked), so the question
    is put to it on a state where the change is visible: a pause, a lock or a disabling on the
    state as it is (the entry is added even when it is already there), an unpause, an unlock or
    an enabling on a state where the entry is put in first. Nothing but `adminStep` decides. -/
def stepAllowed (c : Ctl) : Admin → Bool
  | .pause who key => (adminStep c (.pause who key)).paused.length != c.paused.length
  | .unpause who key =>
    let c1 := { c with paused := key :: c.paused }
    (adminStep c1 (.unpause who key)).paused.length != c1.paused.length
  | .lock who a => (adminStep c (.lock who a)).locked.length != c.locked.length
  | .unlock who a =>
    let c1 := { c with locked := a :: c.locked }
    (adminStep c1 (.unlock who a)).locked.length != c1.locked.length
  | .authOffSelf a => (adminStep c (.authOffSelf a)).authOff.length != c.authOff.length
  | .authIntent a _ => (adminStep c (.authIntent a false)).authOff.length != c.authOff.length
  | .authForce who a false =>
    (adminStep c (.authForce who a false)).authOff.length != c.authOff.length
  | .authForce who a true =>
    let c1 := { c with authOff := a :: c.authOff }
    (adminStep c1 (.authForce who a true)).authOff.length != c1.authOff.length
  | .acl _ => true

inductive Res where
  /-- The model says the receipt succeeds, with this state and (when modelled) return value. -/
  | ok (s : RS) (ret : Option Json)
  /-- The model says the receipt fails; nothing changes. -/
  | fail
  /-- The receipt is outside the model. -/
  | skip (why : String)

/-- `DepositMessage` (src/tokens/mod.rs): the receiver named by `msg`, and the signed payloads to
    execute in the same receipt (`execute_intents` with `refund_if_fails`; without it they are
    sent to the contract as a separate `execute_intents` receipt). -/
inductive Target where
  | to (a : Acct) (inline : List Json)
  | bad

/-- Shape of a signed payload (`MultiPayload`): an object with a `standard` tag, a `payload`
    and a `signature`. -/
def signedShape (j : Json) : Bool :=
  (strField j "standard").isSome && (j.getObjVal? "payload").toOption.isSome &&
    (j.getObjVal? "signature").toOption.isSome

/-- The action of a JSON deposit message. The field is a flattened `Option` of an untagged
    enum: when `execute_intents` is missing or anything in it does not deserialize, serde yields
    no action and the message is a plain deposit to `receiver_id` (seen on the deployed wasm:
    a malformed payload with `refund_if_fails` is credited, not refunded). -/
def depositAction (j : Json) : Option (List Json × Bool) :=
  match j.getObjVal? "execute_intents" with
  | .ok (.arr a) =>
    let rif? : Option Bool := match j.getObjVal? "refund_if_fails" with
      | .error _ => some false
      | .ok (.bool b) => some b
      | .ok _ => none
    match rif? with
    | some rif => if a.toList.all signedShape then some (a.toList, rif) else none
    | none => none
  | _ => none

def depositTarget (sender : Acct) (msg : String) : Target :=
  if msg.isEmpty then .to sender []
  else if msg.startsWith "{" then
    match Json.parse msg with
    | .ok j =>
      match acctField j "receiver_id" with
      | some r =>
        match depositAction j with
        | some (payloads, true) => .to r payloads
        | _ => .to r []
      | none => .bad
    | .error _ => .bad
  else if validAccountId msg then .to msg []
  else .bad

def hasStorageDeposit (j : Json) : Bool :=
  match j.getObjVal? "storage_deposit" with
  | .ok .null => false
  | .ok _ => true
  | .error _ => false

/-- The intents of one signed payload. -/
def payloadIntents (sp : Json) : List Json :=
  match (strField sp "payload").bind (fun txt => (Json.parse txt).toOption) with
  | some pl =>
    match pl.getObjVal? "intents" with
    | .ok (.arr a) => a.toList
    | _ => []
  | none => []

/-- An intent whose ledger function tests the pause of `intents` itself: `Via.ok .intent` inside
    `startWithdraw` (`ft_withdraw`), `IntentsW.startUnwrap` (`native_withdraw`, `storage_deposit`,
    the storage deposit of an `mt_withdraw`). -/
def intentTestsPause (j : Json) : Bool :=
  match strField j "intent" with
  | some "ft_withdraw" => true
  | some "native_withdraw" => true
  | some "storage_deposit" => true
  | some "mt_withdraw" => hasStorageDeposit j
  | _ => false

/-- The pause of `intents` (`#[pause(name = "intents")]` on `execute_intents`) as the decode
    layer applies it: only to a call none of whose intents tests it in the model. A call that
    succeeds in the model has run every one of its intents, so for the other calls the model's
    own guard decides. -/
def pausedHere (s : RS) (signed : List Json) : Bool :=
  s.ctl.isPaused "intents" && !(signed.any fun sp => (payloadIntents sp).any intentTestsPause)

/-- After the credit of a deposit: the inline intents, if any. -/
def afterCredit (run : RS → List Json → Option (Option RS)) (s : RS) (inline : List Json)
    (ret : Json) : Res :=
  if inline.isEmpty then .ok s (some ret)
  else if pausedHere s inline then .fail
  else
    match run s inline with
    | none => .fail
    | some none => if s.ctl.isPaused "intents" then .fail else .skip "an intent kind outside the model"
    | some (some s') => .ok s' (some ret)

/-- `ft_on_transfer` (tokens/nep141/deposit.rs:18-75). The token is the predecessor. -/
def mFtOnTransfer (run : RS → List Json → Option (Option RS)) (s : RS) (pred : Acct) (dep : Nat)
    (args : Json) : Res :=
  match acctField args "sender_id", u128Field args "amount", strField args "msg" with
  | some sender, some amt, some msg =>
    if dep != 0 then .fail
    else
      match depositTarget sender msg with
      | .bad => .fail
      | .to recv inline =>
        let tid := "nep141:" ++ pred
        if s.ctl.isPaused "ft_on_transfer" then .fail
        else
          match credit (s.get tid) recv amt with
          | some L' => afterCredit run (s.put tid L') inline (Json.str "0")
          | none => .fail
  | _, _, _ => .fail

/-- `ft_withdraw` (withdraw.rs:25-50) and `ft_force_withdraw` (withdraw.rs:199-225). -/
def mFtWithdraw (s : RS) (pred : Acct) (dep : Nat) (args : Json) (force : Bool) : Res :=
  let owner? := if force then acctField args "owner_id" else some pred
  match owner?, acctField args "token", acctField args "receiver_id", u128Field args "amount",
      optStrField args "memo", optStrField args "msg" with
  | some owner, some token, some receiver, some amt, some memo, some msg =>
    if dep != 1 then .fail
    else
      let tid := "nep141:" ++ token
      let w : Wd := { owner := owner, receiver := receiver, amount := amt, memo := memo, msg := msg }
      let via := if force then Via.force pred else Via.method pred
      match startWithdraw (s.get tid) via w with
      | some L' => .ok (s.put tid L') none
      | none => .fail
  | _, _, _, _, _, _ => .fail

/-- `ft_resolve_withdraw` (withdraw.rs:156-194): `#[private]`, reads promise result 0. -/
def mFtResolveWithdraw (s : RS) (me pred : Acct) (dep : Nat) (args : Json) (results : List PR) :
    Res :=
  if pred != me || dep != 0 then .fail
  else
    match acctField args "token", acctField args "sender_id", u128Field args "amount",
        boolField args "is_call", results with
    | some token, some owner, some amt, some isCall, res :: _ =>
      let r : Rs := ⟨owner, amt, isCall, res, 0⟩
      let tid := "nep141:" ++ token
      match resolveWithdraw (s.get tid) r with
      | some L' => .ok (s.put tid L') (some (Json.str (toString r.used)))
      | none => .fail
    | _, _, _, _, _ => .fail

/-- A batch of internal moves, all or nothing. -/
def moves (s : RS) (auth : MoveAuth) (src dst : Acct) : List (String × Nat) → Option RS
  | [] => some s
  | (tid, amt) :: t =>
    if !validTokenId tid then none
    else
      match moveBal (s.get tid) auth src dst amt with
      | some L' => moves (s.put tid L') auth src dst t
      | none => none

/-- `mt_transfer`, `mt_batch_transfer`, `mt_transfer_call`, `mt_batch_transfer_call`
    (tokens/nep245/core.rs:15-104, `internal_mt_batch_transfer` 164-216). The pause of
    `mt_transfer` and the auth-by-predecessor flag of the caller are tested by the model's
    `directOk`, the lock of the caller by `MoveAuth.ok` inside `moveBal`. -/
def mMtTransfer (s : RS) (pred : Acct) (dep : Nat) (args : Json) (batch call : Bool) : Res :=
  let ids? := if batch then strArrField args "token_ids" else (strField args "token_id").map ([·])
  let amts? := if batch then u128ArrField args "amounts" else (u128Field args "amount").map ([·])
  let noApp := absentField args (if batch then "approvals" else "approval")
  let msgOk := !call || (strField args "msg").isSome
  match acctField args "receiver_id", ids?, amts?, optStrField args "memo" with
  | some receiver, some ids, some amts, some _ =>
    if !msgOk || dep != 1 || !noApp || !directOk s.ctl pred
        || ids.length != amts.length || amts.isEmpty || (call && ids.length > 10) then .fail
    else
      match moves s .owner pred receiver (ids.zip amts) with
      | some s' => .ok s' none
      | none => .fail
  | _, _, _, _ => .fail

/-- `mt_force_transfer`, `mt_force_batch_transfer`, `mt_force_transfer_call`,
    `mt_force_batch_transfer_call` (tokens/nep245/force.rs): `internal_mt_batch_transfer` with
    `force = true` from `owner_id`. No pause key and no auth-by-predecessor flag apply; the role
    is tested by `MoveAuth.ok` inside `moveBal`. -/
def mMtForceTransfer (s : RS) (pred : Acct) (dep : Nat) (args : Json) (batch call : Bool) : Res :=
  let ids? := if batch then strArrField args "token_ids" else (strField args "token_id").map ([·])
  let amts? := if batch then u128ArrField args "amounts" else (u128Field args "amount").map ([·])
  let noApp := absentField args (if batch then "approvals" else "approval")
  let msgOk := !call || (strField args "msg").isSome
  match acctField args "owner_id", acctField args "receiver_id", ids?, amts?,
      optStrField args "memo" with
  | some owner, some receiver, some ids, some amts, some _ =>
    if !msgOk || dep != 1 || !noApp || ids.length != amts.length || amts.isEmpty
        || (call && ids.length > 10) then .fail
    else
      match moves s (.force pred) owner receiver (ids.zip amts) with
      | some s' => .ok s' none
      | none => .fail
  | _, _, _, _, _ => .fail

/-- `nft_force_withdraw` (tokens/nep171/withdraw.rs:199-224): the forced withdrawal of one unit
    of `nep171:<token>:<token_id>`. The role is tested by `Via.ok` inside `startWithdraw`. -/
def mNftForceWithdraw (s : RS) (pred : Acct) (dep : Nat) (args : Json) : Res :=
  match acctField args "owner_id", acctField args "token", acctField args "receiver_id",
      strField args "token_id", optStrField args "memo", optStrField args "msg" with
  | some owner, some token, some receiver, some id, some memo, some msg =>
    if dep != 1 then .fail
    else
      let tid := "nep171:" ++ token ++ ":" ++ id
      let w : Wd := { owner := owner, receiver := receiver, amount := 1, memo := memo, msg := msg }
      match startWithdraw (s.get tid) (.force pred) w with
      | some L' => .ok (s.put tid L') none
      | none => .fail
  | _, _, _, _, _, _ => .fail

/-- `promise_result_checked_json_with_len::<Vec<U128>>(0, n)`: the requested refunds, when the
    result is a JSON array of `n` `U128` strings within the length bound `54 n + 5`. -/
def refundsOf (res : PR) (n : Nat) : Option (List Nat) :=
  match res with
  | .failed => none
  | .ok bytes =>
    if bytes.length > 54 * n + 5 then none
    else
      match String.fromUTF8? (ByteArray.mk (bytes.map (·.toUInt8)).toArray) with
      | none => none
      | some str =>
        match Json.parse str with
        | .ok (.arr a) =>
          match a.toList.mapM (fun x => match x with
              | .str t => parseU128S t
              | _ => none) with
          | some l => if l.length == n then some l else none
          | none => none
        | _ => none

/-- The loop of `mt_resolve_transfer` (tokens/nep245/resolver.rs:40-96): each row is one transfer
    call (`Intents.Xc`) of its ledger id. The refund — the requested one capped by the amount and
    by the receiver's balance — and its move back to the previous owner are the model's
    `Xc.refund` and `resolveTransfer`. Returns the used amounts. -/
def resolveLoop (s : RS) (receiver sender : Acct) :
    List (String × Acct × Nat × Nat) → Option (RS × List Nat)
  | [] => some (s, [])
  | (tid, prev, amt, req) :: t =>
    if !validTokenId tid || prev != sender then none
    else
      let x : Xc := ⟨prev, receiver, amt⟩
      let L := s.get tid
      match resolveTransfer L x req with
      | some L' =>
        (resolveLoop (s.put tid L') receiver sender t).map fun q =>
          (q.1, (amt - x.refund L req) :: q.2)
      | none => none

def mMtResolveTransfer (s : RS) (me pred : Acct) (dep : Nat) (args : Json) (results : List PR) :
    Res :=
  if pred != me || dep != 0 then .fail
  else
    match strArrField args "previous_owner_ids", acctField args "receiver_id",
        strArrField args "token_ids", u128ArrField args "amounts", results with
    | some prevs, some receiver, some ids, some amts, res :: _ =>
      if !absentField args "approvals" || ids.isEmpty || prevs.length != ids.length
          || amts.length != ids.length then .fail
      else
        let reqs := (refundsOf res amts.length).getD amts
        let rows := (ids.zip (prevs.zip (amts.zip reqs)))
        match resolveLoop s receiver (prevs.headD "") rows with
        | some (s', used) => .ok s' (some (Json.arr (used.map (fun u => Json.str (toString u))).toArray))
        | none => .fail
    | _, _, _, _, _ => .fail

/-! ### NEP-245 deposit and withdrawal (ledger part only; no theorem covers these paths) -/

/-- `deposit` over several token ids, all or nothing (tokens/mod.rs:18-74). -/
def credits (s : RS) (owner : Acct) : List (String × Nat) → Option RS
  | [] => some s
  | (tid, amt) :: t =>
    match credit (s.get tid) owner amt with
    | some L' => credits (s.put tid L') owner t
    | none => none

/-- `withdraw` over several token ids, all or nothing (tokens/mod.rs:76-128). -/
def debits (s : RS) (owner : Acct) (force : Bool) : List (String × Nat) → Option RS
  | [] => some s
  | (tid, amt) :: t =>
    match debit (s.get tid) owner amt force with
    | some L' => debits (s.put tid L') owner force t
    | none => none

/-- `mt_on_transfer` (tokens/nep245/deposit.rs:18-109). The token contract is the predecessor;
    the ledger ids are `nep245:<predecessor>:<token id>`. -/
def mMtOnTransfer (run : RS → List Json → Option (Option RS)) (s : RS) (me pred : Acct)
    (dep : Nat) (args : Json) : Res :=
  match acctField args "sender_id", strArrField args "previous_owner_ids",
      strArrField args "token_ids", u128ArrField args "amounts", strField args "msg" with
  | some sender, some prevs, some ids, some amts, some msg =>
    if dep != 0 || s.ctl.isPaused "mt_on_transfer" || amts.isEmpty || ids.length != amts.length
        || prevs.length != ids.length || !prevs.all validAccountId || pred == me
        || ids.any (fun t => t.utf8ByteSize > 127) then .fail
    else
      match depositTarget sender msg with
      | .bad => .fail
      | .to recv inline =>
        match credits s recv ((ids.map fun t => "nep245:" ++ pred ++ ":" ++ t).zip amts) with
        | some s' =>
          afterCredit run s' inline (Json.arr (amts.map (fun _ => Json.str "0")).toArray)
        | none => .fail
  | _, _, _, _, _ => .fail

/-- `mt_withdraw` (tokens/nep245/withdraw.rs:30-58) and `mt_force_withdraw` (267-296),
    `internal_mt_withdraw` (62-93). -/
def mMtWithdraw (s : RS) (pred : Acct) (dep : Nat) (args : Json) (force : Bool) : Res :=
  let owner? := if force then acctField args "owner_id" else some pred
  match owner?, acctField args "token", acctField args "receiver_id", strArrField args "token_ids",
      u128ArrField args "amounts", optStrField args "memo", optStrField args "msg" with
  | some owner, some token, some _, some ids, some amts, some _, some _ =>
    -- the role of a forced withdrawal is the model's (`Via.ok` of `Via.force`), not a list of its own
    let allowed :=
      if force then (Via.force pred).ok s.ctl { owner := pred, receiver := pred, amount := 0 }
      else !s.ctl.isPaused "mt_withdraw" && !s.ctl.authOff.contains pred
    if dep != 1 || !allowed || ids.length != amts.length || ids.isEmpty || ids.length > 10 then .fail
    else
      match debits s owner force ((ids.map fun t => "nep245:" ++ token ++ ":" ++ t).zip amts) with
      | some s' => .ok s' none
      | none => .fail
  | _, _, _, _, _, _, _ => .fail

/-- The result `mt_resolve_withdraw` reads for `is_call`. -/
inductive VecRes where
  | err                      -- failed or too long
  | bad                      -- not a JSON array of `n` `U128`
  | good (l : List Nat)

def vecResult (res : PR) (n : Nat) : VecRes :=
  match res with
  | .failed => .err
  | .ok bytes =>
    if bytes.length > 54 * n + 5 then .err
    else
      match refundsOf res n with
      | some l => .good l
      | none => .bad

/-- `mt_resolve_withdraw` (tokens/nep245/withdraw.rs:208-262). -/
def mMtResolveWithdraw (s : RS) (me pred : Acct) (dep : Nat) (args : Json) (results : List PR) :
    Res :=
  if pred != me || dep != 0 then .fail
  else
    match acctField args "token", acctField args "sender_id", strArrField args "token_ids",
        u128ArrField args "amounts", boolField args "is_call", results with
    | some token, some owner, some ids, some amts, some isCall, res :: _ =>
      if ids.length != amts.length || amts.isEmpty then .fail
      else
        let n := amts.length
        let used0 : List Nat :=
          if isCall then
            match vecResult res n with
            | .good l => l
            | .bad => amts.map fun _ => 0
            | .err => amts
          else
            match res with
            | .ok [] => amts
            | _ => amts.map fun _ => 0
        let used := (used0.zip amts).map fun (u, a) => min u a
        let refunds := ((ids.zip (amts.zip used)).filterMap fun (t, a, u) =>
          if a - u > 0 then some ("nep245:" ++ token ++ ":" ++ t, a - u) else none)
        match credits s owner refunds with
        | some s' => .ok s' (some (Json.arr (used.map (fun u => Json.str (toString u))).toArray))
        | none => .fail
    | _, _, _, _, _, _ => .fail

/-! ### `execute_intents` (the signature itself is not checked) -/

/-- The wNEAR token of the deployment (`config.wnear_id` of the harness world). -/
def wnearId : String := "wrap.near"

def optU128Field (j : Json) (k : String) : Option (Option Nat) :=
  match j.getObjVal? k with
  | .error _ => some none
  | .ok .null => some none
  | .ok (.str s) => (parseU128S s).map some
  | .ok _ => none

/-- The debit of an intent that unwraps (`native_withdraw`, `storage_deposit`, the
    `storage_deposit` of a withdrawal of another token id): `IntentsW.startUnwrap` on the ledger
    of `nep141:<wNEAR>`. -/
def unwrapDebit (s : RS) (signer : Acct) (x : Nat) : Option RS :=
  let wid := "nep141:" ++ wnearId
  (IntentsW.startUnwrap (s.get wid) signer x).map fun L' => s.put wid L'

/-- One intent of a signed payload. `none`: it fails; `some none`: its kind is outside the
    model. -/
def applyIntent (s : RS) (signer : Acct) (j : Json) : Option (Option RS) :=
  match strField j "intent" with
  | some "transfer" =>
    match acctField j "receiver_id", j.getObjVal? "tokens" with
    | some receiver, .ok tokens =>
      let pairs := (objPairs tokens).map fun (tid, v) => (tid, match v with
        | .str a => parseU128S a
        | _ => none)
      if pairs.isEmpty || receiver == signer || pairs.any (fun q => q.2.isNone) then none
      else (moves s .owner signer receiver (pairs.map fun q => (q.1, q.2.getD 0))).map some
    | _, _ => none
  | some "ft_withdraw" =>
    match acctField j "token", acctField j "receiver_id", u128Field j "amount",
        optStrField j "memo", optStrField j "msg", optU128Field j "storage_deposit" with
    | some token, some receiver, some amt, some memo, some msg, some sd =>
      let tid := "nep141:" ++ token
      let w : Wd := { owner := signer, receiver := receiver, amount := amt, memo := memo,
                      msg := msg, sd := sd }
      if token == wnearId then
        -- a withdrawal of wNEAR itself: the amount and the storage deposit leave the same ledger
        (IntentsW.startWithdrawW (s.get tid) .intent w).map fun L' => some (s.put tid L')
      else
        match startWithdraw (s.get tid) .intent w with
        | none => none
        | some L' =>
          match sd with
          | none => some (some (s.put tid L'))
          | some d => (unwrapDebit (s.put tid L') signer d).map some
    | _, _, _, _, _, _ => none
  | some "mt_withdraw" =>
    match acctField j "token", acctField j "receiver_id", strArrField j "token_ids",
        u128ArrField j "amounts", optU128Field j "storage_deposit" with
    | some token, some _, some ids, some amts, some sd =>
      if ids.length != amts.length || ids.isEmpty || ids.length > 10 then none
      else
        let rows := (ids.map fun t => "nep245:" ++ token ++ ":" ++ t).zip amts
        match debits s signer false rows, sd with
        | none, _ => none
        | some s', none => some (some s')
        | some s', some d => (unwrapDebit s' signer d).map some
    | _, _, _, _, _ => none
  | some "native_withdraw" =>
    match acctField j "receiver_id", u128Field j "amount" with
    | some _, some amt => (unwrapDebit s signer amt).map some
    | _, _ => none
  | some "storage_deposit" =>
    match acctField j "contract_id", u128Field j "amount" with
    | some _, some amt => (unwrapDebit s signer amt).map some
    | _, _ => none
  | some "set_auth_by_predecessor_id" =>
    match boolField j "enabled" with
    | some enabled =>
      let a : Admin := .authIntent signer enabled
      if stepAllowed s.ctl a then some (some { s with ctl := adminStep s.ctl a }) else none
    | none => none
  | _ => some none

def applyIntents (s : RS) (signer : Acct) : List Json → Option (Option RS)
  | [] => some (some s)
  | j :: t =>
    match applyIntent s signer j with
    | none => none
    | some none => some none
    | some (some s') => applyIntents s' signer t

def natOfDigits (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-- An RFC 3339 time of the form `YYYY-MM-DDTHH:MM:SS[.fraction]Z` in nanoseconds since
    1970-01-01 (days from the civil date, proleptic Gregorian). Any other form: `none`. -/
def parseDeadlineNs (s : String) : Option Nat :=
  let cs := s.toList
  let num (i n : Nat) : Option Nat := natOfDigits ((cs.drop i).take n)
  let seps := cs[4]? == some '-' && cs[7]? == some '-' && cs[10]? == some 'T'
    && cs[13]? == some ':' && cs[16]? == some ':'
  let frac? : Option Nat :=
    match cs.drop 19 with
    | ['Z'] => some 0
    | '.' :: rest =>
      match rest.reverse with
      | 'Z' :: fr => natOfDigits ((fr.reverse ++ List.replicate 9 '0').take 9)
      | _ => none
    | _ => none
  match seps, num 0 4, num 5 2, num 8 2, num 11 2, num 14 2, num 17 2, frac? with
  | true, some y, some m, some d, some hh, some mm, some ss, some f =>
    if y < 1970 || m < 1 || m > 12 || d < 1 || d > 31 then none
    else
      let y' := if m ≤ 2 then y - 1 else y
      let era := y' / 400
      let yoe := y' - era * 400
      let mp := if m > 2 then m - 3 else m + 9
      let doy := (153 * mp + 2) / 5 + d - 1
      let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
      let days := era * 146097 + doe - 719468
      some ((((days * 24 + hh) * 60 + mm) * 60 + ss) * 1000000000 + f)
  | _, _, _, _, _, _, _, _ => none

/-- What `execute_signed_intent` (core/src/engine/mod.rs:42-80) tests of one signed payload
    before its intents run, except the signature itself. The tests are the model's
    `Intents.admit`: the verifying contract, the deadline against the block time, that the public
    key is one of the signer's, that the nonce is new, that the signer is not locked
    (`commit_nonce`). `none`: rejected; otherwise the state with the nonce committed
    (`Intents.commitNonce`). The decode layer only prepares the payload and the state the question
    is put on: without a block time in the trace, or with a deadline `parseDeadlineNs` does not
    read, the deadline is set to the block time (not expired); in a trace that lists no keys, or
    for a payload without a `public_key` field, the key is put into the table the question is
    asked on (the key is not tested). The table itself starts as `world.keys` and follows the
    receipts of `add_public_key` and `remove_public_key` (`mKey`). -/
def admitPayload (me : Acct) (ts : Option Nat) (s : RS) (sp pl : Json) (signer : Acct) :
    Option RS :=
  match strField pl "verifying_contract", strField pl "deadline", strField pl "nonce" with
  | some vc, some dl, some nonce =>
    let now := ts.getD 0
    let deadline := match ts, parseDeadlineNs dl with
      | some _, some d => d
      | _, _ => now
    let pk? := if s.noKeys then none else strField sp "public_key"
    let key := pk?.getD ""
    let A : AuthSt := match pk? with
      | some _ => s.auth
      | none => { s.auth with keys := (signer, key) :: s.auth.keys }
    let p : Payload := { signer := signer, key := key, contract := vc, deadline := deadline,
                         nonce := nonce }
    if admit replayImplicit me now s.ctl A p then some { s with auth := commitNonce s.auth p }
    else none
  | _, _, _ => none

def applyPayloads (me : Acct) (ts : Option Nat) (s : RS) : List Json → Option (Option RS)
  | [] => some (some s)
  | sp :: t =>
    match (strField sp "payload").bind (fun txt => (Json.parse txt).toOption) with
    | none => none
    | some pl =>
      match acctField pl "signer_id", pl.getObjVal? "intents" with
      | some signer, .ok (.arr intents) =>
        match admitPayload me ts s sp pl signer with
        | none => none
        | some s1 =>
          -- `commit_nonce` needs the signer's account unlocked: `Intents.admit` has tested it
          match applyIntents s1 signer intents.toList with
          | none => none
          | some none => some none
          | some (some s') => applyPayloads me ts s' t
      | some signer, .error _ =>
        match admitPayload me ts s sp pl signer with
        | none => none
        | some s1 => applyPayloads me ts s1 t
      | _, _ => none

/-- `execute_intents` (src/contract/intents/mod.rs:26-42). The signature of a payload is not
    checked; what else is tested before its intents run: `admitPayload`. -/
def mExecuteIntents (me : Acct) (ts : Option Nat) (s : RS) (dep : Nat) (args : Json) : Res :=
  match args.getObjVal? "signed" with
  | .ok (.arr signed) =>
    if dep != 0 || pausedHere s signed.toList then .fail
    else
      match applyPayloads me ts s signed.toList with
      | none => .fail
      | some none =>
        if s.ctl.isPaused "intents" then .fail else .skip "an intent kind outside the model"
      | some (some s') => .ok s' none
  | _ => .fail

/-- The callbacks that follow wNEAR `near_withdraw`: `do_ft_withdraw`, `do_mt_withdraw` (only
    with a storage deposit), `do_native_withdraw`, `do_storage_deposit`. They require the
    `near_withdraw` result to be a success with an empty value and write nothing. -/
def mDoCallback (s : RS) (me pred : Acct) (args : Json) (results : List PR) (always : Bool) :
    Res :=
  if pred != me then .fail
  else
    let needs := always ||
      (match (args.getObjValD "withdraw").getObjVal? "storage_deposit" with
       | .ok .null => false
       | .ok _ => true
       | .error _ => false)
    if !needs then .ok s none
    else
      match results with
      | .ok [] :: _ => .ok s none
      | _ => .fail

/-- `pa_pause_feature` / `pa_unpause_feature` (near-plugins 0.5.3 `Pausable`). Who may: decided
    by `adminStep` (`stepAllowed`). -/
def mPause (s : RS) (pred : Acct) (dep : Nat) (args : Json) (pause : Bool) : Res :=
  match strField args "key" with
  | some key =>
    let a : Admin := if pause then .pause pred key else .unpause pred key
    if dep != 0 || !stepAllowed s.ctl a then .fail
    else
      .ok { s with ctl := adminStep s.ctl a }
        (some (Json.bool (if pause then !s.ctl.paused.contains key else s.ctl.paused.contains key)))
  | none => .fail

/-- `force_lock_account` / `force_unlock_account` (accounts/force.rs:16-52). Who may: decided by
    `adminStep` (`stepAllowed`). -/
def mLock (s : RS) (pred : Acct) (dep : Nat) (args : Json) (lock : Bool) : Res :=
  match acctField args "account_id" with
  | some acct =>
    let a : Admin := if lock then .lock pred acct else .unlock pred acct
    if dep != 1 || !stepAllowed s.ctl a then .fail
    else
      .ok { s with ctl := adminStep s.ctl a }
        (some (Json.bool (if lock then !s.ctl.locked.contains acct else s.ctl.locked.contains acct)))
  | none => .fail

/-- `disable_auth_by_predecessor_id` (accounts/mod.rs:62-72): fails when the flag is already off
    or the account is locked; both are the guard of `adminStep (.authOffSelf _)`. -/
def mAuthSelf (s : RS) (pred : Acct) (dep : Nat) : Res :=
  let a : Admin := .authOffSelf pred
  if dep != 1 || !stepAllowed s.ctl a then .fail
  else .ok { s with ctl := adminStep s.ctl a } none

/-- `force_disable_auth_by_predecessor_ids` / `force_enable_auth_by_predecessor_ids`
    (accounts/force.rs:54-83): the role is that of `adminStep (.authForce ..)`, asked once for
    the call; then every listed account is switched, locked or not. -/
def mAuthForce (s : RS) (pred : Acct) (dep : Nat) (args : Json) (enable : Bool) : Res :=
  match strArrField args "account_ids" with
  | some ids =>
    if !ids.all validAccountId || dep != 1 || !stepAllowed s.ctl (.authForce pred "" enable) then
      .fail
    else
      .ok { s with ctl := ids.foldl (fun c a => adminStep c (.authForce pred a enable)) s.ctl } none
  | none => .fail

/-- `add_public_key` / `remove_public_key` (accounts/mod.rs:40-54): one yoctoNEAR; authentication
    by predecessor enabled for the caller (`keyCallAllowed`: the guard of the strict world's own
    steps); then the model's `addKey` / `removeKey` — the account is not locked, the key is not
    there yet / is there. The key is taken as the contract prints it; the traces pass well-formed
    keys only. -/
def mKey (s : RS) (pred : Acct) (dep : Nat) (args : Json) (add : Bool) : Res :=
  match strField args "public_key" with
  | some k =>
    if dep != 1 || !keyCallAllowed s.ctl pred add then .fail
    else
      match (if add then addKey replayImplicit s.ctl s.auth pred k
             else removeKey replayImplicit s.ctl s.auth pred k) with
      | some A => .ok { s with auth := A } none
      | none => .fail
  | none => .fail

/-- The `acl_*` methods of near-plugins 0.5.3 `AccessControllable` that change the role table. -/
def aclMethods : List String :=
  ["acl_grant_role", "acl_revoke_role", "acl_renounce_role", "acl_add_admin", "acl_revoke_admin",
   "acl_renounce_admin", "acl_add_super_admin", "acl_revoke_super_admin",
   "acl_transfer_super_admin"]

/-- The call of the model (`Intents.AclCall`) a receipt of an `acl_*` method makes, when its
    arguments decode (an unknown role name panics). -/
def aclCallOf (pred : Acct) (method : String) (args : Json) : Option AclCall :=
  let acct? := acctField args "account_id"
  let role? := (strField args "role").bind roleOfString
  match method with
  | "acl_grant_role" => role?.bind fun r => acct?.map fun a => .grantRole pred r a
  | "acl_revoke_role" => role?.bind fun r => acct?.map fun a => .revokeRole pred r a
  | "acl_renounce_role" => role?.map fun r => .renounceRole pred r
  | "acl_add_admin" => role?.bind fun r => acct?.map fun a => .addAdmin pred r a
  | "acl_revoke_admin" => role?.bind fun r => acct?.map fun a => .revokeAdmin pred r a
  | "acl_renounce_admin" => role?.map fun r => .renounceAdmin pred r
  | "acl_add_super_admin" => acct?.map fun a => .addSuper pred a
  | "acl_revoke_super_admin" => acct?.map fun a => .revokeSuper pred a
  | "acl_transfer_super_admin" => acct?.map fun a => .transferSuper pred a
  | _ => none

/-- A string that is no account id: the account for which `aclPermitted` asks. -/
def aclProbe : Acct := "?"

/-- Whether the model's `aclStep` lets the caller of an `acl_*` method change the table at all.
    `aclStep` returns the table unchanged for a caller it refuses, so the question is put to it
    as the same call for an account that is in no list (`aclProbe`), on a table where the change
    shows (for a revocation the entry is put in first). Nothing but `aclStep` decides. `none`:
    the two methods that need no permission. -/
def aclPermitted (x : Acl) : AclCall → Option Bool
  | .grantRole who r _ =>
    some ((aclStep x (.grantRole who r aclProbe)).roles.contains (aclProbe, r))
  | .revokeRole who r _ =>
    some (!(aclStep { x with roles := (aclProbe, r) :: x.roles }
      (.revokeRole who r aclProbe)).roles.contains (aclProbe, r))
  | .addAdmin who r _ =>
    some ((aclStep x (.addAdmin who r aclProbe)).admins.contains (aclProbe, r))
  | .revokeAdmin who r _ =>
    some (!(aclStep { x with admins := (aclProbe, r) :: x.admins }
      (.revokeAdmin who r aclProbe)).admins.contains (aclProbe, r))
  | .addSuper who _ => some ((aclStep x (.addSuper who aclProbe)).supers.contains aclProbe)
  | .revokeSuper who _ =>
    some (!(aclStep { x with supers := aclProbe :: x.supers }
      (.revokeSuper who aclProbe)).supers.contains aclProbe)
  | .transferSuper who _ =>
    some ((aclStep x (.transferSuper who aclProbe)).supers.contains aclProbe)
  | .renounceRole _ _ => none
  | .renounceAdmin _ _ => none

/-- What an `acl_*` method returns: `null` to a caller without the permission, otherwise whether
    the call changed something, read from the table before the call (a transfer of the
    super-admin role to oneself returns `true`). -/
def aclReturn (x : Acl) (c : AclCall) : Json :=
  let changes : Bool := match c with
    | .grantRole _ r a => !x.roles.contains (a, r)
    | .revokeRole _ r a => x.roles.contains (a, r)
    | .renounceRole who r => x.roles.contains (who, r)
    | .addAdmin _ r a => !x.admins.contains (a, r)
    | .revokeAdmin _ r a => x.admins.contains (a, r)
    | .renounceAdmin who r => x.admins.contains (who, r)
    | .addSuper _ a => !x.supers.contains a
    | .revokeSuper _ a => x.supers.contains a
    | .transferSuper who a => a == who || !x.supers.contains a
  match aclPermitted x c with
  | some false => Json.null
  | _ => Json.bool changes

/-- The `acl_*` methods of near-plugins 0.5.3 `AccessControllable` (derive
    `access_controllable.rs:150-420, 598-660`). They are not payable; an unknown role name
    panics; a caller without the permission gets `null` and nothing changes. The table after the
    call is the model's `Intents.aclStep`, and whether the caller has the permission is asked of
    `aclStep` as well (`aclPermitted`); the decode layer has no rule of its own. -/
def mAcl (s : RS) (pred : Acct) (method : String) (dep : Nat) (args : Json) : Res :=
  if dep != 0 then .fail
  else if !aclMethods.contains method then .skip ("method " ++ method)
  else
    match aclCallOf pred method args with
    | none => .fail
    | some c =>
      let x := aclStep s.acl c
      .ok { s with supers := x.supers, admins := x.admins, ctl := adminStep s.ctl (.acl x.roles) }
        (some (aclReturn s.acl c))

/-- A guarded method outside the ledger, called by a holder of one of its roles (fees.rs,
    admin.rs, intents/relayer.rs, salts.rs, garbage_collector.rs, admin_call.rs). Modelled:
    whether the call succeeds, and the three pieces of state that decides it. None of these
    methods touches the ledger or the switches. Decode-layer code, covered by no theorem. -/
def mOutside (s : RS) (m : String) (dep : Nat) (args : Json) : Res :=
  let paused := s.ctl.isPaused "intents"
  let isEmptyArr (k : String) : Option Bool := match args.getObjVal? k with
    | .ok (.arr a) => some a.isEmpty
    | _ => none
  match m with
  | "set_fee" =>
    match (args.getObjValAs? Nat "fee").toOption with
    | some fee =>
      if fee > 1000000 || paused || dep != 1 || fee == s.fee then .fail
      else .ok { s with fee := fee } none
    | none => .fail
  | "set_fee_collector" =>
    match acctField args "fee_collector" with
    | some a =>
      if paused || dep != 1 || a == s.feeCollector then .fail
      else .ok { s with feeCollector := a } none
    | none => .fail
  | "add_full_access_key" => if (strField args "public_key").isNone || dep != 1 then .fail else .ok s none
  | "delete_key" => if (strField args "public_key").isNone || dep != 1 then .fail else .ok s none
  | "add_relayer_key" =>
    if (strField args "public_key").isNone || paused || dep != 1 then .fail else .ok s none
  | "delete_relayer_key" =>
    match strField args "public_key" with
    | some pk =>
      if paused || dep != 1 || !s.relayKeys.contains pk then .fail
      else .ok { s with relayKeys := s.relayKeys.filter fun k => k != pk } none
    | none => .fail
  | "cleanup_nonces" =>
    match isEmptyArr "nonces" with
    | some true => if dep != 1 then .fail else .ok s none
    | some false => .skip "cleanup_nonces with nonces, outside the model"
    | none => .fail
  | "update_current_salt" => if dep != 1 then .fail else .ok s none
  | "invalidate_salts" =>
    match isEmptyArr "salts" with
    | some true => if dep != 1 then .fail else .ok s none
    | some false => .skip "invalidate_salts with salts, outside the model"
    | none => .fail
  | "admin_call" =>
    match isEmptyArr "promises" with
    | some true => if dep == 0 then .fail else .ok s none
    | some false => .skip "admin_call with promises, outside the model"
    | none => .fail
  | m => .skip ("an authorised call of " ++ m ++ ", outside the model")

/-- `do_add_relayer_key` (intents/relayer.rs:29-32), the contract's own receipt after
    `add_relayer_key`: fails when the key is already a relayer key. -/
def mDoAddRelayerKey (s : RS) (me pred : Acct) (args : Json) : Res :=
  if pred != me then .fail
  else
    match strField args "public_key" with
    | some pk => if s.relayKeys.contains pk then .fail else .ok { s with relayKeys := pk :: s.relayKeys } none
    | none => .fail

/-- Role-guarded methods outside the ledger model (contract source at 16d04f6e), with the roles
    one of which the caller must hold. The role test is the model's (`Ctl.any`). -/
def outsideGuards : List (String × List Role) :=
  [("upgrade", [.DAO, .Upgrader]), ("admin_call", [.DAO]), ("set_fee", [.DAO, .FeesManager]),
   ("set_fee_collector", [.DAO, .FeesManager]), ("add_full_access_key", [.DAO]),
   ("delete_key", [.DAO]), ("add_relayer_key", [.DAO, .RelayerKeysManager]),
   ("delete_relayer_key", [.DAO, .RelayerKeysManager]),
   ("cleanup_nonces", [.DAO, .GarbageCollector]), ("update_current_salt", [.DAO, .SaltManager]),
   ("invalidate_salts", [.DAO, .SaltManager])]

def viewMethods : List String :=
  ["mt_balance_of", "mt_batch_balance_of", "mt_supply", "mt_batch_supply", "mt_token",
   "mt_tokens", "mt_tokens_for_owner", "is_account_locked", "pa_is_paused", "pa_all_paused",
   "has_public_key", "public_keys_of", "is_nonce_used", "is_auth_by_predecessor_id_enabled",
   "contract_source_metadata", "acl_role_variants", "acl_is_super_admin", "acl_is_admin",
   "acl_has_role", "acl_has_any_role", "acl_get_super_admins", "acl_get_admins",
   "acl_get_grantees", "acl_get_permissioned_accounts"]

/-- One receipt on the contract. -/
def modelCall (privates : List String) (me : Acct) (ts : Option Nat) (s : RS) (pred : Acct)
    (method : String) (dep : Nat) (args : Json) (results : List PR) : Res :=
  match method with
  | "ft_on_transfer" => mFtOnTransfer (applyPayloads me ts) s pred dep args
  | "ft_withdraw" => mFtWithdraw s pred dep args false
  | "ft_force_withdraw" => mFtWithdraw s pred dep args true
  | "ft_resolve_withdraw" => mFtResolveWithdraw s me pred dep args results
  | "mt_transfer" => mMtTransfer s pred dep args false false
  | "mt_batch_transfer" => mMtTransfer s pred dep args true false
  | "mt_transfer_call" => mMtTransfer s pred dep args false true
  | "mt_batch_transfer_call" => mMtTransfer s pred dep args true true
  | "mt_resolve_transfer" => mMtResolveTransfer s me pred dep args results
  | "mt_on_transfer" => mMtOnTransfer (applyPayloads me ts) s me pred dep args
  | "mt_withdraw" => mMtWithdraw s pred dep args false
  | "mt_force_withdraw" => mMtWithdraw s pred dep args true
  | "mt_resolve_withdraw" => mMtResolveWithdraw s me pred dep args results
  | "execute_intents" => mExecuteIntents me ts s dep args
  | "do_ft_withdraw" => mDoCallback s me pred args results false
  | "do_mt_withdraw" => mDoCallback s me pred args results false
  | "do_native_withdraw" => mDoCallback s me pred args results true
  | "do_storage_deposit" => mDoCallback s me pred args results true
  | "pa_pause_feature" => mPause s pred dep args true
  | "pa_unpause_feature" => mPause s pred dep args false
  | "force_lock_account" => mLock s pred dep args true
  | "force_unlock_account" => mLock s pred dep args false
  | "mt_force_transfer" => mMtForceTransfer s pred dep args false false
  | "mt_force_batch_transfer" => mMtForceTransfer s pred dep args true false
  | "mt_force_transfer_call" => mMtForceTransfer s pred dep args false true
  | "mt_force_batch_transfer_call" => mMtForceTransfer s pred dep args true true
  | "nft_force_withdraw" => mNftForceWithdraw s pred dep args
  | "disable_auth_by_predecessor_id" => mAuthSelf s pred dep
  | "force_disable_auth_by_predecessor_ids" => mAuthForce s pred dep args false
  | "force_enable_auth_by_predecessor_ids" => mAuthForce s pred dep args true
  | "do_add_relayer_key" => mDoAddRelayerKey s me pred args
  | "add_public_key" => mKey s pred dep args true
  | "remove_public_key" => mKey s pred dep args false
  | "new" => .fail
  | m =>
    if privates.contains m && pred != me then .fail
    else if viewMethods.contains m then .ok s none
    else if m.startsWith "acl_" then mAcl s pred m dep args
    else
      match outsideGuards.find? (fun e => e.1 == m) with
      | some (_, roles) => if s.ctl.any pred roles then mOutside s m dep args else .fail
      | none => .skip ("method " ++ m)

/-! ### Which receipts involve wNEAR -/

/-- An intent that reads or writes the ledger id `nep141:<wNEAR>`: a withdrawal of wNEAR, any
    intent that unwraps (`native_withdraw`, `storage_deposit`, a withdrawal with
    `storage_deposit`), a transfer of that id. -/
def intentTouchesWNear (j : Json) : Bool :=
  match strField j "intent" with
  | some "native_withdraw" => true
  | some "storage_deposit" => true
  | some "ft_withdraw" => strField j "token" == some wnearId || hasStorageDeposit j
  | some "mt_withdraw" => hasStorageDeposit j
  | some "nft_withdraw" => hasStorageDeposit j
  | some "transfer" =>
    (objPairs (j.getObjValD "tokens")).any fun q => q.1 == "nep141:" ++ wnearId
  | _ => false

def payloadsTouchWNear (signed : List Json) : Bool :=
  signed.any fun sp =>
    match (strField sp "payload").bind (fun txt => (Json.parse txt).toOption) with
    | some pl =>
      match pl.getObjVal? "intents" with
      | .ok (.arr a) => a.toList.any intentTouchesWNear
      | _ => false
    | none => false

/-- The signed payloads a deposit message asks to execute, whatever `refund_if_fails` says. -/
def msgPayloads (args : Json) : List Json :=
  match strField args "msg" with
  | some msg =>
    if msg.startsWith "{" then
      match Json.parse msg with
      | .ok j =>
        match j.getObjVal? "execute_intents" with
        | .ok (.arr a) => a.toList
        | _ => []
      | .error _ => []
    else []
  | none => []

/-- A receipt on the contract that involves wNEAR: it reads or writes the ledger id
    `nep141:<wNEAR>`, or it is a callback of an unwrap. Decided from the receipt's inputs only
    (predecessor, method, arguments), so failed receipts are counted too. -/
def involvesWNear (pred method : String) (args : Json) : Bool :=
  let wid := "nep141:" ++ wnearId
  let wd := args.getObjValD "withdraw"
  match method with
  | "ft_on_transfer" => pred == wnearId || payloadsTouchWNear (msgPayloads args)
  | "mt_on_transfer" => payloadsTouchWNear (msgPayloads args)
  | "ft_withdraw" => strField args "token" == some wnearId
  | "ft_force_withdraw" => strField args "token" == some wnearId
  | "ft_resolve_withdraw" => strField args "token" == some wnearId
  | "do_native_withdraw" => true
  | "do_storage_deposit" => true
  | "do_ft_withdraw" => strField wd "token" == some wnearId || hasStorageDeposit wd
  | "do_mt_withdraw" => hasStorageDeposit wd
  | "execute_intents" =>
    match args.getObjVal? "signed" with
    | .ok (.arr signed) => payloadsTouchWNear signed.toList
    | _ => false
  | "mt_transfer" => strField args "token_id" == some wid
  | "mt_transfer_call" => strField args "token_id" == some wid
  | "mt_batch_transfer" => ((strArrField args "token_ids").getD []).contains wid
  | "mt_batch_transfer_call" => ((strArrField args "token_ids").getD []).contains wid
  | "mt_resolve_transfer" => ((strArrField args "token_ids").getD []).contains wid
  | _ => false

/-! ### Observable state -/

def sortStrs (l : List String) : List String := (l.toArray.qsort (· < ·)).toList

def dedup (l : List String) : List String :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The accounts whose lock flag the harness reads. -/
def lockWatch : List String :=
  ["owner.near", "alice.near", "bob.near", "carol.near", "recv1.near", "recv2.near", "unreg.near",
   "ghost.near", "evil.near"]

structure Obs where
  ledger : List (String × List (String × Nat))
  supply : List (String × Nat)
  paused : List String
  locked : List String
  /-- Watched accounts with authentication by predecessor id disabled. -/
  authOff : List String
  /-- The role table: super-admins, and `<Role>:<account>` for admins and for grantees. -/
  supers : List String
  admins : List String
  grantees : List String
  deriving BEq

def sortBy1 {α : Type} (l : List (String × α)) : List (String × α) :=
  (l.toArray.qsort (fun a b => a.1 < b.1)).toList

def RS.obs (s : RS) : Obs :=
  let led := s.led.filterMap fun (tid, b, _) =>
    let nz := sortBy1 ((dedup (b.map (·.1))).filterMap fun a =>
      let v := bal b a
      if v == 0 then none else some (a, v))
    if nz.isEmpty then none else some (tid, nz)
  let sup := s.led.filterMap fun (tid, _, sp) => if sp == 0 then none else some (tid, sp)
  let tag (l : List (Acct × Role)) : List String :=
    sortStrs (dedup (l.map fun (a, r) => roleName r ++ ":" ++ a))
  { ledger := sortBy1 led, supply := sortBy1 sup,
    paused := sortStrs (dedup s.ctl.paused),
    locked := sortStrs ((dedup s.ctl.locked).filter lockWatch.contains),
    authOff := sortStrs ((dedup s.ctl.authOff).filter lockWatch.contains),
    supers := sortStrs (dedup s.supers), admins := tag s.admins, grantees := tag s.ctl.roles }

def Obs.toJson (o : Obs) : Json :=
  Json.mkObj [
    ("ledger", Json.mkObj (o.ledger.map fun (tid, l) =>
      (tid, Json.mkObj (l.map fun (a, v) => (a, Json.str (toString v)))))),
    ("supply", Json.mkObj (o.supply.map fun (tid, v) => (tid, Json.str (toString v)))),
    ("paused", Json.arr (o.paused.map Json.str).toArray),
    ("locked", Json.arr (o.locked.map Json.str).toArray),
    ("auth_off", Json.arr (o.authOff.map Json.str).toArray),
    ("acl", Json.mkObj [("super_admins", Json.arr (o.supers.map Json.str).toArray),
      ("admins", Json.arr (o.admins.map Json.str).toArray),
      ("grantees", Json.arr (o.grantees.map Json.str).toArray)])]

def strList (j : Json) : List String :=
  match j with
  | .arr a => a.toList.filterMap fun x => match x with
    | .str s => some s
    | _ => none
  | _ => []

def natOf (j : Json) : Nat :=
  match j with
  | .str s => (parseU128S s).getD 0
  | _ => 0

/-- `{"<Role>": [accounts]}` as pairs. -/
def rolePairs (j : Json) : List (Acct × Role) :=
  (objPairs j).flatMap fun (name, l) =>
    match roleOfString name with
    | some r => (match l with
      | .arr a => a.toList.filterMap fun x => match x with
        | .str acct => some (acct, r)
        | _ => none
      | _ => [])
    | none => []

/-- The trace's `state` as a replay state (used to compare, and to continue after a receipt
    outside the model). What a trace does not record (`auth_off` and `acl` in traces written
    before those fields existed; keys and nonces always) is taken from `prev`. -/
def stateOfTrace (prev : RS) (j : Json) : RS :=
  let ledger := objPairs (j.getObjValD "ledger")
  let supply := objPairs (j.getObjValD "supply")
  let tids := dedup (ledger.map (·.1) ++ supply.map (·.1))
  let led := tids.map fun tid =>
    let b := match ledger.find? (fun e => e.1 == tid) with
      | some (_, m) => (objPairs m).map fun (a, v) => (a, natOf v)
      | none => []
    let sp := match supply.find? (fun e => e.1 == tid) with
      | some (_, v) => natOf v
      | none => 0
    (tid, b, sp)
  let authOff := match j.getObjVal? "auth_off" with
    | .ok v => strList v
    | .error _ => prev.ctl.authOff
  let (supers, admins, grantees) := match j.getObjVal? "acl" with
    | .ok a => (strList (a.getObjValD "super_admins"), rolePairs (a.getObjValD "admins"),
        rolePairs (a.getObjValD "grantees"))
    | .error _ => (prev.supers, prev.admins, prev.ctl.roles)
  { prev with
    led := led,
    ctl := { roles := grantees, paused := strList (j.getObjValD "paused"),
             locked := strList (j.getObjValD "locked"), authOff := authOff },
    supers := supers, admins := admins }

/-- `world.keys`: the public keys each account registered before the trace starts. -/
def keysOfWorld (w : Json) : List (Acct × String) :=
  (objPairs (w.getObjValD "keys")).flatMap fun (a, l) => (strList l).map fun k => (a, k)

def rolesOfWorld (w : Json) : List (Acct × Role) :=
  let r := w.getObjValD "roles"
  let one (k : String) (rs : List Role) : List (Acct × Role) :=
    match r.getObjVal? k with
    | .ok (.str a) => rs.map fun x => (a, x)
    | _ => []
  one "pause" [.PauseManager, .UnpauseManager] ++ one "force_withdraw" [.UnrestrictedWithdrawer] ++
    one "lock" [.UnrestrictedAccountLocker, .UnrestrictedAccountUnlocker]

structure Tally where
  steps : Nat := 0
  agree : Nat := 0
  disagree : Nat := 0
  skipped : Nat := 0
  env : Nat := 0
  auth : Nat := 0
  /-- Receipts that involve wNEAR (`involvesWNear`), and their verdicts. -/
  wnear : Nat := 0
  wnearAgree : Nat := 0
  wnearDisagree : Nat := 0
  /-- Among them: the callbacks that follow `near_withdraw`. -/
  unwrapCb : Nat := 0
  /-- The receipts that were not compared (`env`, `auth`, `skip`), by reason. -/
  why : List (String × Nat) := []

def bumpWhy (l : List (String × Nat)) (k : String) (n : Nat := 1) : List (String × Nat) :=
  if l.any (fun e => e.1 == k) then l.map fun e => if e.1 == k then (e.1, e.2 + n) else e
  else l ++ [(k, n)]

def Tally.toJson (t : Tally) : Json :=
  Json.mkObj [("contract_steps", t.steps), ("agree", t.agree), ("disagree", t.disagree),
    ("skipped", t.skipped), ("env", t.env), ("auth", t.auth),
    ("not_compared", Json.mkObj ((sortBy1 t.why).map fun (k, n) => (k, (n : Json)))),
    ("wnear", t.wnear), ("wnear_agree", t.wnearAgree), ("wnear_disagree", t.wnearDisagree),
    ("unwrap_callbacks", t.unwrapCb)]

def Tally.add (a b : Tally) : Tally :=
  ⟨a.steps + b.steps, a.agree + b.agree, a.disagree + b.disagree, a.skipped + b.skipped,
    a.env + b.env, a.auth + b.auth, a.wnear + b.wnear, a.wnearAgree + b.wnearAgree,
    a.wnearDisagree + b.wnearDisagree, a.unwrapCb + b.unwrapCb,
    b.why.foldl (fun l e => bumpWhy l e.1 e.2) a.why⟩

/-- A callback that follows `near_withdraw`, called by the contract itself (the same methods
    called by another account are rejected as private and are not counted here). -/
def isUnwrapCallback (me pred method : String) (args : Json) : Bool :=
  pred == me &&
    (method == "do_native_withdraw" || method == "do_storage_deposit" ||
      ((method == "do_ft_withdraw" || method == "do_mt_withdraw") &&
        hasStorageDeposit (args.getObjValD "withdraw")))

/-- A failure the environment chose (gas, a forced fault), not the method's logic. -/
def envFailure (step : Json) : Bool :=
  let fault := match step.getObjVal? "fault" with
    | .ok .null => false
    | .ok _ => true
    | .error _ => false
  let status := (strField step "status").getD ""
  fault || (status != "ok" && !status.startsWith "Panic(")

/-- Why the environment made the receipt fail. -/
def envReason (step : Json) : String :=
  let fault := match step.getObjVal? "fault" with
    | .ok .null => false
    | .ok _ => true
    | .error _ => false
  let status := (strField step "status").getD ""
  if fault then "gas: a failure forced by the harness"
  else if status.startsWith "OutOfGas" || status.startsWith "GasLimitExceeded" then
    "gas: ran out of the attached gas"
  else "runtime: " ++ ((status.splitOn "(").headD status)

/-- A signed payload was rejected for a reason the replay does not decide: the signature itself
    (the model has no ed25519), the salted nonce format, and, in a trace that does not record
    them, the block time (deadline) or the registered keys. -/
def authReason (step : Json) (hasTime hasKeys : Bool) : Option String :=
  let status := (strField step "status").getD ""
  let has (k : String) : Bool := (status.splitOn k).length > 1
  if has "invalid signature" then some "signature: not checked by the model"
  else if has "salt" || has "nonce was already expired" || has "deadline is greater than nonce"
      || has "invalid nonce" then some "signature level: salted nonce, outside the model"
  else if !hasTime && has "deadline has expired" then
    some "signature level: deadline, the trace has no block time"
  else if !hasKeys && has "public key" then
    some "signature level: public key, the trace lists no keys"
  else none

def retJson (step : Json) : Option Json :=
  match step.getObjVal? "ret" with
  | .ok r =>
    match r.getObjVal? "kind" with
    | .ok (.str "value") => (r.getObjVal? "json").toOption
    | _ => none
  | _ => none

def replayTrace (t : Json) : Json × Tally := Id.run do
  let world := t.getObjValD "world"
  let me := (strField world "contract").getD "intents.near"
  let privates := strList (world.getObjValD "private")
  let keys := keysOfWorld world
  let hasKeys := !keys.isEmpty
  let fees := world.getObjValD "fees"
  let s0 : RS := { ctl := { roles := rolesOfWorld world }, auth := { keys := keys },
                   noKeys := keys.isEmpty,
                   fee := ((fees.getObjValAs? Nat "fee").toOption).getD 0,
                   feeCollector := (strField fees "fee_collector").getD "" }
  let mut s : RS := stateOfTrace s0 ((t.getObjValD "init").getObjValD "state")
  let mut out : Array Json := #[]
  let mut tally : Tally := {}
  let steps := match t.getObjVal? "steps" with
    | .ok (.arr a) => a
    | _ => #[]
  for step in steps do
    let recv := (strField step "recv").getD ""
    let method? := strField step "method"
    if recv != me then continue
    match method? with
    | none => continue
    | some method =>
      let pred := (strField step "pred").getD ""
      let dep := (u128Field step "deposit").getD 0
      let args := step.getObjValD "args"
      let traceOk := (boolField step "ok").getD false
      let traceState := stateOfTrace s (step.getObjValD "state")
      let ts := (strField step "ts").bind parseU128S
      tally := { tally with steps := tally.steps + 1 }
      let mut verdict := ""
      let mut why := ""
      let mut modelOk : Json := Json.null
      if envFailure step then
        -- the receipt failed for a reason the model does not decide (gas); what the model does
        -- say is that a failed receipt changes nothing, and that is compared
        if s.obs == traceState.obs then
          verdict := "env"
          why := envReason step
          tally := { tally with env := tally.env + 1, why := bumpWhy tally.why why }
        else
          verdict := "DISAGREE"
          tally := { tally with disagree := tally.disagree + 1 }
      else
        match modelCall privates me ts s pred method dep args (decodeResults step) with
        | .skip reason =>
          verdict := "skip"
          why := "outside the model: " ++ reason
          tally := { tally with skipped := tally.skipped + 1, why := bumpWhy tally.why why }
          s := traceState
        | .fail =>
          modelOk := Json.bool false
          if traceOk == false && s.obs == traceState.obs then
            verdict := "agree"
            tally := { tally with agree := tally.agree + 1 }
          else
            verdict := "DISAGREE"
            tally := { tally with disagree := tally.disagree + 1 }
        | .ok s' ret =>
          modelOk := Json.bool true
          let retOk := match ret, retJson step with
            | some a, some b => a == b
            | _, _ => true
          if traceOk == true && s'.obs == traceState.obs && retOk then
            verdict := "agree"
            tally := { tally with agree := tally.agree + 1 }
            s := s'
          else if traceOk == false && s.obs == traceState.obs
              && (authReason step ts.isSome hasKeys).isSome then
            verdict := "auth"
            why := (authReason step ts.isSome hasKeys).getD ""
            modelOk := Json.null
            tally := { tally with auth := tally.auth + 1, why := bumpWhy tally.why why }
          else
            verdict := "DISAGREE"
            tally := { tally with disagree := tally.disagree + 1 }
            out := out.push (Json.mkObj [("i", step.getObjValD "i"), ("method", method),
              ("pred", pred), ("verdict", "model-state-before-resync"), ("state", s'.obs.toJson)])
      if verdict == "DISAGREE" then s := traceState
      let wn := involvesWNear pred method args
      if wn then
        tally := { tally with
          wnear := tally.wnear + 1
          wnearAgree := tally.wnearAgree + (if verdict == "agree" then 1 else 0)
          wnearDisagree := tally.wnearDisagree + (if verdict == "DISAGREE" then 1 else 0)
          unwrapCb := tally.unwrapCb + (if isUnwrapCallback me pred method args then 1 else 0) }
      out := out.push (Json.mkObj [("i", step.getObjValD "i"), ("method", method), ("pred", pred),
        ("verdict", verdict), ("why", why), ("model_ok", modelOk), ("trace_ok", traceOk),
        ("wnear", wn), ("state", s.obs.toJson)])
  return (Json.mkObj [("id", t.getObjValD "id"), ("mock", t.getObjValD "mock"),
    ("steps", Json.arr out), ("summary", tally.toJson)], tally)

/-! ### World-level replay: the token and the contract inside one `Intents.World`

  The replay above runs each receipt of the contract through the ledger functions, with the
  token as the environment the trace recorded. This one runs the receipts of both contracts
  through `Intents.stdStep` — the step function of the two-contract world the theorems are
  about — on one `World` state: the token is `ProvedFT.exec`, the contract's callbacks read the
  results the token model produced, not the ones the trace recorded.

  From a trace it takes the token's state before the first receipt (`init.tokens_state`) and,
  for every receipt on the token or on the contract, the inputs that the world leaves open:
  who called what with which arguments, what a third-party receiver answered, and whether the
  environment made the receipt fail (gas). Which entry of the model's in-flight lists a receipt
  is — which settlement callback, which queued token receipt, which `ft_resolve_withdraw` — is
  followed by receipt id: every entry is paired with the id of the receipt the wasm created
  for it.

  Compared after every such receipt: whether it succeeded (where the world decides that), the
  ledger of `nep141:<token>` and its supply, the switches, the token balance of the contract,
  and the token balance of every watched account and the token's supply (the trace side of the
  last two is `init.tokens_state` plus the measured `moves`).

  Internal transfers of the token's ledger id and the `acl_*` calls run through
  `Intents.sstep`, the step function of the strict world (`Intents/Strict.lean`), on the same
  state. A transfer call leaves an entry in `SWorld.calls`, paired with the receipt id of its
  `mt_resolve_transfer`; that receipt must find its entry, with the same sender, receiver and
  amount, its refund is the model's, and the entry must be gone afterwards. The role table
  (super-admins, admins, grantees) is advanced by the model's rules and compared with the trace
  after every receipt. Keys, nonces and the `payload` step of the strict world are not followed
  here: the intents of a successful call are applied one by one, as before.

  The world is the one of the standard token; receipts that concern other ledger ids are not
  part of it. Mock traces are skipped: their token is not the standard one on purpose. -/

def optAcctField (j : Json) (k : String) : Option (Option Acct) :=
  match j.getObjVal? k with
  | .error _ => some none
  | .ok .null => some none
  | .ok (.str s) => if validAccountId s then some (some s) else none
  | .ok _ => none

def optBoolField (j : Json) (k : String) : Option (Option Bool) :=
  match j.getObjVal? k with
  | .error _ => some none
  | .ok .null => some none
  | .ok (.bool b) => some (some b)
  | .ok _ => none

/-- A method of the token with near-sdk 5.29.0 argument deserialization (`ProvedFT.Method`). -/
def tokMethod (name : String) (args : Json) : Method :=
  let j := if (args.getObjVal? "$raw").toOption.isSome then Json.null else args
  let orBad (m : Option Method) : Method := m.getD .bad
  match name with
  | "ft_transfer" => orBad do
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      let memo ← optStrField j "memo"
      pure (.ft_transfer r x memo)
  | "ft_transfer_call" => orBad do
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      let memo ← optStrField j "memo"
      let msg ← strField j "msg"
      pure (.ft_transfer_call r x memo msg)
  | "ft_resolve_transfer" => orBad do
      let s ← acctField j "sender_id"
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      pure (.ft_resolve_transfer s r x)
  | "storage_deposit" => orBad do
      let a ← optAcctField j "account_id"
      let ro ← optBoolField j "registration_only"
      pure (.storage_deposit a ro)
  | "storage_withdraw" => orBad ((optU128Field j "amount").map .storage_withdraw)
  | "storage_unregister" => orBad ((optBoolField j "force").map .storage_unregister)
  | "ft_total_supply" => .ft_total_supply
  | "storage_balance_bounds" => .storage_balance_bounds
  | "ft_balance_of" => orBad ((acctField j "account_id").map .ft_balance_of)
  | "storage_balance_of" => orBad ((acctField j "account_id").map .storage_balance_of)
  | "new" => .reinit
  | "new_default_meta" => .reinit
  | _ => .bad

/-- The world state with, for every in-flight entry of the model, the receipt that stands for
    it in the trace. -/
structure WS where
  w : World
  /-- Per `pend` entry: the token's settlement callback, the `ft_on_transfer` it waits for, and
      (for a withdrawal of the contract) the `ft_resolve_withdraw` that follows. -/
  pendIds : List (String × String × String) := []
  /-- Per `unwrap` entry: the `do_ft_withdraw` callback and the `ft_resolve_withdraw`. -/
  unwrapIds : List (String × String) := []
  /-- Per `outbox` entry: the token receipt and the `ft_resolve_withdraw`. -/
  outboxIds : List (String × String) := []
  /-- Per `resolves` entry: the `ft_resolve_withdraw` receipt. -/
  resolveIds : List String := []
  /-- The transfer calls of the token's ledger id whose `mt_resolve_transfer` is in flight
      (`SWorld.calls` of the strict world), and per entry that callback's receipt. -/
  calls : List Xc := []
  callIds : List String := []
  /-- near-plugins super-admins and admins of a role (`SWorld.supers`, `SWorld.admins`). -/
  supers : List Acct := []
  admins : List (Acct × Role) := []

/-- The state of the strict world (`Intents/Strict.lean`) the replay is in. Keys and nonces are
    not followed by the world-level replay. -/
def WS.strict (ws : WS) : SWorld :=
  { w := ws.w, calls := ws.calls, supers := ws.supers, admins := ws.admins }

def WS.ofStrict (ws : WS) (S : SWorld) : WS :=
  { ws with w := S.w, calls := S.calls, supers := S.supers, admins := S.admins }

/-- The strict world of the replay: no implicit keys (`replayImplicit`), signatures not tested. -/
def strictCfg (K : Cfg) : SCfg := { base := K, implicit := replayImplicit, valid := fun _ _ _ => true }

structure WOut where
  ws : WS
  /-- Whether the world says the receipt succeeds, when it decides that. -/
  decided : Option Bool := none
  /-- The trace and the model do not fit together (an in-flight entry is missing, …). -/
  err : Option String := none
  /-- The receipt is part of this world. -/
  inWorld : Bool := true

def ridOf (j : Json) : String := (strField j "rid").getD ""

def callsOf (step : Json) : List Json :=
  match step.getObjVal? "calls" with
  | .ok (.arr a) => a.toList
  | _ => []

/-- The settlement callbacks a token receipt created: each with the `ft_on_transfer` it waits
    for. -/
def settlementsOf (T : Acct) (step : Json) : List (String × String) :=
  let cs := callsOf step
  let ons := cs.filter fun c => strField c "method" == some "ft_on_transfer"
  let cbs := cs.filter fun c =>
    strField c "recv" == some T && strField c "method" == some "ft_resolve_transfer"
  (cbs.zip ons).map fun (cb, on) => (ridOf cb, ridOf on)

def prSame : PR → PR → Bool
  | .failed, .failed => true
  | .ok a, .ok b => a == b
  | _, _ => false

/-- A token panic that is about gas, which the model does not have. -/
def tokGasPanic (step : Json) : Bool :=
  (((strField step "status").getD "").splitOn "More gas is required").length > 1

/-- One receipt on the token. -/
def worldTokenStep (K : Cfg) (ws : WS) (step : Json) : WOut :=
  let T := K.tok.self
  let S := ws.w
  let pred := (strField step "pred").getD ""
  let dep := (u128Field step "deposit").getD 0
  let args := step.getObjValD "args"
  let methods := strList (step.getObjValD "methods")
  let traceOk := (boolField step "ok").getD false
  let env := envFailure step || tokGasPanic step
  let myRid := ridOf step
  match methods with
  | [] =>
    if traceOk then { ws := { ws with w := stdStep K S (.tokNearIn dep) } } else { ws := ws }
  | m :: _ =>
    if pred == T && m == "ft_resolve_transfer" && (boolField step "callback").getD false then
      match ws.pendIds.findIdx? (fun e => e.1 == myRid) with
      | none => { ws := ws, err := some "a settlement callback the model does not have in flight" }
      | some i =>
        let res := (decodeResults step).headD .failed
        let S' := stdStep K S (if env then .tokResolveFails i else .tokResolve i res)
        let gone := S'.pend.length < S.pend.length
        let after := (ws.pendIds[i]?.getD ("", "", "")).2.2
        let decided : Option Bool :=
          if env then none
          else
            match S.pend[i]? with
            | some e =>
              match resOf e res with
              | some r =>
                some (ProvedFT.exec K.tok S.c
                  ⟨T, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [r]⟩).isSome
              | none => some false
            | none => none
        { ws := { ws with
            w := S'
            pendIds := if gone then ws.pendIds.eraseIdx i else ws.pendIds
            resolveIds :=
              if S'.resolves.length > S.resolves.length then ws.resolveIds ++ [after]
              else ws.resolveIds }
          decided := decided
          err := if gone then none
            else some "the settlement ran before the contract's ft_on_transfer in the model" }
    else if pred == K.me then
      if m == "storage_deposit" && methods.length == 1 then
        match optAcctField args "account_id" with
        | some (some acc) =>
          if env then { ws := ws }
          else
            { ws := { ws with w := stdStep K S (.meStorageDeposit acc dep) }
              decided := some (ProvedFT.exec K.tok S.c
                ⟨K.me, dep, .storage_deposit (some acc) none, []⟩).isSome }
        | _ => { ws := ws, decided := if env then none else some false }
      else
        match ws.outboxIds.findIdx? (fun e => e.1 == myRid) with
        | none =>
          { ws := ws, err := some "a token receipt of the contract that is not in the model's outbox" }
        | some j =>
          let after := (ws.outboxIds[j]?.getD ("", "")).2
          let S' := stdStep K S (if env then .tokXferFails j else .tokXfer j)
          let started := S'.pend.length - S.pend.length
          let cbs := settlementsOf T step
          { ws := { ws with
              w := S'
              outboxIds := ws.outboxIds.eraseIdx j
              pendIds := ws.pendIds ++ (cbs.take started).map (fun (cb, on) => (cb, on, after))
              resolveIds :=
                if S'.resolves.length > S.resolves.length then ws.resolveIds ++ [after]
                else ws.resolveIds }
            decided := if env then none
              else (S.outbox[j]?).map fun w => (xferBatch (ProvedFT.exec K.tok) K.me S.c w).isSome
            err := if started > cbs.length then
                some "the model starts a settlement the receipt did not create" else none }
    else if env then { ws := ws }
    else
      let meth := tokMethod m args
      let rs := decodeResults step
      let o := ProvedFT.exec K.tok S.c ⟨pred, dep, meth, ProvedFT.resultsFor K.tok pred rs⟩
      let S' := stdStep K S (.tokCall pred dep meth rs)
      let started := S'.pend.length - S.pend.length
      let cbs := settlementsOf T step
      { ws := { ws with
          w := S'
          pendIds := ws.pendIds ++ (cbs.take started).map (fun (cb, on) => (cb, on, "")) }
        decided := some o.isSome
        err := if started > cbs.length then
            some "the model starts a settlement the receipt did not create" else none }

/-- The receipts a contract receipt created for its withdrawals of the token. -/
structure Made where
  /-- Receipts on the token. -/
  tok : List String
  /-- `do_ft_withdraw` callbacks for the token. -/
  dos : List String
  /-- `ft_resolve_withdraw` callbacks for the token. -/
  res : List String
  /-- `mt_resolve_transfer` callbacks, with their arguments. -/
  mtRes : List Json

def madeBy (K : Cfg) (step : Json) : Made :=
  let T := K.tok.self
  let cs := callsOf step
  { tok := (cs.filter fun c => strField c "recv" == some T).map ridOf
    dos := (cs.filter fun c => strField c "recv" == some K.me
              && strField c "method" == some "do_ft_withdraw"
              && strField ((c.getObjValD "args").getObjValD "withdraw") "token" == some T).map ridOf
    res := (cs.filter fun c => strField c "recv" == some K.me
              && strField c "method" == some "ft_resolve_withdraw"
              && strField (c.getObjValD "args") "token" == some T).map ridOf
    mtRes := cs.filter fun c => strField c "recv" == some K.me
              && strField c "method" == some "mt_resolve_transfer" }

structure Cur where
  ws : WS
  made : Made
  err : Option String := none

/-- One intent of a successful call, as steps of the world. -/
def worldIntent (K : Cfg) (cur : Cur) (signer : Acct) (j : Json) : Cur :=
  let T := K.tok.self
  let tid := "nep141:" ++ T
  let S := cur.ws.w
  match strField j "intent" with
  | some "ft_withdraw" =>
    if strField j "token" != some T then cur
    else
      match acctField j "receiver_id", u128Field j "amount", optStrField j "memo",
          optStrField j "msg", optU128Field j "storage_deposit" with
      | some receiver, some amt, some memo, some msg, some sd =>
        let w : Wd := { owner := signer, receiver := receiver, amount := amt, memo := memo,
                        msg := msg, sd := sd }
        let S' := stdStep K S (.ftWithdraw .intent w)
        match cur.made.res with
        | [] => { cur with err := some "no ft_resolve_withdraw receipt for a withdrawal intent" }
        | r :: rest =>
          if sd.isNone then
            if S'.outbox.length > S.outbox.length then
              { cur with
                ws := { cur.ws with
                  w := S', outboxIds := cur.ws.outboxIds ++ [(cur.made.tok.headD "", r)] }
                made := { cur.made with tok := cur.made.tok.drop 1, res := rest } }
            else { cur with err := some "the wasm ran a withdrawal intent the model refuses" }
          else
            if S'.unwrap.length > S.unwrap.length then
              { cur with
                ws := { cur.ws with
                  w := S', unwrapIds := cur.ws.unwrapIds ++ [(cur.made.dos.headD "", r)] }
                made := { cur.made with dos := cur.made.dos.drop 1, res := rest } }
            else { cur with err := some "the wasm ran a withdrawal intent the model refuses" }
      | _, _, _, _, _ => { cur with err := some "an ft_withdraw intent that does not decode" }
  | some "transfer" =>
    match acctField j "receiver_id", j.getObjVal? "tokens" with
    | some receiver, .ok tokens =>
      match (objPairs tokens).find? (fun q => q.1 == tid) with
      | some (_, .str a) =>
        match parseU128S a with
        | some amt =>
          -- a `Transfer` with a notification (`msg`) is a transfer call: `mt_resolve_transfer`
          -- follows, and the model keeps an entry for it
          let call := (strField j "msg").isSome
          match runOp (strictCfg K) (ProvedFT.exec K.tok) signer cur.ws.strict
              (.move receiver amt call) with
          | none => cur
          | some SS =>
            if !call then { cur with ws := cur.ws.ofStrict SS }
            else
              match cur.made.mtRes.findIdx? (fun c =>
                  let a := c.getObjValD "args"
                  strField a "receiver_id" == some receiver
                    && ((strArrField a "previous_owner_ids").getD []).head? == some signer
                    && ((strArrField a "token_ids").getD []).contains tid) with
              | none =>
                { cur with
                  ws := cur.ws.ofStrict SS
                  err := some "no mt_resolve_transfer receipt for a transfer with a notification" }
              | some i =>
                { cur with
                  ws := { cur.ws.ofStrict SS with
                    callIds := cur.ws.callIds ++ [ridOf (cur.made.mtRes[i]?.getD Json.null)] }
                  made := { cur.made with mtRes := cur.made.mtRes.eraseIdx i } }
        | none => cur
      | _ => cur
    | _, _ => cur
  | some "set_auth_by_predecessor_id" =>
    match boolField j "enabled" with
    | some en =>
      { cur with ws := { cur.ws with w := stdStep K S (.admin (.authIntent signer en)) } }
    | none => cur
  | _ => cur

def worldPayloads (K : Cfg) (cur : Cur) (signed : List Json) : Cur :=
  signed.foldl (fun c sp =>
    match (strField sp "payload").bind (fun txt => (Json.parse txt).toOption) with
    | some pl =>
      match acctField pl "signer_id", pl.getObjVal? "intents" with
      | some signer, .ok (.arr intents) => intents.toList.foldl (fun c j => worldIntent K c signer j) c
      | _, _ => c
    | none => c) cur

/-- The rows of a transfer that are of the token's ledger id: their amounts, in order. -/
def tokRows (tid : String) (args : Json) (batch : Bool) : List Nat :=
  let ids := if batch then (strArrField args "token_ids").getD []
    else ((strField args "token_id").map ([·])).getD []
  let amts := if batch then (u128ArrField args "amounts").getD []
    else ((u128Field args "amount").map ([·])).getD []
  (ids.zip amts).filterMap fun (i, a) => if i == tid then some a else none

/-- The rows of one transfer of the token's id as steps of the strict world (`mk` makes the
    step of a row from its amount). An entry that a transfer call leaves in `SWorld.calls` is
    paired with the receipt of its `mt_resolve_transfer`; an entry without such a receipt is an
    error. -/
def transferAll (G : SCfg) (ws : WS) (mk : Nat → SStep) (amts : List Nat) (cbRid : String) :
    WS × Option String :=
  amts.foldl (fun (q : WS × Option String) a =>
    let ws := q.1
    let S' := sstd G ws.strict (mk a)
    let grew := S'.calls.length > ws.calls.length
    ({ ws.ofStrict S' with callIds := if grew then ws.callIds ++ [cbRid] else ws.callIds },
      if grew && cbRid == "" then
        some "the model has an mt_resolve_transfer in flight for which the wasm created no receipt"
      else q.2)) (ws, none)

/-- The `mt_resolve_transfer` receipt a transfer call created. -/
def resolveRid (K : Cfg) (step : Json) : String :=
  (((madeBy K step).mtRes.head?).map ridOf).getD ""

/-- The rows of one `mt_resolve_transfer` receipt that are of the token's id, as steps of the
    strict world. Each row must be the next transfer call in flight that waits for this receipt,
    with the same sender, receiver and amount. `fails`: the receipt changed nothing (out of gas,
    or a panic), so each of its entries is dropped without a refund. -/
def resolveRows (G : SCfg) (ws : WS) (rid : String) (receiver : Acct) (fails : Bool) :
    List (Acct × Nat × Nat) → WS × Option String
  | [] => (ws, none)
  | (prev, amt, req) :: t =>
    match ws.callIds.findIdx? (fun e => e == rid) with
    | none => (ws, some "an mt_resolve_transfer for which the model has no transfer call in flight")
    | some k =>
      let same := ws.calls[k]? == some (⟨prev, receiver, amt⟩ : Xc)
      let S' := sstd G ws.strict (if fails then .resolveTransferFails k else .resolveTransfer k req)
      -- the callback ran (or failed) once: the model must not have it in flight any more
      let gone := S'.calls.length + 1 == ws.calls.length
      let ws1 : WS := { ws.ofStrict S' with
        calls := if gone then S'.calls else ws.calls.eraseIdx k
        callIds := ws.callIds.eraseIdx k }
      let r := resolveRows G ws1 rid receiver fails t
      (r.1,
        if !same then
          some "mt_resolve_transfer has other arguments than the transfer call the model has in flight"
        else if !gone then
          some "the model still has the transfer call in flight after its mt_resolve_transfer"
        else r.2)

/-- One receipt on the contract. -/
def worldContractStep (K : Cfg) (ws : WS) (step traceState : Json) : WOut :=
  let T := K.tok.self
  let tid := "nep141:" ++ T
  let S := ws.w
  let G := strictCfg K
  let pred := (strField step "pred").getD ""
  let method := (strField step "method").getD ""
  let dep := (u128Field step "deposit").getD 0
  let args := step.getObjValD "args"
  let traceOk := (boolField step "ok").getD false
  let env := envFailure step
  let myRid := ridOf step
  let out (w : World) : WS := { ws with w := w }
  let outside : WOut := { ws := ws, inWorld := false }
  let admin (pre : Bool) (a : Admin) : WOut :=
    if env then { ws := ws }
    else if !pre then { ws := ws, decided := some false }
    else { ws := out (stdStep K S (.admin a)), decided := some (stepAllowed S.L.ctl a) }
  match method with
  | "ft_on_transfer" =>
    if pred != T then outside
    else
      match ws.pendIds.findIdx? (fun e => e.2.1 == myRid) with
      | none => { ws := ws, err := some "an ft_on_transfer the model's token did not send" }
      | some i =>
        let target := match acctField args "sender_id", u128Field args "amount",
            strField args "msg" with
          | some sender, some _, some msg => if dep != 0 then Target.bad else depositTarget sender msg
          | _, _, _ => Target.bad
        let told := match S.pend[i]?, acctField args "sender_id", u128Field args "amount" with
          | some e, some sender, some amt => e.sender == sender && e.amount == amt
          | _, _, _ => false
        match target with
        | .to recv inline =>
          -- inline intents (a deposit message with `execute_intents`): their outcome is taken
          -- from the trace, their effect on this ledger is applied
          let good := !env && (inline.isEmpty || traceOk)
          let S1 := stdStep K S (.onTransfer i recv good)
          let credited := match S1.pend[i]? with
            | some e => e.ann == Ann.dep (some true)
            | none => false
          let cur := if credited && !inline.isEmpty then
              worldPayloads K { ws := out S1, made := madeBy K step } inline
            else { ws := out S1, made := madeBy K step }
          { ws := cur.ws
            decided := if env || !inline.isEmpty then none else some credited
            err := if !told then some "the token model announced another transfer than the receipt carries"
              else cur.err }
        | .bad =>
          { ws := out (stdStep K S (.onTransfer i K.me false))
            decided := if env then none else some false }
  | "ft_withdraw" | "ft_force_withdraw" =>
    let force := method == "ft_force_withdraw"
    if strField args "token" != some T then outside
    else if env then { ws := ws }
    else
      let owner? := if force then acctField args "owner_id" else some pred
      match owner?, acctField args "receiver_id", u128Field args "amount", optStrField args "memo",
          optStrField args "msg" with
      | some owner, some receiver, some amt, some memo, some msg =>
        if dep != 1 then { ws := ws, decided := some false }
        else
          let w : Wd := { owner := owner, receiver := receiver, amount := amt, memo := memo, msg := msg }
          let S' := stdStep K S (.ftWithdraw (if force then .force pred else .method pred) w)
          let started := S'.outbox.length > S.outbox.length
          let made := madeBy K step
          { ws := { ws with
              w := S'
              outboxIds := if started then ws.outboxIds ++ [(made.tok.headD "", made.res.headD "")]
                else ws.outboxIds }
            decided := some started }
      | _, _, _, _, _ => { ws := ws, decided := some false }
  | "execute_intents" =>
    let signed := match args.getObjVal? "signed" with
      | .ok (.arr a) => a.toList
      | _ => []
    if env || !traceOk then { ws := ws }
    else
      let cur := worldPayloads K { ws := ws, made := madeBy K step } signed
      { ws := cur.ws, err := cur.err }
  | "do_ft_withdraw" =>
    let wd := args.getObjValD "withdraw"
    if pred != K.me || strField wd "token" != some T then outside
    else
      match ws.unwrapIds.findIdx? (fun e => e.1 == myRid) with
      | none => outside      -- without a storage deposit the contract does not call this method on itself
      | some j =>
        let after := (ws.unwrapIds[j]?.getD ("", "")).2
        let S' := stdStep K S (.doFtWithdraw j traceOk)
        { ws := { ws with
            w := S'
            unwrapIds := ws.unwrapIds.eraseIdx j
            outboxIds := if traceOk then ws.outboxIds ++ [((madeBy K step).tok.headD "", after)]
              else ws.outboxIds
            resolveIds := if traceOk then ws.resolveIds else ws.resolveIds ++ [after] } }
  | "ft_resolve_withdraw" =>
    if pred != K.me || strField args "token" != some T then outside
    else
      match ws.resolveIds.findIdx? (fun e => e == myRid) with
      | none => { ws := ws, err := some "an ft_resolve_withdraw the model does not have ready" }
      | some k =>
        let seen := (decodeResults step).headD .failed
        let same := match S.resolves[k]? with
          | some r =>
            prSame r.res seen && some r.amount == u128Field args "amount"
              && some r.owner == acctField args "sender_id" && some r.isCall == boolField args "is_call"
          | none => false
        { ws := { ws with
            w := stdStep K S (if env then .resolveWdFails k else .resolveWd k)
            resolveIds := ws.resolveIds.eraseIdx k }
          decided := if env then none else (S.resolves[k]?).map fun r => (resolveWithdraw S.L r).isSome
          err := if same then none
            else some "ft_resolve_withdraw read another result, or has other arguments, than the model derived" }
  | "mt_transfer" | "mt_batch_transfer" | "mt_transfer_call" | "mt_batch_transfer_call" =>
    let batch := method == "mt_batch_transfer" || method == "mt_batch_transfer_call"
    let call := method == "mt_transfer_call" || method == "mt_batch_transfer_call"
    let rows := tokRows tid args batch
    if rows.isEmpty then outside
    else if env || !traceOk then { ws := ws }
    else
      match acctField args "receiver_id" with
      | some receiver =>
        let r := transferAll G ws (fun a => .transfer pred receiver a call) rows (resolveRid K step)
        { ws := r.1, err := r.2 }
      | none => { ws := ws, err := some "a successful transfer without a receiver" }
  | "mt_force_transfer" | "mt_force_batch_transfer" | "mt_force_transfer_call"
  | "mt_force_batch_transfer_call" =>
    let batch := method == "mt_force_batch_transfer" || method == "mt_force_batch_transfer_call"
    let call := method == "mt_force_transfer_call" || method == "mt_force_batch_transfer_call"
    let rows := tokRows tid args batch
    if rows.isEmpty then outside
    else if env || !traceOk then { ws := ws }
    else
      match acctField args "owner_id", acctField args "receiver_id" with
      | some owner, some receiver =>
        let r := transferAll G ws (fun a => .forceTransfer pred owner receiver a call) rows
          (resolveRid K step)
        { ws := r.1, err := r.2 }
      | _, _ => { ws := ws, err := some "a successful forced transfer without owner or receiver" }
  | "mt_resolve_transfer" =>
    if pred != K.me then outside
    else
      match strArrField args "previous_owner_ids", acctField args "receiver_id",
          strArrField args "token_ids", u128ArrField args "amounts" with
      | some prevs, some receiver, some ids, some amts =>
        if !ids.contains tid then outside
        else
          -- every row of the token's id is one transfer call in flight; a receipt that changed
          -- nothing (gas, a panic) drops its entries
          let reqs := (refundsOf ((decodeResults step).headD .failed) amts.length).getD amts
          let rows := (ids.zip (prevs.zip (amts.zip reqs))).filterMap fun (id, row) =>
            if id == tid then some row else none
          let r := resolveRows G ws myRid receiver (env || !traceOk) rows
          { ws := r.1, err := r.2 }
      | _, _, _, _ => outside
  | "pa_pause_feature" =>
    match strField args "key" with
    | some key => admin (dep == 0) (.pause pred key)
    | none => { ws := ws, decided := if env then none else some false }
  | "pa_unpause_feature" =>
    match strField args "key" with
    | some key => admin (dep == 0) (.unpause pred key)
    | none => { ws := ws, decided := if env then none else some false }
  | "force_lock_account" =>
    match acctField args "account_id" with
    | some a => admin (dep == 1) (.lock pred a)
    | none => { ws := ws, decided := if env then none else some false }
  | "force_unlock_account" =>
    match acctField args "account_id" with
    | some a => admin (dep == 1) (.unlock pred a)
    | none => { ws := ws, decided := if env then none else some false }
  | "disable_auth_by_predecessor_id" => admin (dep == 1) (.authOffSelf pred)
  | "force_disable_auth_by_predecessor_ids" | "force_enable_auth_by_predecessor_ids" =>
    let enable := method == "force_enable_auth_by_predecessor_ids"
    match strArrField args "account_ids" with
    | some ids =>
      if env then { ws := ws }
      else if !ids.all validAccountId || dep != 1 then { ws := ws, decided := some false }
      else
        { ws := out (ids.foldl (fun S a => stdStep K S (.admin (.authForce pred a enable))) S)
          decided := some (stepAllowed S.L.ctl (.authForce pred "" enable)) }
    | none => { ws := ws, decided := if env then none else some false }
  | m =>
    if m.startsWith "acl_" && traceOk && !env then
      -- the role table changes by the rules of the strict world (`Intents.aclStep`); a trace
      -- that does not record the table is not followed
      match traceState.getObjVal? "acl" with
      | .ok _ =>
        match aclCallOf pred m args with
        | some c => { ws := ws.ofStrict (sstd G ws.strict (.acl c)) }
        | none => { ws := ws }
      | .error _ => outside
    else outside

/-- The token's balances and supply as the trace measured them: `init.tokens_state` plus the
    `moves` of every receipt so far. -/
structure TokSeen where
  bals : List (Acct × Nat) := []
  supply : Nat := 0

def signedNat (s : String) : Bool × Nat :=
  match s.toList with
  | '-' :: rest => (true, (parseU128S (String.ofList rest)).getD 0)
  | _ => (false, (parseU128S s).getD 0)

def TokSeen.apply (t : TokSeen) (T : Acct) (step : Json) : TokSeen :=
  match step.getObjVal? "moves" with
  | .ok (.arr ms) =>
    ms.foldl (fun t m =>
      match m with
      | .arr #[.str c, .null, holder, .str d] =>
        if c != T then t
        else
          let (neg, n) := signedNat d
          match holder with
          | .str h =>
            let cur := ((t.bals.find? (fun e => e.1 == h)).map (·.2)).getD 0
            { t with bals := (h, if neg then cur - n else cur + n) :: t.bals.filter (fun e => e.1 != h) }
          | _ => { t with supply := if neg then t.supply - n else t.supply + n }
      | _ => t) t
  | _ => t

/-- What differs between the world state and the trace after a receipt, if anything. -/
def worldDiff (K : Cfg) (holders : List Acct) (ws : WS) (st : Json) (seen : TokSeen) :
    Option String :=
  let S := ws.w
  let tid := "nep141:" ++ K.tok.self
  let led := (objPairs ((st.getObjValD "ledger").getObjValD tid)).map fun (a, v) => (a, natOf v)
  let accts := dedup (led.map (·.1) ++ S.L.bals.map (·.1))
  let ledOk := accts.all fun a => bal S.L.bals a == ((led.find? (fun e => e.1 == a)).map (·.2)).getD 0
  let supOk := S.L.supply == natOf ((st.getObjValD "supply").getObjValD tid)
  let heldOk := bal S.c.accts K.me == natOf ((st.getObjValD "held").getObjValD tid)
  let pausedOk := sortStrs (dedup S.L.ctl.paused) == sortStrs (strList (st.getObjValD "paused"))
  let lockedOk := sortStrs ((dedup S.L.ctl.locked).filter lockWatch.contains)
    == sortStrs (strList (st.getObjValD "locked"))
  let authOk := match st.getObjVal? "auth_off" with
    | .ok v => sortStrs ((dedup S.L.ctl.authOff).filter lockWatch.contains) == sortStrs (strList v)
    | .error _ => true
  let tokOk := holders.all fun a =>
    bal S.c.accts a == ((seen.bals.find? (fun e => e.1 == a)).map (·.2)).getD 0
  let tokSupOk := S.c.supply == seen.supply
  let aclOk := match st.getObjVal? "acl" with
    | .ok a =>
      let tag (l : List (Acct × Role)) : List String :=
        sortStrs (dedup (l.map fun (a, r) => roleName r ++ ":" ++ a))
      tag S.L.ctl.roles == tag (rolePairs (a.getObjValD "grantees"))
        && tag ws.admins == tag (rolePairs (a.getObjValD "admins"))
        && sortStrs (dedup ws.supers) == sortStrs (dedup (strList (a.getObjValD "super_admins")))
    | .error _ => true
  if !ledOk then some "the ledger balances of the token's id"
  else if !supOk then some "the ledger supply of the token's id"
  else if !heldOk then some "the token balance of the contract"
  else if !pausedOk then some "the paused keys"
  else if !lockedOk then some "the locked accounts"
  else if !authOk then some "the auth-by-predecessor flags"
  else if !tokOk then some "a token balance"
  else if !tokSupOk then some "the token supply"
  else if !aclOk then some "the role table"
  else none

structure WTally where
  /-- Traces replayed, and traces left out because their token is a mock. -/
  traces : Nat := 0
  mockTraces : Nat := 0
  /-- Receipts on the token and receipts on the contract that are part of the world. -/
  tokenReceipts : Nat := 0
  contractReceipts : Nat := 0
  /-- Receipts on the contract about other ledger ids: not part of this world. -/
  outside : Nat := 0
  agree : Nat := 0
  disagree : Nat := 0
  /-- Failures the environment chose (gas); that nothing changed is compared. -/
  env : Nat := 0

def WTally.toJson (t : WTally) : Json :=
  Json.mkObj [("traces", t.traces), ("mock_traces_left_out", t.mockTraces),
    ("token_receipts", t.tokenReceipts), ("contract_receipts", t.contractReceipts),
    ("contract_receipts_of_other_ledger_ids", t.outside), ("agree", t.agree),
    ("disagree", t.disagree), ("env", t.env)]

def WTally.add (a b : WTally) : WTally :=
  ⟨a.traces + b.traces, a.mockTraces + b.mockTraces, a.tokenReceipts + b.tokenReceipts,
    a.contractReceipts + b.contractReceipts, a.outside + b.outside, a.agree + b.agree,
    a.disagree + b.disagree, a.env + b.env⟩

/-- `storage_balance_bounds().min` of the standard token (125 bytes of storage). -/
def tokMinBal : Nat := 1250000000000000000000

/-- The world replay of one trace: the tally and the first disagreements. -/
def replayWorld (t : Json) : WTally × Array Json := Id.run do
  if t.getObjValD "mock" == Json.bool true then return ({ mockTraces := 1 }, #[])
  let world := t.getObjValD "world"
  let me := (strField world "contract").getD "intents.near"
  let T := match world.getObjVal? "assets" with
    | .ok (.arr a) => (a.toList.findSome? fun x =>
        match x.getObjVal? "inner" with
        | .ok .null => strField x "contract"
        | _ => none).getD "token.near"
    | _ => "token.near"
  let holders := strList (world.getObjValD "holders")
  let init := t.getObjValD "init"
  let ts := (init.getObjValD "tokens_state").getObjValD T
  let registered := strList (ts.getObjValD "registered")
  let balOf (a : Acct) : Nat := natOf ((ts.getObjValD "balances").getObjValD a)
  -- The NEAR balance of the token is not in the trace. The token model runs with parameters
  -- under which its NEAR conditions hold: no base stake, no stake per entry, a balance and a
  -- cap that no trace approaches.
  let E : Env := { self := T, minBal := tokMinBal, base := 0, entry := fun _ => 0,
                   cap := 10 ^ 36 }
  let K : Cfg := { tok := E, me := me }
  let s0 : RS := stateOfTrace { ctl := { roles := rolesOfWorld world } } (init.getObjValD "state")
  let c0 : St := { accts := registered.map fun a => (a, balOf a), supply := natOf (ts.getObjValD "supply"),
                   near := 10 ^ 33 }
  let mut ws : WS := { w := { c := c0, L := { bals := [], supply := 0, ctl := s0.ctl } },
                       supers := s0.supers, admins := s0.admins }
  let mut seen : TokSeen := { bals := holders.map fun a => (a, balOf a), supply := c0.supply }
  let mut tally : WTally := { traces := 1 }
  let mut bad : Array Json := #[]
  let steps := match t.getObjVal? "steps" with
    | .ok (.arr a) => a
    | _ => #[]
  for step in steps do
    let recv := (strField step "recv").getD ""
    let traceOk := (boolField step "ok").getD false
    let st := step.getObjValD "state"
    seen := seen.apply T step
    if recv != T && !(recv == me && (strField step "method").isSome) then continue
    let before := ws
    let o := if recv == T then worldTokenStep K ws step else worldContractStep K ws step st
    ws := o.ws
    if !o.inWorld then
      tally := { tally with outside := tally.outside + 1 }
      continue
    if recv == T then tally := { tally with tokenReceipts := tally.tokenReceipts + 1 }
    else tally := { tally with contractReceipts := tally.contractReceipts + 1 }
    let why : Option String :=
      match o.err with
      | some e => some e
      | none =>
        match o.decided with
        | some b =>
          if b != traceOk then
            some (if b then "the world says the receipt succeeds, it failed"
              else "the world says the receipt fails, it succeeded")
          else worldDiff K holders ws st seen
        | none => worldDiff K holders ws st seen
    match why with
    | none =>
      if (envFailure step || (recv == T && tokGasPanic step)) && !traceOk then
        tally := { tally with env := tally.env + 1 }
      else tally := { tally with agree := tally.agree + 1 }
    | some e =>
      tally := { tally with disagree := tally.disagree + 1 }
      if bad.size < 5 then
        bad := bad.push (Json.mkObj [("i", step.getObjValD "i"), ("recv", recv),
          ("method", step.getObjValD "method"), ("pred", step.getObjValD "pred"),
          ("ok", traceOk), ("why", e),
          ("in_flight_before", Json.mkObj [("pend", before.w.pend.length),
            ("outbox", before.w.outbox.length), ("unwrap", before.w.unwrap.length),
            ("resolves", before.w.resolves.length), ("calls", before.calls.length)])])
  return (tally, bad)

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) (total : Tally) (wtotal : WTally)
    (quiet world : Bool) : IO (Tally × WTally) := do
  let line ← h.getLine
  if line.isEmpty then return (total, wtotal)
  if line.trimAscii.isEmpty then loop h out total wtotal quiet world
  else
    match Json.parse line with
    | .error e =>
      out.putStrLn (Json.mkObj [("error", e)]).compress
      loop h out total wtotal quiet world
    | .ok t =>
      match t.getObjVal? "sim_panic" with
      | .ok _ =>
        out.putStrLn (Json.mkObj [("id", t.getObjValD "id"), ("sim_panic", true)]).compress
        loop h out total wtotal quiet world
      | .error _ =>
        let (j, tally) := replayTrace t
        let (wt, wbad) := if world then replayWorld t else ({}, #[])
        let extra : List (String × Json) :=
          if world then [("world", wt.toJson), ("world_disagreements", Json.arr wbad)] else []
        if quiet then
          out.putStrLn (Json.mkObj ([("id", t.getObjValD "id"), ("mock", t.getObjValD "mock"),
            ("summary", tally.toJson)] ++ extra)).compress
        else out.putStrLn (j.mergeObj (Json.mkObj extra)).compress
        loop h out (total.add tally) (wtotal.add wt) quiet world

/-- `intentsmodel [--summary] [--world]`: `--summary` leaves the per-receipt records out;
    `--world` adds the world-level replay of every trace whose token is the standard one. -/
def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let world := args.contains "--world"
  let (total, wtotal) ← loop stdin stdout {} {} (args.contains "--summary") world
  stdout.putStrLn (Json.mkObj ([("total", total.toJson)] ++
    (if world then [("world", wtotal.toJson)] else []))).compress
  return (if total.disagree == 0 && wtotal.disagree == 0 then 0 else 1)
