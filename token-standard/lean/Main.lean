/-
  ftmodel: replays the receipts a near-contract-sim trace executed on the token contract through
  the Lean model (`ProvedFT.exec`) and prints the model's view after every observed block.

  stdin:  one trace per line (written by `ftcert-gen traces`)
  stdout: one line per trace:
    {"id", "init": {...InitOK facts...},
     "steps": [{"ok","ret","transfers","calls","events","rcase"}...],
     "obs":   [{"h","supply","near","storage","map"}...]}

  The decode layer below (JSON arguments as near-sdk 5.29.0 deserializes them, account-id
  validation of near-account-id 2.6.0, the JSON shapes of return values and events) is not part
  of the proved model; it is checked only by conformance on the inputs the harness generates.
-/
import Lean.Data.Json
import ProvedFT.Model

open Lean ProvedFT

/-! ### Decode layer -/

/-- near-account-id 2.6.0 `validate`: 2..64 bytes of `a-z 0-9 - _ .`, separators not at the
    ends and not adjacent. -/
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

/-- A required `U128` / `NearToken` field: a JSON string holding a u128. -/
def u128Field (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => parseU128S s
  | _ => none

/-- `Option<U128>` / `Option<NearToken>`: absent or null → `some none`; a bad value → `none`. -/
def optU128Field (j : Json) (k : String) : Option (Option Nat) :=
  match j.getObjVal? k with
  | .error _ => some none
  | .ok .null => some none
  | .ok (.str s) => (parseU128S s).map some
  | .ok _ => none

def acctField (j : Json) (k : String) : Option Acct :=
  match j.getObjVal? k with
  | .ok (.str s) => if validAccountId s then some s else none
  | _ => none

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

def optStrField (j : Json) (k : String) : Option (Option String) :=
  match j.getObjVal? k with
  | .error _ => some none
  | .ok .null => some none
  | .ok (.str s) => some (some s)
  | .ok _ => none

def strField (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

/-- Arguments of a method that takes any: must be a JSON object. -/
def argsObj (args : String) : Option Json :=
  match Json.parse args with
  | .ok j@(.obj _) => some j
  | _ => none

/-- The standard's methods as the token exports them, with near-sdk 5.29.0 argument
    deserialization. `initMethod` is the token's `#[init]` method. -/
def decode (initMethod name args : String) : Method :=
  let viaArgs (f : Json → Option Method) : Method :=
    match argsObj args with
    | some j => (f j).getD .bad
    | none => .bad
  match name with
  | "ft_transfer" => viaArgs fun j => do
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      let memo ← optStrField j "memo"
      pure (.ft_transfer r x memo)
  | "ft_transfer_call" => viaArgs fun j => do
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      let memo ← optStrField j "memo"
      let msg ← strField j "msg"
      pure (.ft_transfer_call r x memo msg)
  | "ft_resolve_transfer" => viaArgs fun j => do
      let s ← acctField j "sender_id"
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      pure (.ft_resolve_transfer s r x)
  | "storage_deposit" => viaArgs fun j => do
      let a ← optAcctField j "account_id"
      let ro ← optBoolField j "registration_only"
      pure (.storage_deposit a ro)
  | "storage_withdraw" => viaArgs fun j => (optU128Field j "amount").map .storage_withdraw
  | "storage_unregister" => viaArgs fun j => (optBoolField j "force").map .storage_unregister
  | "ft_total_supply" => .ft_total_supply
  | "storage_balance_bounds" => .storage_balance_bounds
  | "ft_balance_of" => viaArgs fun j => (acctField j "account_id").map .ft_balance_of
  | "storage_balance_of" => viaArgs fun j => (acctField j "account_id").map .storage_balance_of
  | n => if n == initMethod then .reinit else .bad

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0

def unhex : List Char → List Nat
  | a :: b :: rest => (hexVal a * 16 + hexVal b) :: unhex rest
  | _ => []

/-! ### JSON helpers -/

def natStr (j : Json) (k : String) : Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => s.toNat!
  | .ok (.num n) => n.mantissa.toNat
  | _ => 0

def strOf (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok (.str s) => s
  | _ => ""

def boolOf (j : Json) (k : String) : Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => b
  | _ => false

def arrOf (j : Json) (k : String) : Array Json :=
  match j.getObjVal? k with
  | .ok (.arr a) => a
  | _ => #[]

def u128J (n : Nat) : Json := Json.str (toString n)

def retJson : Ret → Json
  | .unit => Json.mkObj [("kind", "none")]
  | .promise => Json.mkObj [("kind", "promise")]
  | .u128 n => Json.mkObj [("kind", "value"), ("json", u128J n)]
  | .bool b => Json.mkObj [("kind", "value"), ("json", toJson b)]
  | .storageBalance t a =>
    Json.mkObj [("kind", "value"), ("json", Json.mkObj [("total", u128J t), ("available", u128J a)])]
  | .storageBalanceOpt none => Json.mkObj [("kind", "value"), ("json", Json.null)]
  | .storageBalanceOpt (some (t, a)) =>
    Json.mkObj [("kind", "value"), ("json", Json.mkObj [("total", u128J t), ("available", u128J a)])]
  | .bounds mn mx =>
    Json.mkObj [("kind", "value"), ("json", Json.mkObj [("min", u128J mn),
      ("max", match mx with | some x => u128J x | none => Json.null)])]

def memoFields : Option String → List (String × Json)
  | some m => [("memo", Json.str m)]
  | none => []

/-- The `EVENT_JSON` payload `events.rs` logs, as a JSON value. -/
def evJson : Ev → Json
  | .transfer a b x memo =>
    Json.mkObj [("standard", "nep141"), ("version", "1.0.0"), ("event", "ft_transfer"),
      ("data", Json.arr #[Json.mkObj ([("old_owner_id", Json.str a), ("new_owner_id", Json.str b),
        ("amount", u128J x)] ++ memoFields memo)])]
  | .burn a x memo =>
    Json.mkObj [("standard", "nep141"), ("version", "1.0.0"), ("event", "ft_burn"),
      ("data", Json.arr #[Json.mkObj ([("owner_id", Json.str a), ("amount", u128J x)] ++
        memoFields memo)])]

/-- The model's parameters for a deployment, from what the harness measured about the
    protocol (byte cost, record overhead 40 bytes) and the `accounts` map layout (prefix length):
    an entry is `40 + (prefix + 4 + len id) + 16` bytes; the storage-balance minimum is that for a
    64-character id. -/
structure Deploy where
  self : Acct
  byte : Nat
  prefixLen : Nat
  storage0 : Nat
  init : Accts

def entryBytes (D : Deploy) (a : Acct) : Nat := 60 + D.prefixLen + a.utf8ByteSize

def entriesBytes (D : Deploy) (l : Accts) : Nat := (l.map fun (a, _) => entryBytes D a).foldl (· + ·) 0

def envOf (D : Deploy) : Env :=
  { self := D.self, minBal := (124 + D.prefixLen) * D.byte,
    base := (D.storage0 - entriesBytes D D.init) * D.byte,
    entry := fun a => entryBytes D a * D.byte, cap := 2 ^ 127 }

def storageBytes (D : Deploy) (st : St) : Nat := D.storage0 - entriesBytes D D.init + entriesBytes D st.accts

def obsJson (D : Deploy) (h : Nat) (st : St) : Json :=
  Json.mkObj [("h", toJson h), ("supply", u128J st.supply), ("near", u128J st.near),
    ("storage", toJson (storageBytes D st)),
    ("map", Json.mkObj (st.accts.map fun (a, v) => (a, u128J v)))]

def callJson (self : Acct) (msg : String) : Acct × Acct × Nat → Json
  | (sn, rc, x) =>
    Json.mkObj [("receiver", Json.str rc),
      ("on_args", Json.mkObj [("sender_id", Json.str sn), ("amount", u128J x), ("msg", Json.str msg)]),
      ("resolve_receiver", Json.str self),
      ("resolve_args", Json.mkObj [("sender_id", Json.str sn), ("receiver_id", Json.str rc),
        ("amount", u128J x)]),
      ("resolve_gas", toJson GAS_FOR_RESOLVE_TRANSFER)]

/-- One receipt on the token through the model. -/
def replayStep (D : Deploy) (initMethod : String) (s : St) (j : Json) : St × Json :=
  let E := envOf D
  if strOf j "k" == "in" then
    if boolOf j "ok" && s.near + natStr j "deposit" ≤ E.cap then
      ({ s with near := s.near + natStr j "deposit" }, Json.mkObj [("ok", toJson true)])
    else (s, Json.mkObj [("ok", toJson false)])
  else
    let m := decode initMethod (strOf j "method") (strOf j "args")
    let results : List PR :=
      match j.getObjVal? "res" with
      | .ok r =>
        if boolOf r "failed" then [PR.failed]
        else match r.getObjVal? "okhex" with
          | .ok (.str h) => [PR.ok (unhex h.toList)]
          | _ => []
      | _ => []
    -- Running out of gas is not modelled: a receipt the runtime stopped for gas is the
    -- environment step `resolveFails` / a failed call, which changes nothing.
    if boolOf j "oog" then (s, Json.mkObj [("ok", toJson false), ("oog", toJson true)])
    else
      let rcase : Json := match m, results with
        | .ft_resolve_transfer sn rc amt, res :: _ =>
          let f := refundOf s.accts rc amt res
          if f = 0 then
            Json.str (if unusedOf amt res = 0 then "unused=0" else "receiver-balance=0")
          else if (get s.accts sn).isSome then
            Json.str (if f < unusedOf amt res then "partial-refund" else "refund")
          else Json.str "sender-gone:burn"
        | _, _ => Json.null
      let msg := match m with
        | .ft_transfer_call _ _ _ msg => msg
        | _ => ""
      match exec E s ⟨strOf j "pred", natStr j "deposit", m, results⟩ with
      | none => (s, Json.mkObj [("ok", toJson false)])
      | some o =>
        (o.st, Json.mkObj [("ok", toJson true), ("rcase", rcase), ("ret", retJson o.ret),
          ("transfers", Json.arr (o.transfers.toArray.map fun (a, x) => Json.arr #[Json.str a, u128J x])),
          ("calls", Json.arr (o.calls.toArray.map (callJson D.self msg))),
          ("events", Json.arr (o.events.toArray.map evJson))])

def accts (j : Json) : Accts :=
  match j with
  | .obj kvs => kvs.toList.map fun (k, v) =>
      (k, match v with | .str s => s.toNat! | _ => 0)
  | _ => []

def nodupB : Accts → Bool
  | [] => true
  | (k, _) :: t => (get t k).isNone && nodupB t

def runTrace (t : Json) : Json := Id.run do
  let initJ := (t.getObjVal? "init").toOption.getD Json.null
  let init := accts ((initJ.getObjVal? "map").toOption.getD Json.null)
  let D : Deploy := ⟨strOf t "self", natStr t "byte", natStr t "prefix_len", natStr t "storage0", init⟩
  let E := envOf D
  let initMethod := strOf t "init_method"
  let s0 : St := ⟨init, natStr initJ "supply", natStr t "near0"⟩
  -- InitOK (Model.lean), checked on the observed initial state
  let okNodup := nodupB s0.accts
  let okCons := s0.supply == total s0.accts
  let okBound := decide (s0.supply ≤ U128_MAX)
  let okSolv := decide (s0.accts.length * E.minBal + E.base ≤ s0.near)
  let okStor := decide (entriesBytes D D.init ≤ D.storage0)
  let mut s := s0
  let steps := arrOf t "steps"
  let mut i := 0
  let mut outSteps : Array Json := #[]
  let mut outObs : Array Json := #[]
  for o in arrOf t "obs" do
    let h := natStr o "h"
    while i < steps.size && natStr steps[i]! "h" ≤ h do
      let (s', r) := replayStep D initMethod s steps[i]!
      s := s'
      outSteps := outSteps.push r
      i := i + 1
    outObs := outObs.push (obsJson D h s)
  while i < steps.size do
    let (s', r) := replayStep D initMethod s steps[i]!
    s := s'
    outSteps := outSteps.push r
    i := i + 1
  return Json.mkObj [("id", (t.getObjVal? "id").toOption.getD Json.null),
    ("env", Json.mkObj [("minBal", u128J E.minBal), ("base", u128J E.base),
      ("entry_overhead_bytes", toJson (60 + D.prefixLen))]),
    ("init_ok", Json.mkObj [("nodup", toJson okNodup), ("supply_eq_sum", toJson okCons),
      ("supply_le_u128", toJson okBound), ("storage_solvent", toJson okSolv),
      ("entries_fit", toJson okStor),
      ("all", toJson (okNodup && okCons && okBound && okSolv && okStor))]),
    ("steps", Json.arr outSteps), ("obs", Json.arr outObs)]

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := String.ofList ((line.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r' || c == ' ')).reverse)
  unless l.isEmpty do
    match Json.parse l with
    | .ok t => stdout.putStrLn (runTrace t).compress
    | .error e => stdout.putStrLn (Json.mkObj [("error", Json.str e)]).compress
    stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
