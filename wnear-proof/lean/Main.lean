/-
  wnearmodel: replays the receipts a near-contract-sim trace executed on wrap.near through the
  Lean model and prints the model's view after every observed block.

  stdin:  one trace per line (written by `wnear-gen traces`)
  stdout: one line per trace:
    {"id", "steps": [{"ok","ret","transfers","oog"}...],
     "obs": [{"h","supply","near","storage","map"}...]}

  The decode layer below (JSON arguments, account-id validation, U128 strings, the promise
  result's bytes) mirrors near-sdk 3.1.0 / serde_json for the inputs the harness generates; it
  is not part of the proved model.
-/
import Lean.Data.Json
import WNear.Model

open Lean WNear

/-! ### Decode layer -/

/-- near-sdk 3.1.0 `env::is_valid_account_id`. -/
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
  cs.length ≥ 2 && cs.length ≤ 64 && go cs true

def digitsVal (cs : List Char) : Nat := cs.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0

/-- Rust `u128::from_str_radix(s, 10)`: optional '+', at least one digit, no overflow. -/
def parseU128Chars (cs : List Char) : Option Nat :=
  let ds := match cs with
    | '+' :: rest => rest
    | _ => cs
  if ds.isEmpty then none
  else if ds.all Char.isDigit then
    let n := digitsVal ds
    if n ≤ U128_MAX then some n else none
  else none

/-- A required `U128` field: a JSON string holding a u128. -/
def u128Field (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.str s) => parseU128Chars s.toList
  | _ => none

/-- `Option<U128>`: absent or null → `some none`; a bad value → `none` (deserialization fails). -/
def optU128Field (j : Json) (k : String) : Option (Option Nat) :=
  match j.getObjVal? k with
  | .error _ => some none
  | .ok .null => some none
  | .ok (.str s) => (parseU128Chars s.toList).map some
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

def optStrField (j : Json) (k : String) : Option Unit :=
  match j.getObjVal? k with
  | .error _ => some ()
  | .ok .null => some ()
  | .ok (.str _) => some ()
  | .ok _ => none

def strField (j : Json) (k : String) : Option Unit :=
  match j.getObjVal? k with
  | .ok (.str _) => some ()
  | _ => none

/-- Arguments of a method that takes any: must be a JSON object. -/
def argsObj (args : String) : Option Json :=
  match Json.parse args with
  | .ok j@(.obj _) => some j
  | _ => none

/-- The exported methods of the deployed wasm, with near-sdk 3.1.0 argument deserialization. -/
def decode (name args : String) : Method :=
  let viaArgs (f : Json → Option Method) : Method :=
    match argsObj args with
    | some j => (f j).getD .bad
    | none => .bad
  match name with
  | "new" => .new
  | "near_deposit" => .near_deposit
  | "near_withdraw" => viaArgs fun j => (u128Field j "amount").map .near_withdraw
  | "ft_transfer" => viaArgs fun j => do
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      let _ ← optStrField j "memo"
      pure (.ft_transfer r x)
  | "ft_transfer_call" => viaArgs fun j => do
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      let _ ← optStrField j "memo"
      let _ ← strField j "msg"
      pure (.ft_transfer_call r x)
  | "ft_resolve_transfer" => viaArgs fun j => do
      let s ← acctField j "sender_id"
      let r ← acctField j "receiver_id"
      let x ← u128Field j "amount"
      pure (.ft_resolve_transfer s r x)
  | "storage_deposit" => viaArgs fun j => do
      let a ← optAcctField j "account_id"
      let _ ← optBoolField j "registration_only"
      pure (.storage_deposit a)
  | "storage_withdraw" => viaArgs fun j => (optU128Field j "amount").map .storage_withdraw
  | "storage_unregister" => viaArgs fun j => (optBoolField j "force").map .storage_unregister
  | "ft_total_supply" | "ft_metadata" | "storage_balance_bounds" | "storage_minimum_balance" =>
      .view
  | "ft_balance_of" | "storage_balance_of" => viaArgs fun j => (acctField j "account_id").map fun _ => .view
  | _ => .bad

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0

def unhex : List Char → List Nat
  | a :: b :: rest => (hexVal a * 16 + hexVal b) :: unhex rest
  | _ => []

def isWs (b : Nat) : Bool := b == 0x20 || b == 0x09 || b == 0x0a || b == 0x0d

/-- `serde_json::from_slice::<U128>(bytes)` for escape-free input: optional JSON whitespace
    around one JSON string whose content is a u128 decimal (`from_str_radix`). -/
def parsePromiseValue (bytes : List Nat) : Option Nat :=
  let t := ((bytes.dropWhile isWs).reverse.dropWhile isWs).reverse
  match t with
  | 0x22 :: rest =>
    match rest.reverse with
    | 0x22 :: innerRev =>
      let inner := innerRev.reverse
      if inner.any (fun b => b == 0x22 || b == 0x5c || b < 0x20 || b ≥ 0x80) then none
      else parseU128Chars (inner.map Char.ofNat)
    | _ => none
  | _ => none

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

def storageBytes (st : St) (storage0 : Nat) : Nat :=
  storage0 + (st.accts.map fun (a, _) => 61 + a.utf8ByteSize).foldl (· + ·) 0

def obsJson (h : Nat) (st : St) (storage0 : Nat) : Json :=
  Json.mkObj [("h", toJson h), ("supply", u128J st.supply), ("near", u128J st.near),
    ("storage", toJson (storageBytes st storage0)),
    ("map", Json.mkObj (st.accts.map fun (a, v) => (a, u128J v)))]

/-- One receipt on wrap.near through the model. -/
def replayStep (E : Env) (s : St) (j : Json) : St × Json :=
  if strOf j "k" == "in" then
    if boolOf j "ok" && s.near + natStr j "deposit" ≤ E.cap then
      ({ s with near := s.near + natStr j "deposit" }, Json.mkObj [("ok", toJson true)])
    else (s, Json.mkObj [("ok", toJson false)])
  else
    let m := decode (strOf j "method") (strOf j "args")
    let results : List PR :=
      match j.getObjVal? "res" with
      | .ok r =>
        if boolOf r "failed" then [PR.failed]
        else match r.getObjVal? "okhex" with
          | .ok (.str h) => [PR.ok (parsePromiseValue (unhex h.toList))]
          | _ => []
      | _ => []
    -- Running out of gas is not modeled: a receipt the runtime stopped for gas is the
    -- environment step `resolveFails` / a failed call, which changes nothing.
    if boolOf j "oog" then (s, Json.mkObj [("ok", toJson false), ("oog", toJson true)])
    else
      -- coverage label of a resolve callback: which branch of internal_ft_resolve_transfer ran
      let rcase : Json := match m, results with
        | .ft_resolve_transfer sn rc amt, [res] =>
          let f := refundOf s.accts rc amt res
          if f = 0 then
            Json.str (if unusedOf amt res = 0 then "unused=0" else "receiver-balance=0")
          else if (get s.accts sn).isSome then
            Json.str (if f < unusedOf amt res then "partial-refund" else "refund")
          else Json.str "sender-gone:burn"
        | _, _ => Json.null
      match exec E s ⟨strOf j "pred", natStr j "deposit", m, results⟩ with
      | none => (s, Json.mkObj [("ok", toJson false)])
      | some o =>
        (o.st, Json.mkObj [("ok", toJson true), ("rcase", rcase),
          ("ret", match o.ret with | some n => u128J n | none => Json.null),
          ("transfers", Json.arr (o.transfers.toArray.map fun (a, x) => Json.arr #[Json.str a, u128J x]))])

def runTrace (t : Json) : Json := Id.run do
  let byte := natStr t "byte"
  let storage0 := natStr t "storage0"
  let E : Env := { self := strOf t "self", minBal := natStr t "min", base := storage0 * byte,
                   entry := fun a => (61 + a.utf8ByteSize) * byte, cap := 2 ^ 127 }
  let mut s : St := ⟨[], 0, natStr t "near0"⟩
  let steps := arrOf t "steps"
  let mut i := 0
  let mut outSteps : Array Json := #[]
  let mut outObs : Array Json := #[]
  for o in arrOf t "obs" do
    let h := natStr o "h"
    while i < steps.size && natStr steps[i]! "h" ≤ h do
      let (s', r) := replayStep E s steps[i]!
      s := s'
      outSteps := outSteps.push r
      i := i + 1
    outObs := outObs.push (obsJson h s storage0)
  while i < steps.size do
    let (s', r) := replayStep E s steps[i]!
    s := s'
    outSteps := outSteps.push r
    i := i + 1
  return Json.mkObj [("id", (t.getObjVal? "id").toOption.getD Json.null),
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
