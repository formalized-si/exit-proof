/-
  poolmodel: runs the Lean model of the staking pool on JSON traces.
  stdin: one trace per line (schema in ../README section of REPORT.md / harness);
  stdout: one line per trace {"id", "results": [MOBS_init, MOBS_step1, ...]}.
-/
import Lean.Data.Json
import StakingPool.World

open Lean StakingPool

def DESER : String := "Failed to deserialize input from JSON."

def u128Of (j : Json) : Except String Nat :=
  match j with
  | .str s => match s.toNat? with
    | some n => if n ≤ U128_MAX then .ok n else .error DESER
    | none => .error DESER
  | _ => .error DESER

def getU128 (j : Json) (k : String) : Except String Nat := do
  let v ← (j.getObjVal? k).mapError (fun _ => DESER)
  u128Of v

def getFee (j : Json) : Except String Fee := do
  let n ← (j.getObjValAs? Nat "numerator").mapError (fun _ => DESER)
  let d ← (j.getObjValAs? Nat "denominator").mapError (fun _ => DESER)
  if n ≥ 2^32 || d ≥ 2^32 then throw DESER
  return ⟨n, d⟩

def parseMethod (name : String) (args : Json) : Except String Method :=
  match name with
  | "ping" => .ok .ping
  | "deposit" => .ok .deposit
  | "deposit_and_stake" => .ok .depositAndStake
  | "withdraw_all" => .ok .withdrawAll
  | "withdraw" => Method.withdraw <$> getU128 args "amount"
  | "stake_all" => .ok .stakeAll
  | "stake" => Method.stake <$> getU128 args "amount"
  | "unstake_all" => .ok .unstakeAll
  | "unstake" => Method.unstake <$> getU128 args "amount"
  | "update_staking_key" =>
    Method.updateStakingKey <$> (args.getObjValAs? String "stake_public_key").mapError (fun _ => DESER)
  | "update_reward_fee_fraction" => do
    let f ← (args.getObjVal? "reward_fee_fraction").mapError (fun _ => DESER)
    Method.updateFee <$> getFee f
  | "vote" => do
    let a ← (args.getObjValAs? String "voting_account_id").mapError (fun _ => DESER)
    let b ← (args.getObjValAs? Bool "is_vote").mapError (fun _ => DESER)
    return Method.vote a b
  | "pause_staking" => .ok .pauseStaking
  | "resume_staking" => .ok .resumeStaking
  | "on_stake_action" => .ok .onStakeAction
  | "new" => .ok .reinit
  | _ => .error "MethodNotFound"

def nat (n : Nat) : Json := toJson n
def str (s : String) : Json := Json.str s
def u128 (n : Nat) : Json := Json.str (toString n)

def accJson (a : Account) : Json :=
  Json.mkObj [("unstaked", u128 a.unstaked), ("stake_shares", u128 a.stakeShares),
    ("unstaked_available_epoch_height", nat a.availEpoch)]

def feeJson (f : Fee) : Json := Json.mkObj [("numerator", nat f.num), ("denominator", nat f.den)]

def stateJson (c : Contract) : Json :=
  Json.mkObj [
    ("owner_id", str c.owner), ("stake_public_key", str c.key),
    ("last_epoch_height", nat c.lastEpoch), ("last_total_balance", u128 c.ltb),
    ("total_stake_shares", u128 c.ts), ("total_staked_balance", u128 c.s),
    ("reward_fee_fraction", feeJson c.fee), ("paused", Json.bool c.paused),
    ("accounts", Json.mkObj ((storedIds c).map fun k => (k, accJson (c.get k))))]

def viewsJson (c : Contract) (epoch : Nat) (ids : List String) : Json :=
  Json.mkObj (ids.map fun id =>
    match viewAccount c epoch id with
    | .ok (u, st, w) => (id, Json.mkObj [("unstaked_balance", u128 u), ("staked_balance", u128 st),
        ("can_withdraw", Json.bool w)])
    | .error e => (id, Json.mkObj [("error", str e)]))

/-- ids and epoch of the views the simulator took for this observation -/
def obsViewIds (obs : Json) : List String :=
  match obs.getObjVal? "views" with
  | .ok (.obj kvs) => kvs.toList.map (·.1)
  | _ => []

def obsEpoch (obs : Json) (dflt : Nat) : Nat :=
  match obs.getObjVal? "env" with
  | .ok envj => (envj.getObjValAs? Nat "epoch").toOption.getD dflt
  | _ => dflt

def mobs (ok : Bool) (err : Option String) (eff : Eff) (c : Contract) (obs : Json) (epoch : Nat)
    (extra : List (String × Json) := []) : Json :=
  let vEpoch := obsEpoch obs epoch
  Json.mkObj ([
    ("ok", Json.bool ok),
    ("err", match err with | some e => str e | none => Json.null),
    ("transfer", u128 eff.transfer),
    ("stake", match eff.stake with | some s => u128 s | none => Json.null),
    ("reward", u128 eff.reward),
    ("state", stateJson c),
    ("views", viewsJson c vEpoch (obsViewIds obs)),
    ("total_staked_view", u128 c.s),
    ("num_accounts", nat (storedIds c).length)] ++ extra)

def runTrace (t : Json) : Except String Json := do
  let id := t.getObjValD "id"
  let vks ← (t.getObjValAs? (Array String) "valid_keys")
  let vk : String → Bool := fun k => vks.contains k
  let self := (t.getObjValAs? String "self").toOption.getD "pool.near"
  let ini ← t.getObjVal? "init"
  let pred ← ini.getObjValAs? String "pred"
  let owner ← ini.getObjValAs? String "owner"
  let key ← ini.getObjValAs? String "key"
  let fee ← (ini.getObjVal? "fee") >>= getFee
  let epoch ← ini.getObjValAs? Nat "epoch"
  let bal ← getU128 ini "balance"
  let lck ← getU128 ini "locked"
  let iobs := ini.getObjValD "sim"
  let env : Env := { self := self, pred := pred, epoch := epoch, balance := bal, locked := lck, deposit := 0 }
  match init vk env owner key fee with
  | .error e =>
    let dummy : Contract := Contract.mk owner key epoch 0 0 0 fee Accts.empty false
    return Json.mkObj [("id", id), ("results", Json.arr #[mobs false (some e) {} dummy iobs epoch])]
  | .ok (c0, eff0) =>
    let steps ← t.getObjValAs? (Array Json) "steps"
    let mut out : Array Json := #[mobs true none eff0 c0 iobs epoch]
    -- the World of StakingPool/World.lean, with the simulator's balances plugged in
    let mut w : World := World.init c0 epoch bal
    for st in steps do
      let obs := st.getObjValD "sim"
      let kind ← st.getObjValAs? String "kind"
      if kind == "call" then
        let pred ← st.getObjValAs? String "pred"
        let mname ← st.getObjValAs? String "method"
        let args := st.getObjValD "args"
        let dep ← getU128 st "deposit"
        let ep ← st.getObjValAs? Nat "epoch"
        let bal ← getU128 st "balance"
        let lck ← getU128 st "locked"
        while w.epoch < ep do
          w := w.advance
        -- the protocol's moves since the last call (income / rebalance steps)
        w := { w with liquid := bal - dep, locked := lck }
        let pua := Json.mkObj [("locked", u128 lck),
          ("bound", u128 (maxWin w.hist w.epoch + (w.liquid + w.locked - w.c.ltb))),
          ("ok", Json.bool (decide (PUA w))), ("cons", Json.bool (decide (w.c.ltb ≤ w.liquid + w.locked)))]
        let env := w.env self pred dep
        match parseMethod mname args with
        | .error e => out := out.push (mobs false (some e) {} w.c obs ep [("pua", pua)])
        | .ok m =>
          match exec vk w.c env m with
          | .ok (c', eff) =>
            w := w.afterCall dep c' eff
            out := out.push (mobs true none eff c' obs ep [("pua", pua)])
          | .error e => out := out.push (mobs false (some e) {} w.c obs ep [("pua", pua)])
      else
        let ep := obsEpoch obs w.epoch
        while w.epoch < ep do
          w := w.advance
        out := out.push (mobs true none {} w.c obs w.epoch)
    return Json.mkObj [("id", id), ("results", Json.arr out)]

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := line.trimAscii.toString
  if l.isEmpty then loop stdin stdout else
  match Json.parse l >>= runTrace with
  | .ok j => stdout.putStrLn j.compress
  | .error e => stdout.putStrLn (Json.mkObj [("error", Json.str e)]).compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
