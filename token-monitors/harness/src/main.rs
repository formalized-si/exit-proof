//! ftmon: observer for the model-free property monitors of NEP-141 tokens.
//!
//! Deploys a token wasm on near-contract-sim (nearcore runtime), initializes it as a config file
//! says (init call, optional setup calls, extra accounts and stubs), and runs random multi-account
//! traces through the standard interface only. It records what an outside observer sees: the
//! views `ft_total_supply` and `ft_balance_of` of every watched account after every block, and
//! every receipt the token executed. It makes no judgement: `monitors/monitors.py` checks the
//! properties on these records. Nothing here depends on the token's storage layout, error texts,
//! log format or library version.
//!
//! Usage:
//!   ftmon try <token.wasm> <config.json>                         init + setup; prints what happened
//!   ftmon run <token.wasm> <config.json> <seed> <start> <count>  traces as JSON lines on stdout
//!
//! The config format is described in CONFIG.md (the wrapper scripts validate it before this
//! program reads it).
//!
//! A trace is a list of rounds. A round submits one operation ("single": the exact monitors
//! apply) or several at once with held settlements ("batch"/"funding": the aggregate monitors
//! apply) and then produces blocks until nothing is pending.

use base64::Engine;
use near_contract_sim::prelude::*;
use near_contract_sim::{ExecutionStatus, Fault, ReceiptOutcome, Receipts, Reply, Stub};
use serde_json::{Value, json};

const USERS: [&str; 5] = [
    "owner.near",
    "alice.near",
    "bob.near",
    "c1.near",
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.near",
];
const RECVS: [&str; 2] = ["recv1.near", "recv2.near"];
const GHOST: &str = "ghost.near";
const EVIL: &str = "evil.near";

/// A contract that makes the token's `ft_resolve_transfer` the `promise_then` callback of its own
/// failing promise, with arguments it chooses.
fn evil_wat(token: &str, resolve: &str) -> String {
    format!(
        r#"(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "current_account_id" (func $current_account_id (param i64)))
  (import "env" "promise_create" (func $promise_create (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $promise_then (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_return" (func $promise_return (param i64)))
  (memory (export "memory") 1)
  (data (i32.const 0) "{token}")
  (data (i32.const 80) "{resolve}")
  (data (i32.const 112) "nope")
  (func (export "attack")
    (local $p1 i64) (local $inlen i64) (local $melen i64)
    (call $input (i64.const 0))
    (local.set $inlen (call $register_len (i64.const 0)))
    (call $read_register (i64.const 0) (i64.const 512))
    (call $current_account_id (i64.const 1))
    (local.set $melen (call $register_len (i64.const 1)))
    (call $read_register (i64.const 1) (i64.const 256))
    (local.set $p1 (call $promise_create (local.get $melen) (i64.const 256) (i64.const 4) (i64.const 112)
      (i64.const 0) (i64.const 0) (i64.const 128) (i64.const 5000000000000)))
    (call $promise_return (call $promise_then (local.get $p1) (i64.const {len}) (i64.const 0) (i64.const {rlen})
      (i64.const 80) (local.get $inlen) (i64.const 512) (i64.const 128) (i64.const 20000000000000)))))"#,
        token = token,
        len = token.len(),
        resolve = resolve,
        rlen = resolve.len()
    )
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
    fn upto(&mut self, n: u128) -> u128 {
        let r = (self.next() as u128) << 64 | self.next() as u128;
        if n == 0 {
            0
        } else if n == u128::MAX {
            r
        } else {
            r % (n + 1)
        }
    }
}

fn near(n: u128) -> u128 {
    n * 1_000_000_000_000_000_000_000_000
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[derive(Clone)]
struct CallSpec {
    caller: String,
    receiver: String,
    method: String,
    args: Vec<u8>,
    deposit: u128,
    gas_tgas: Option<u64>,
    may_fail: bool,
}

struct Cfg {
    token: String,
    wasm: Vec<u8>,
    token_near: u128,
    accounts: Vec<String>,
    init: Option<CallSpec>,
    setup: Vec<CallSpec>,
    track: Vec<String>,
    /// The account that hands out tokens in the funding round. Not given in the config: the user
    /// account with the largest balance after the set-up (`check_world` fills it in).
    funder: String,
    funder_given: bool,
    stubs: Vec<(String, Vec<(String, Value)>)>,
    timestamp_ns: Option<u64>,
    /// Optional `transfer_memos`: memos the traces attach to transfers (always to a transfer sent to the
    /// token account itself). Empty by default.
    memos: Vec<String>,
    /// Optional `resolve_method`: the name of the token's settlement callback when it is not
    /// `ft_resolve_transfer`. The holds, the stranger's calls and the monitors then use that name.
    resolve: String,
}

fn call_spec(v: &Value, token: &str) -> CallSpec {
    let args = match (&v["args_base64"], &v["args"]) {
        (Value::String(b), _) => base64::engine::general_purpose::STANDARD.decode(b).expect("args_base64 is not base64"),
        (_, Value::String(s)) => s.as_bytes().to_vec(),
        (_, Value::Null) => b"{}".to_vec(),
        (_, other) => serde_json::to_vec(other).unwrap(),
    };
    CallSpec {
        caller: v["caller"].as_str().unwrap_or(token).to_string(),
        receiver: v["receiver"].as_str().unwrap_or(token).to_string(),
        method: v["method"].as_str().expect("call needs a method").to_string(),
        args,
        deposit: v["deposit"].as_str().map(|s| s.parse().expect("deposit")).unwrap_or(0),
        gas_tgas: v["gas_tgas"].as_u64(),
        may_fail: v["may_fail"].as_bool().unwrap_or(false),
    }
}

fn read_cfg(wasm_path: &str, path: &str) -> Cfg {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let v: Value = serde_json::from_str(&text).unwrap_or_else(|e| panic!("{path}: {e}"));
    let token = v["token_account"].as_str().unwrap_or("token.near").to_string();
    let wasm = std::fs::read(wasm_path).unwrap_or_else(|e| panic!("{wasm_path}: {e}"));
    let strs = |x: &Value| -> Vec<String> {
        x.as_array().map(|a| a.iter().filter_map(|s| s.as_str().map(String::from)).collect()).unwrap_or_default()
    };
    let stubs = v["stubs"]
        .as_array()
        .map(|a| {
            a.iter()
                .map(|s| {
                    let ms = s["methods"].as_object().map(|o| o.iter().map(|(k, r)| (k.clone(), r.clone())).collect()).unwrap_or_default();
                    (s["account"].as_str().expect("stub account").to_string(), ms)
                })
                .collect()
        })
        .unwrap_or_default();
    Cfg {
        init: if v["init"].is_object() { Some(call_spec(&v["init"], &token)) } else { None },
        setup: v["setup"].as_array().map(|a| a.iter().map(|c| call_spec(c, &token)).collect()).unwrap_or_default(),
        accounts: strs(&v["accounts"]),
        track: strs(&v["track"]),
        funder: v["funder"].as_str().unwrap_or("").to_string(),
        funder_given: v["funder"].is_string(),
        token_near: v["token_near"].as_u64().unwrap_or(50) as u128,
        timestamp_ns: v["timestamp_ns"].as_u64(),
        memos: strs(&v["transfer_memos"]),
        resolve: v["resolve_method"].as_str().unwrap_or("ft_resolve_transfer").to_string(),
        stubs,
        wasm,
        token,
    }
}

fn do_call(sim: &mut Sim, c: &CallSpec) -> near_contract_sim::TxOutcome {
    let mut tx = sim
        .call(c.caller.as_str(), c.receiver.as_str(), &c.method)
        .args(c.args.clone())
        .deposit(Balance::from_yoctonear(c.deposit));
    if let Some(g) = c.gas_tgas {
        tx = tx.gas(Gas::from_teragas(g));
    }
    tx.transact()
}

fn failure_text(o: &near_contract_sim::TxOutcome) -> String {
    o.failure().map(|f| format!("{f:?}")).unwrap_or_else(|| "no failure reported".into())
}

fn outcome_json(c: &CallSpec, o: &near_contract_sim::TxOutcome) -> Value {
    json!({
        "caller": c.caller, "receiver": c.receiver, "method": c.method,
        "args": String::from_utf8_lossy(&c.args), "deposit": c.deposit.to_string(),
        "ok": o.is_success(), "may_fail": c.may_fail,
        "failure": o.failure().map(|f| format!("{f:?}")),
        "value": o.value().map(|v| String::from_utf8_lossy(v).to_string()),
        "logs": o.all_logs(),
        "receipts": o.receipts.iter().map(|r| json!({
            "pred": r.predecessor_id.as_str(), "recv": r.receiver_id.as_str(), "method": r.method_names.first(),
            "ok": r.is_success(), "status": status_text(r)})).collect::<Vec<_>>(),
    })
}

/// The world: accounts, the token deployed and set up. The second value is the log of the init
/// and setup calls.
fn build_world(cfg: &Cfg) -> Result<(Sim, Vec<Value>), (String, Vec<Value>)> {
    let mut sim = Sim::new();
    if let Some(ns) = cfg.timestamp_ns {
        sim.set_timestamp_ns(ns);
    }
    for u in USERS {
        sim.create_account(u, Balance::from_near(1_000_000));
    }
    for a in &cfg.accounts {
        if sim.account(a.as_str()).is_none() {
            sim.create_account(a.as_str(), Balance::from_near(1_000_000));
        }
    }
    let t = cfg.token.as_str();
    sim.create_account(t, Balance::from_near(cfg.token_near));
    sim.deploy(t, cfg.wasm.clone());
    for r in RECVS {
        sim.create_account(r, Balance::from_near(1_000));
        sim.deploy_stub(r, Stub::new().on("ft_on_transfer", Reply::json("0")).on("go", Reply::json("0")));
    }
    sim.create_account(EVIL, Balance::from_near(1_000));
    sim.deploy(EVIL, wat::parse_str(evil_wat(t, &cfg.resolve)).expect("evil.wat"));
    for (acc, methods) in &cfg.stubs {
        if sim.account(acc.as_str()).is_none() {
            sim.create_account(acc.as_str(), Balance::from_near(1_000_000));
        }
        let mut s = Stub::new();
        for (m, reply) in methods {
            s = s.on(m, Reply::json(reply.clone()));
        }
        sim.deploy_stub(acc.as_str(), s);
    }
    let mut log = vec![];
    if let Some(init) = &cfg.init {
        let o = do_call(&mut sim, init);
        log.push(outcome_json(init, &o));
        if !o.is_success() {
            return Err((format!("init {} failed: {}", init.method, failure_text(&o)), log));
        }
    }
    for c in &cfg.setup {
        let o = do_call(&mut sim, c);
        log.push(outcome_json(c, &o));
        if !o.is_success() && !c.may_fail {
            return Err((format!("setup call {} failed: {}", c.method, failure_text(&o)), log));
        }
    }
    Ok((sim, log))
}

/// Checks that the set-up left a world the monitors can judge, and decides who hands out tokens:
/// the supply view is a positive number, it equals the sum of the watched balances, and a user
/// account holds tokens. Returns a description of the world, or the reason it cannot be used.
fn check_world(sim: &Sim, cfg: &mut Cfg, ids: &[String]) -> Result<Value, String> {
    if sim.account(cfg.token.as_str()).is_none() {
        return Err(format!(
            "after the set-up the token account {} no longer exists: the contract deleted its own account \
             (some tokens do this when a call made by their init fails; look at the failed receipts above)",
            cfg.token
        ));
    }
    let obs = observe(sim, cfg, ids);
    let Some(supply) = obs["supply"].as_str().and_then(|s| s.parse::<u128>().ok()) else {
        return Err(format!(
            "after the set-up the view ft_total_supply did not return a number in a string (it returned {})",
            obs["supply"]
        ));
    };
    let mut holders: Vec<(String, u128)> =
        ids.iter().map(|a| (a.clone(), bal_of(&obs, a))).filter(|(_, b)| *b > 0).collect();
    holders.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    let sum = holders.iter().fold(0u128, |s, (_, b)| s.saturating_add(*b));
    let held = json!(holders.iter().map(|(a, b)| (a.clone(), json!(b.to_string()))).collect::<serde_json::Map<_, _>>());
    if supply == 0 {
        return Err("after the set-up ft_total_supply is 0: no tokens exist, so no transfer can succeed. \
                    Mint or distribute tokens in `init` or in `setup` calls"
            .into());
    }
    if sum != supply {
        return Err(format!(
            "after the set-up ft_total_supply is {supply} but the watched accounts hold {sum} ({held}). \
             List every account that receives tokens during init and setup under `track` (or `accounts`). \
             If all of them are listed, the token creates supply that no account holds, which violates P1"
        ));
    }
    // accounts that can act as the funder: the generator's users and the config's extra accounts
    let can_fund = |a: &str| USERS.contains(&a) || cfg.accounts.iter().any(|x| x == a);
    let from;
    if cfg.funder_given {
        from = "config";
        if bal_of(&obs, &cfg.funder) == 0 {
            return Err(format!("the funder {} holds no tokens after the set-up (holders: {held})", cfg.funder));
        }
    } else {
        from = "largest holder among the user accounts";
        match holders.iter().find(|(a, _)| can_fund(a)) {
            Some((a, _)) => cfg.funder = a.clone(),
            None => {
                return Err(format!(
                    "after the set-up no user account holds tokens (holders: {held}). Add a `setup` call that \
                     mints or transfers tokens to a user account such as owner.near, or name the `funder`"
                ));
            }
        }
    }
    Ok(json!({"supply": supply.to_string(), "holders": held, "funder": cfg.funder, "funder_from": from,
              "watched_accounts": ids}))
}

fn all_ids() -> Vec<&'static str> {
    let mut v: Vec<&str> = USERS.to_vec();
    v.extend(RECVS);
    v
}

fn targets<'a>(cfg: &'a Cfg) -> Vec<&'a str> {
    let mut v: Vec<&str> = all_ids();
    v.extend([GHOST, EVIL, cfg.token.as_str(), "Bad!Id", "x"]);
    v
}

/// Every account whose balance is watched: the closed world of the simulation.
fn tracked(cfg: &Cfg) -> Vec<String> {
    let mut v: Vec<String> = targets(cfg).iter().map(|s| s.to_string()).collect();
    for a in cfg.accounts.iter().chain(cfg.track.iter()) {
        if !v.contains(a) {
            v.push(a.clone());
        }
    }
    for (a, _) in &cfg.stubs {
        if !v.contains(a) {
            v.push(a.clone());
        }
    }
    v
}

fn view_str(sim: &Sim, token: &str, method: &str, args: Value) -> Option<String> {
    let r = sim.view(token, method, args);
    match r.value().and_then(|b| serde_json::from_slice::<Value>(b).ok()) {
        Some(Value::String(s)) => Some(s),
        _ => None,
    }
}

/// What an outside observer sees: the supply view and the balance view of every tracked account
/// (null where the view fails or does not return a string).
fn observe(sim: &Sim, cfg: &Cfg, ids: &[String]) -> Value {
    let supply = view_str(sim, &cfg.token, "ft_total_supply", json!({}));
    let mut bal = serde_json::Map::new();
    for a in ids {
        bal.insert(a.clone(), json!(view_str(sim, &cfg.token, "ft_balance_of", json!({"account_id": a}))));
    }
    json!({"h": sim.height(), "supply": supply, "bal": bal})
}

fn bal_of(obs: &Value, who: &str) -> u128 {
    obs["bal"][who].as_str().and_then(|s| s.parse().ok()).unwrap_or(0)
}

fn amount_for(rng: &mut Rng, bal: u128) -> u128 {
    match rng.below(100) {
        0..=4 => 0,
        5..=29 => bal,
        30..=37 => bal.saturating_add(1),
        38..=44 => 1,
        45..=47 => u128::MAX,
        _ => rng.upto(bal),
    }
}

/// What a receiver's `ft_on_transfer` does, with a machine-readable description for the monitors.
fn receiver_reply(rng: &mut Rng, token: &str, amount: u128) -> (Reply, Value) {
    let num = |rng: &mut Rng| -> u128 {
        match rng.below(7) {
            0 => 0,
            1 => amount,
            2 => amount.saturating_add(1),
            3 => amount / 2,
            4 => u128::MAX,
            _ => rng.upto(amount),
        }
    };
    let l42 = format!("\"{}7\"", "0".repeat(39));
    let l43 = format!("\"{}7\"", "0".repeat(40));
    match rng.below(100) {
        0..=39 => {
            let n = num(rng);
            (Reply::json(n.to_string()), json!({"kind": "num", "u": n.to_string()}))
        }
        40..=51 => {
            let gs: Vec<String> = [
                "{", "abc", "5", "\"-1\"", "\"+3\"", " \"7\" ", "\"\"", "null", "\"+\"",
                "\"340282366920938463463374607431768211456\"", "\"12a\"", "[\"40\"]", "\"0007\"", "",
                "\"\\u0035\"", "\"7\"\n", "\"7\" x",
            ]
            .iter()
            .map(|s| s.to_string())
            .chain([l42, l43])
            .collect();
            let g = rng.pick(&gs).clone();
            (Reply::bytes(g.as_bytes().to_vec()), json!({"kind": "bytes", "text": g}))
        }
        52..=63 => (Reply::panic("receiver refuses"), json!({"kind": "panic"})),
        64..=78 => {
            let ids = all_ids();
            let to = *rng.pick(&ids);
            let amt = amount_for(rng, amount);
            let n = num(rng);
            (
                Reply::call(token, "ft_transfer", json!({"receiver_id": to, "amount": amt.to_string()}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                json!({"kind": "nested_transfer", "to": to, "amt": amt.to_string(), "u": n.to_string()}),
            )
        }
        79..=86 => {
            let n = num(rng);
            let force = rng.chance(70);
            (
                Reply::call(token, "storage_unregister", json!({"force": force}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                json!({"kind": "nested_unregister", "force": force, "u": n.to_string()}),
            )
        }
        87..=91 => (Reply::json("0").at_limit(), json!({"kind": "limit"})),
        _ => {
            let n = num(rng);
            (Reply::json(n), json!({"kind": "json_number", "u": n.to_string()}))
        }
    }
}

/// Submits one random operation and returns its description.
fn submit_op(sim: &mut Sim, rng: &mut Rng, cfg: &Cfg, last: &Value, min: u128, batch: bool) -> Value {
    let token = cfg.token.as_str();
    let ids = all_ids();
    let who = *rng.pick(&ids);
    let bal = bal_of(last, who);
    let one = |rng: &mut Rng| -> u128 {
        if rng.chance(92) { 1 } else { *rng.pick(&[0u128, 2]) }
    };
    let roll = rng.below(100);
    let (tx, mut d): (CryptoHash, Value) = match roll {
        0..=26 => {
            let ts = targets(cfg);
            let to = *rng.pick(&ts);
            let amt = amount_for(rng, bal);
            let dep = one(rng);
            let mut args = json!({"receiver_id": to, "amount": amt.to_string()});
            if rng.chance(30) {
                args["memo"] = json!("hi");
            }
            if !cfg.memos.is_empty() && (to == token || rng.chance(25)) {
                args["memo"] = json!(rng.pick(&cfg.memos).clone());
            }
            let memo = args["memo"].clone();
            let h = sim.call(who, token, "ft_transfer").args_json(args).deposit(Balance::from_yoctonear(dep)).submit();
            let mut d = json!({"op": "ft_transfer", "caller": who, "to": to, "amount": amt.to_string(), "deposit": dep.to_string()});
            if !cfg.memos.is_empty() {
                d["memo"] = memo;
            }
            (h, d)
        }
        27..=61 => {
            let to = if rng.chance(82) {
                *rng.pick(&RECVS)
            } else {
                *rng.pick(&[USERS[1], USERS[2], GHOST, EVIL, "Bad!Id"])
            };
            let amt = amount_for(rng, bal);
            let dep = one(rng);
            let (reply, rd) = receiver_reply(rng, token, amt);
            let mut args = json!({"receiver_id": to, "amount": amt.to_string(), "msg": *rng.pick(&["", "m", "take-my-money"])});
            if rng.chance(20) {
                args["memo"] = json!("call memo");
            }
            if !cfg.memos.is_empty() && (to == token || rng.chance(25)) {
                args["memo"] = json!(rng.pick(&cfg.memos).clone());
            }
            let mut tx = sim.call(who, token, "ft_transfer_call").args_json(args).deposit(Balance::from_yoctonear(dep));
            let stub = RECVS.contains(&to);
            if stub {
                tx = tx.stub_reply(to, "ft_on_transfer", reply);
            }
            let mut fault = Value::Null;
            if batch && rng.chance(45) {
                let k = 1 + rng.below(4);
                tx = tx.inject(Receipts::callback(cfg.resolve.as_str()), Fault::Hold(k));
                fault = json!({"hold": k});
            } else if !batch && rng.chance(8) {
                let k = 1 + rng.below(3);
                tx = tx.inject(Receipts::callback(cfg.resolve.as_str()), Fault::Hold(k));
                fault = json!({"hold": k});
            } else if rng.chance(6) {
                tx = tx.inject(Receipts::callback(cfg.resolve.as_str()), Fault::PromiseFailed);
                fault = json!("promise_failed");
            }
            let h = tx.submit();
            (h, json!({"op": "ft_transfer_call", "caller": who, "to": to, "amount": amt.to_string(), "deposit": dep.to_string(),
                       "reply": if stub { rd } else { json!({"kind": "no_stub"}) }, "fault": fault}))
        }
        62..=69 => {
            let ts = targets(cfg);
            let acc: Option<&str> = match rng.below(5) {
                0 | 1 => None,
                2 => Some(GHOST),
                3 => Some(*rng.pick(&ts)),
                _ => Some(*rng.pick(&ids)),
            };
            let amt = *rng.pick(&[0, min.saturating_sub(1), min, min + 5, near(1)]);
            let mut args = match acc {
                Some(a) => json!({"account_id": a}),
                None => json!({}),
            };
            if rng.chance(30) {
                args["registration_only"] = json!(rng.chance(50));
            }
            let h = sim.call(who, token, "storage_deposit").args_json(args.clone()).deposit(Balance::from_yoctonear(amt)).submit();
            (h, json!({"op": "storage_deposit", "caller": who, "args": args, "deposit": amt.to_string()}))
        }
        70..=72 => {
            let args = match rng.below(3) {
                0 => json!({}),
                1 => json!({"amount": "0"}),
                _ => json!({"amount": "1"}),
            };
            let dep = one(rng);
            let h = sim.call(who, token, "storage_withdraw").args_json(args.clone()).deposit(Balance::from_yoctonear(dep)).submit();
            (h, json!({"op": "storage_withdraw", "caller": who, "args": args, "deposit": dep.to_string()}))
        }
        73..=78 => {
            let args = match rng.below(4) {
                0 => json!({}),
                1 => json!({"force": false}),
                _ => json!({"force": true}),
            };
            let dep = one(rng);
            let h = sim.call(who, token, "storage_unregister").args_json(args.clone()).deposit(Balance::from_yoctonear(dep)).submit();
            (h, json!({"op": "storage_unregister", "caller": who, "args": args, "deposit": dep.to_string()}))
        }
        79..=86 => {
            // ft_resolve_transfer from a stranger: four ways
            let victim = *rng.pick(&ids);
            let vb = bal_of(last, victim);
            let amt = if rng.chance(70) { vb } else { rng.upto(vb.saturating_add(1)) };
            let sender = if rng.chance(50) { EVIL } else { *rng.pick(&ids) };
            let args = json!({"sender_id": sender, "receiver_id": victim, "amount": amt.to_string()});
            let way = *rng.pick(&["foreign_callback", "foreign_callback", "direct", "contract", "token_key"]);
            let h = match way {
                "foreign_callback" => sim.call(who, EVIL, "attack").args_json(args.clone()).submit(),
                "direct" => sim.call(who, token, cfg.resolve.as_str()).args_json(args.clone()).submit(),
                "contract" => sim
                    .call(who, RECVS[1], "go")
                    .stub_reply(RECVS[1], "go", Reply::call(token, cfg.resolve.as_str(), args.clone()).then(Reply::json("0")))
                    .submit(),
                _ => sim.call(token, token, cfg.resolve.as_str()).args_json(args.clone()).submit(),
            };
            (h, json!({"op": "foreign_resolve", "caller": who, "way": way, "args": args}))
        }
        87..=91 => {
            let (meth, args) = *rng.pick(&[
                ("ft_total_supply", "{}"),
                ("ft_balance_of", "{\"account_id\":\"alice.near\"}"),
                ("ft_balance_of", "{\"account_id\":\"ghost.near\"}"),
                ("storage_balance_of", "{\"account_id\":\"bob.near\"}"),
                ("storage_balance_bounds", "{}"),
                ("ft_metadata", "{}"),
                ("no_such_method", "{}"),
            ]);
            let dep = *rng.pick(&[0u128, 1, 7]);
            let h = sim.call(who, token, meth).args(args.as_bytes().to_vec()).deposit(Balance::from_yoctonear(dep)).submit();
            (h, json!({"op": "other", "caller": who, "method": meth, "deposit": dep.to_string()}))
        }
        92 => match &cfg.init {
            Some(init) => {
                let h = sim.call(who, token, &init.method).args(init.args.clone()).submit();
                (h, json!({"op": "reinit", "caller": who, "method": init.method}))
            }
            None => {
                let h = sim.call(who, token, "new").args(b"{}".to_vec()).submit();
                (h, json!({"op": "reinit", "caller": who, "method": "new"}))
            }
        },
        93..=94 => {
            let amt = rng.upto(near(3));
            let h = sim.tx(who, token).transfer(Balance::from_yoctonear(amt)).submit();
            (h, json!({"op": "near_transfer", "caller": who, "amount": amt.to_string()}))
        }
        _ => {
            let (meth, args) = *rng.pick(&[
                ("ft_transfer", "{\"receiver_id\":\"bob.near\"}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":5}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\"+5\"}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\"-1\"}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\" 5\"}"),
                ("ft_transfer_call", "{\"receiver_id\":\"recv1.near\",\"amount\":\"1\"}"),
                ("storage_unregister", ""),
                ("storage_unregister", "{\"force\":\"yes\"}"),
                ("storage_deposit", "{\"account_id\":\"UPPER.near\"}"),
                ("storage_withdraw", "{\"amount\":0}"),
            ]);
            let h = sim.call(who, token, meth).args(args.as_bytes().to_vec()).deposit(Balance::from_yoctonear(1)).submit();
            (h, json!({"op": "raw", "caller": who, "method": meth, "args": args}))
        }
    };
    d["tx"] = json!(tx.to_string());
    d
}

fn status_text(r: &ReceiptOutcome) -> String {
    match r.failure() {
        Some(f) => format!("{f:?}"),
        None => "ok".into(),
    }
}

fn ret_of(r: &ReceiptOutcome) -> Value {
    match &r.status {
        ExecutionStatus::SuccessValue(v) if v.is_empty() => json!({"kind": "none"}),
        ExecutionStatus::SuccessValue(v) => match serde_json::from_slice::<Value>(v) {
            Ok(j) => json!({"kind": "value", "json": j}),
            Err(_) => json!({"kind": "bytes", "hex": hex(v)}),
        },
        ExecutionStatus::SuccessReceiptId(_) => json!({"kind": "promise"}),
        _ => Value::Null,
    }
}

/// The receipts of the blocks after `h0` that the monitors read: everything the token executed,
/// and the receiver-side calls of a transfer (`ft_on_transfer`, the stranger's `nope`/`go`/`attack`).
fn receipts_since(sim: &Sim, cfg: &Cfg, h0: u64) -> Vec<Value> {
    let mut out = vec![];
    for r in sim.receipts_in(h0 + 1..) {
        let meth = r.method_names.first().map(String::as_str);
        let on_token = r.receiver_id.as_str() == cfg.token;
        if !(on_token || matches!(meth, Some("ft_on_transfer") | Some("nope") | Some("go") | Some("attack"))) {
            continue;
        }
        let Some(meth) = meth else { continue };
        let args = r.args.first().map(|a| String::from_utf8_lossy(a).to_string()).unwrap_or_default();
        let oog = matches!(
            r.failure(),
            Some(near_contract_sim::Failure::OutOfGas) | Some(near_contract_sim::Failure::GasLimitExceeded)
        );
        out.push(json!({
            "h": r.block_height, "tx": r.tx.to_string(), "pred": r.predecessor_id.as_str(),
            "recv": r.receiver_id.as_str(), "method": meth, "args": args,
            "deposit": r.deposit.as_yoctonear().to_string(), "ok": r.is_success(), "oog": oog,
            "callback": r.is_callback(), "ret": ret_of(&r), "status": status_text(&r), "logs": r.logs,
        }));
    }
    out
}

fn settle(sim: &mut Sim, cfg: &Cfg, ids: &[String], blocks: &mut Vec<Value>) -> bool {
    let mut guard = 0;
    while !sim.is_idle() && guard < 200 {
        sim.step();
        blocks.push(observe(sim, cfg, ids));
        guard += 1;
    }
    sim.is_idle()
}

fn run_trace(base: &Sim, cfg: &Cfg, ids: &[String], min: u128, seed: u64, id: u64) -> Value {
    let mut sim = base.clone();
    let token = cfg.token.as_str();
    let mut rng = Rng(seed ^ (id.wrapping_mul(0x9E3779B97F4A7C15)) | 1);
    let init_obs = observe(&sim, cfg, ids);
    let mut last = init_obs.clone();
    let mut rounds = vec![];
    let mut settled = true;
    // funding round 1: most accounts register (themselves or by someone else)
    {
        let h0 = sim.height();
        let mut ops = vec![];
        for who in all_ids() {
            if who != cfg.funder && rng.chance(88) {
                let payer = if rng.chance(70) { who } else { "bob.near" };
                let dep = *rng.pick(&[min, min, min + 7, near(1)]);
                let h = sim.call(payer, token, "storage_deposit").args_json(json!({"account_id": who}))
                    .deposit(Balance::from_yoctonear(dep)).submit();
                ops.push(json!({"op": "storage_deposit", "caller": payer, "args": {"account_id": who}, "deposit": dep.to_string(), "tx": h.to_string()}));
            }
        }
        for extra in [EVIL, GHOST] {
            if rng.chance(50) {
                let h = sim.call("bob.near", token, "storage_deposit").args_json(json!({"account_id": extra}))
                    .deposit(Balance::from_yoctonear(min.max(1))).submit();
                ops.push(json!({"op": "storage_deposit", "caller": "bob.near", "args": {"account_id": extra}, "deposit": min.to_string(), "tx": h.to_string()}));
            }
        }
        let mut blocks = vec![];
        settled &= settle(&mut sim, cfg, ids, &mut blocks);
        if let Some(b) = blocks.last() {
            last = b.clone();
        }
        rounds.push(json!({"kind": "funding", "ops": ops, "blocks": blocks, "receipts": receipts_since(&sim, cfg, h0)}));
    }
    // funding round 2: the funder hands out tokens
    {
        let h0 = sim.height();
        let fb = bal_of(&last, &cfg.funder);
        let mut ops = vec![];
        for who in all_ids() {
            if who != cfg.funder && rng.chance(85) {
                let amt = rng.upto(fb / 9);
                let h = sim.call(cfg.funder.as_str(), token, "ft_transfer")
                    .args_json(json!({"receiver_id": who, "amount": amt.to_string()}))
                    .deposit(Balance::from_yoctonear(1)).submit();
                ops.push(json!({"op": "ft_transfer", "caller": cfg.funder, "to": who, "amount": amt.to_string(), "deposit": "1", "tx": h.to_string()}));
            }
        }
        let mut blocks = vec![];
        settled &= settle(&mut sim, cfg, ids, &mut blocks);
        if let Some(b) = blocks.last() {
            last = b.clone();
        }
        rounds.push(json!({"kind": "funding", "ops": ops, "blocks": blocks, "receipts": receipts_since(&sim, cfg, h0)}));
    }
    let n_rounds = 10 + rng.below(18);
    for _ in 0..n_rounds {
        let h0 = sim.height();
        let batch = rng.chance(28);
        let mut ops = vec![];
        let mut blocks = vec![];
        if batch {
            let k = 2 + rng.below(3);
            for _ in 0..k {
                ops.push(submit_op(&mut sim, &mut rng, cfg, &last, min, true));
                let gap = *rng.pick(&[0u64, 0, 1, 1, 2]);
                for _ in 0..gap {
                    sim.step();
                    blocks.push(observe(&sim, cfg, ids));
                }
            }
        } else {
            ops.push(submit_op(&mut sim, &mut rng, cfg, &last, min, false));
        }
        settled &= settle(&mut sim, cfg, ids, &mut blocks);
        if let Some(b) = blocks.last() {
            last = b.clone();
        }
        rounds.push(json!({"kind": if batch { "batch" } else { "single" }, "ops": ops, "blocks": blocks,
                           "receipts": receipts_since(&sim, cfg, h0)}));
    }
    let mut out = json!({"id": id, "token": token, "init": init_obs, "rounds": rounds, "settled": settled});
    if cfg.resolve != "ft_resolve_transfer" {
        out["resolve_method"] = json!(cfg.resolve);
    }
    out
}

fn storage_min(sim: &Sim, cfg: &Cfg) -> u128 {
    let v = sim.view(cfg.token.as_str(), "storage_balance_bounds", json!({}));
    v.value()
        .and_then(|b| serde_json::from_slice::<Value>(b).ok())
        .and_then(|j| j["min"].as_str().and_then(|s| s.parse().ok()))
        .unwrap_or(near(1) / 80)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: ftmon try <token.wasm> <config.json> | run <token.wasm> <config.json> <seed> <start> <count>";
    if args.len() < 4 || (args[1] == "run" && args.len() < 7) {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let mut cfg = read_cfg(&args[2], &args[3]);
    let ids = tracked(&cfg);
    match args[1].as_str() {
        "try" => {
            let out = match build_world(&cfg) {
                Ok((sim, log)) => {
                    let world = check_world(&sim, &mut cfg, &ids);
                    let t = cfg.token.as_str();
                    let view = |m: &str, a: Value| -> Value {
                        let r = sim.view(t, m, a);
                        match r.value() {
                            Some(b) => serde_json::from_slice::<Value>(b).unwrap_or(json!({"bytes": hex(b)})),
                            None => json!({"view_failed": format!("{:?}", r.failure())}),
                        }
                    };
                    let mut meta = view("ft_metadata", json!({}));
                    if let Some(o) = meta.as_object_mut() {
                        o.remove("icon");
                    }
                    let mut out = json!({
                        "ok": world.is_ok(), "stage": "world", "token": t, "calls": log,
                        "storage_min": storage_min(&sim, &cfg).to_string(),
                        "storage_balance_bounds": view("storage_balance_bounds", json!({})),
                        "ft_metadata": meta, "observation": observe(&sim, &cfg, &ids),
                    });
                    match world {
                        Ok(w) => out["world"] = w,
                        Err(e) => out["error"] = json!(e),
                    }
                    out
                }
                Err((e, log)) => json!({"ok": false, "stage": "calls", "error": e, "calls": log}),
            };
            println!("{}", serde_json::to_string_pretty(&out).unwrap());
        }
        "run" => {
            let seed: u64 = args[4].parse().expect("seed");
            let start: u64 = args[5].parse().expect("start");
            let count: u64 = args[6].parse().expect("count");
            let (sim, _) = build_world(&cfg).unwrap_or_else(|(e, _)| panic!("{e}"));
            if let Err(e) = check_world(&sim, &mut cfg, &ids) {
                eprintln!("{e}");
                std::process::exit(3);
            }
            let min = storage_min(&sim, &cfg);
            for id in start..start + count {
                let t = run_trace(&sim, &cfg, &ids, min, seed, id);
                println!("{}", serde_json::to_string(&t).unwrap());
            }
        }
        _ => eprintln!("{usage}"),
    }
}
