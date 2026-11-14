//! Certification harness for NEP-141/NEP-145 tokens built on near-contract-standards 5.29.0.
//!
//! Deploys the given wasm on near-contract-sim (nearcore runtime), initializes it with the
//! token's own `#[init]` call, and runs random multi-account traces that use only the standard's
//! interface. For every trace it records every receipt the token executed (in execution order,
//! with its arguments, deposit, promise result, return value, logs, and the receipts it sent)
//! and the token's observed state after every block. The Lean model (`ftmodel`) replays the
//! receipts; `scripts/compare.py` diffs the two and runs the property monitors.
//!
//! Usage:
//!   ftcert-gen probe  <wasm> <init_method> <init_args_json>
//!   ftcert-gen traces <wasm> <init_method> <init_args_json> <seed> <start> <count>

use near_contract_sim::prelude::*;
use near_contract_sim::{CryptoHash, ExecutionStatus, Fault, Receipts, ReceiptOutcome, Reply, Stub};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap, HashSet};

/// The token's account.
const TOKEN: &str = "token.near";
/// Plain accounts (no contract). `owner.near` is the account the init arguments should name.
/// Ids of different lengths: an `accounts` entry costs `60 + prefix + len` bytes; the last one
/// has the maximum length, 64, i.e. exactly the measured storage minimum.
const USERS: [&str; 5] = [
    "owner.near",
    "alice.near",
    "bob.near",
    "c1.near",
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.near",
];
/// Receiver contracts: stubs whose `ft_on_transfer` reply each transaction scripts.
const RECVS: [&str; 2] = ["recv1.near", "recv2.near"];
/// May get registered by others, but no NEAR account exists.
const GHOST: &str = "ghost.near";
/// A contract that makes the token's `ft_resolve_transfer` the `promise_then` callback of its
/// own failing promise, with arguments it chooses: the attack on a resolver whose caller check
/// is missing. `attack(args)`: p1 = self.nope() (no such method: Failed),
/// p2 = p1.then(token.ft_resolve_transfer(args)).
const EVIL: &str = "evil.near";
/// An account id the probe registers to locate the `accounts` map in storage.
const PROBE: &str = "prefix-probe.near";

fn evil_wat() -> String {
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
  (data (i32.const 80) "ft_resolve_transfer")
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
    (call $promise_return (call $promise_then (local.get $p1) (i64.const {len}) (i64.const 0) (i64.const 19)
      (i64.const 80) (local.get $inlen) (i64.const 512) (i64.const 128) (i64.const 20000000000000)))))"#,
        token = TOKEN,
        len = TOKEN.len()
    )
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
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

fn wasm_bytes(path: &str) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|e| panic!("{path}: {e}"))
}

fn sha256_hex(b: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    hex(&Sha256::digest(b))
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

struct World {
    sim: Sim,
    /// Storage key prefix of the `accounts` LookupMap.
    prefix: Vec<u8>,
    /// What the token reports as `storage_balance_bounds().min` (used only to pick inputs).
    min: u128,
}

fn build_world(wasm: &[u8], init_method: &str, init_args: &str) -> Result<World, String> {
    let mut sim = Sim::new();
    for u in USERS {
        sim.create_account(u, Balance::from_near(1_000_000));
    }
    sim.create_account(TOKEN, Balance::from_near(50));
    sim.deploy(TOKEN, wasm.to_vec());
    let init = sim.call(TOKEN, TOKEN, init_method).args(init_args.as_bytes().to_vec()).transact();
    if !init.is_success() {
        return Err(format!("init {init_method}({init_args}) failed: {:?}", init.failure()));
    }
    for r in RECVS {
        sim.create_account(r, Balance::from_near(1_000));
        sim.deploy_stub(r, Stub::new().on("ft_on_transfer", Reply::json("0")));
    }
    sim.create_account(EVIL, Balance::from_near(1_000));
    sim.deploy(EVIL, wat::parse_str(evil_wat()).expect("evil.wat"));
    let prefix = locate_map(&sim)?;
    let min = view_u128_field(&sim, "storage_balance_bounds", "min").unwrap_or(near(1) / 100);
    Ok(World { sim, prefix, min })
}

/// Finds the `accounts` LookupMap prefix: registers a probe account on a copy of the world and
/// looks for the new key `prefix ++ u32le(len) ++ id` holding a 16-byte value.
fn locate_map(sim: &Sim) -> Result<Vec<u8>, String> {
    let before: HashSet<Vec<u8>> = sim.view_state(TOKEN, b"").into_iter().map(|(k, _)| k).collect();
    let mut s2 = sim.clone();
    let o = s2
        .call("alice.near", TOKEN, "storage_deposit")
        .args_json(json!({"account_id": PROBE}))
        .deposit(Balance::from_near(1))
        .transact();
    let mut suffix = (PROBE.len() as u32).to_le_bytes().to_vec();
    suffix.extend_from_slice(PROBE.as_bytes());
    for (k, v) in s2.view_state(TOKEN, b"") {
        if !before.contains(&k) && k.ends_with(&suffix) && v.len() == 16 {
            return Ok(k[..k.len() - suffix.len()].to_vec());
        }
    }
    // fall back to the owner's entry written by init
    let owner = USERS[0];
    let mut suffix = (owner.len() as u32).to_le_bytes().to_vec();
    suffix.extend_from_slice(owner.as_bytes());
    for (k, v) in sim.view_state(TOKEN, b"") {
        if k.ends_with(&suffix) && v.len() == 16 {
            return Ok(k[..k.len() - suffix.len()].to_vec());
        }
    }
    Err(format!("accounts map not located (probe storage_deposit ok={})", o.is_success()))
}

fn view_u128_field(sim: &Sim, method: &str, field: &str) -> Option<u128> {
    let v = sim.view(TOKEN, method, json!({}));
    let j: Value = serde_json::from_slice(v.value()?).ok()?;
    j[field].as_str()?.parse().ok()
}

/// The token's `accounts` map, read from storage: key = prefix ++ borsh(String).
fn map(sim: &Sim, prefix: &[u8]) -> BTreeMap<String, u128> {
    let mut m = BTreeMap::new();
    for (k, v) in sim.view_state(TOKEN, prefix) {
        let rest = &k[prefix.len()..];
        if rest.len() < 4 || v.len() != 16 {
            continue;
        }
        let n = u32::from_le_bytes([rest[0], rest[1], rest[2], rest[3]]) as usize;
        if rest.len() != 4 + n {
            continue;
        }
        let id = String::from_utf8_lossy(&rest[4..]).to_string();
        let mut b = [0u8; 16];
        b.copy_from_slice(&v);
        m.insert(id, u128::from_le_bytes(b));
    }
    m
}

fn observe(sim: &Sim, prefix: &[u8]) -> Value {
    let sv = sim.view(TOKEN, "ft_total_supply", json!({}));
    let supply: Value = match sv.value().and_then(|b| serde_json::from_slice::<Value>(b).ok()) {
        Some(Value::String(s)) => json!(s),
        other => json!(format!("view failed: {other:?} {:?}", sv.failure())),
    };
    let acc = sim.account(TOKEN).expect("token account");
    let m: BTreeMap<String, String> = map(sim, prefix).into_iter().map(|(k, v)| (k, v.to_string())).collect();
    json!({
        "h": sim.height(),
        "supply": supply,
        "near": sim.balance(TOKEN).as_yoctonear().to_string(),
        "storage": acc.storage_usage,
        "map": m,
    })
}

fn all_ids() -> Vec<&'static str> {
    let mut v: Vec<&str> = USERS.to_vec();
    v.extend(RECVS);
    v
}

fn targets() -> Vec<&'static str> {
    let mut v = all_ids();
    v.extend([GHOST, EVIL, TOKEN, "Bad!Id", "x"]);
    v
}

/// An amount relative to a balance: the edges and a random middle.
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

/// What a receiver's `ft_on_transfer` does; also returned as a label for the trace.
fn receiver_reply(rng: &mut Rng, amount: u128, holder: &str) -> (Reply, String) {
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
    let l42 = format!("\"{}7\"", "0".repeat(39)); // 42 bytes: at the length limit
    let l43 = format!("\"{}7\"", "0".repeat(40)); // 43 bytes: over it
    match rng.below(100) {
        0..=29 => {
            let n = num(rng);
            (Reply::json(n.to_string()), format!("json {n}"))
        }
        30..=46 => {
            let gs: Vec<String> = [
                "{", "abc", "5", "\"-1\"", "\"+3\"", " \"7\" ", "\"\"", "null", "\"+\"",
                "\"340282366920938463463374607431768211456\"", "\"12a\"", "[\"40\"]", "\"0007\"", "",
                "\"\\u0035\"", "\"\\u00352\"", "\"+340282366920938463463374607431768211455\"", "\"7\"\n",
                "\"7\" x", "\"\\n7\"",
            ]
            .iter()
            .map(|s| s.to_string())
            .chain([l42, l43])
            .collect();
            let g = rng.pick(&gs).clone();
            (Reply::bytes(g.as_bytes().to_vec()), format!("bytes {g:?}"))
        }
        47..=56 => (Reply::panic("receiver refuses"), "panic".into()),
        57..=71 => {
            // move tokens away before the settlement runs
            let to = *rng.pick(&all_ids());
            let amt = amount_for(rng, amount);
            let n = num(rng);
            (
                Reply::call(TOKEN, "ft_transfer", json!({"receiver_id": to, "amount": amt.to_string()}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("ft_transfer {amt} to {to} by {holder}, then json {n}"),
            )
        }
        72..=80 => {
            let n = num(rng);
            let force = rng.chance(70);
            (
                Reply::call(TOKEN, "storage_unregister", json!({"force": force}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("storage_unregister force={force} by {holder}, then json {n}"),
            )
        }
        81..=86 => (Reply::json("0").at_limit(), "json 0 padded to the return limit".into()),
        _ => {
            let n = num(rng);
            (Reply::json(n), format!("json number {n}"))
        }
    }
}

/// Submits one random operation; returns its label.
fn submit_op(sim: &mut Sim, rng: &mut Rng, w_prefix: &[u8], min: u128, init_method: &str, init_args: &str) -> String {
    let m = map(sim, w_prefix);
    let ids = all_ids();
    let who = *rng.pick(&ids);
    let bal = m.get(who).copied().unwrap_or(0);
    let one = |rng: &mut Rng| -> u128 {
        if rng.chance(92) { 1 } else { *rng.pick(&[0u128, 2]) }
    };
    let roll = rng.below(100);
    match roll {
        0..=21 => {
            let to = *rng.pick(&targets());
            let amt = amount_for(rng, bal);
            let d = one(rng);
            let mut args = json!({"receiver_id": to, "amount": amt.to_string()});
            if rng.chance(30) {
                args["memo"] = json!("hi");
            }
            sim.call(who, TOKEN, "ft_transfer").args_json(args).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} ft_transfer {amt} to {to} (deposit {d})")
        }
        22..=47 => {
            let to = if rng.chance(80) {
                *rng.pick(&RECVS)
            } else {
                *rng.pick(&[USERS[1], USERS[2], GHOST, EVIL, "Bad!Id"])
            };
            let amt = amount_for(rng, bal);
            let d = one(rng);
            let (reply, label) = receiver_reply(rng, amt, to);
            let mut args = json!({"receiver_id": to, "amount": amt.to_string(), "msg": *rng.pick(&["", "m", "take-my-money"])});
            if rng.chance(20) {
                args["memo"] = json!("call memo");
            }
            let mut tx = sim.call(who, TOKEN, "ft_transfer_call").args_json(args).deposit(Balance::from_yoctonear(d));
            if RECVS.contains(&to) {
                tx = tx.stub_reply(to, "ft_on_transfer", reply);
            }
            let mut extra = String::new();
            if rng.chance(20) {
                let k = 1 + rng.below(4);
                tx = tx.inject(Receipts::callback("ft_resolve_transfer"), Fault::Hold(k));
                extra = format!(", settlement held {k} blocks");
            } else if rng.chance(6) {
                tx = tx.inject(Receipts::callback("ft_resolve_transfer"), Fault::PromiseFailed);
                extra = ", ft_on_transfer forced to fail".into();
            }
            tx.submit();
            format!("{who} ft_transfer_call {amt} to {to} (deposit {d}); receiver: {label}{extra}")
        }
        48..=57 => {
            let acc: Option<&str> = match rng.below(5) {
                0 | 1 => None,
                2 => Some(GHOST),
                3 => Some(*rng.pick(&targets())),
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
            sim.call(who, TOKEN, "storage_deposit").args_json(args.clone()).deposit(Balance::from_yoctonear(amt)).submit();
            format!("{who} storage_deposit {args} with {amt}")
        }
        58..=60 => {
            let args = match rng.below(3) {
                0 => json!({}),
                1 => json!({"amount": "0"}),
                _ => json!({"amount": "1"}),
            };
            let d = one(rng);
            sim.call(who, TOKEN, "storage_withdraw").args_json(args.clone()).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} storage_withdraw {args} (deposit {d})")
        }
        61..=68 => {
            let args = match rng.below(4) {
                0 => json!({}),
                1 => json!({"force": false}),
                _ => json!({"force": true}),
            };
            let d = one(rng);
            sim.call(who, TOKEN, "storage_unregister").args_json(args.clone()).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} storage_unregister {args} (deposit {d})")
        }
        69 | 70 => {
            let victim = *rng.pick(&ids);
            let vb = m.get(victim).copied().unwrap_or(0);
            let amt = if rng.chance(70) { vb } else { rng.upto(vb.saturating_add(1)) };
            let sender = if rng.chance(50) { EVIL } else { *rng.pick(&ids) };
            sim.call(who, EVIL, "attack")
                .args_json(json!({"sender_id": sender, "receiver_id": victim, "amount": amt.to_string()}))
                .submit();
            format!("{who} has evil.near run ft_resolve_transfer({sender}, {victim}, {amt}) as its callback")
        }
        71 | 72 => {
            let s = *rng.pick(&ids);
            let r = *rng.pick(&ids);
            let amt = m.get(r).copied().unwrap_or(0);
            let caller = who;
            sim.call(caller, TOKEN, "ft_resolve_transfer")
                .args_json(json!({"sender_id": s, "receiver_id": r, "amount": amt.to_string()}))
                .submit();
            format!("{caller} calls ft_resolve_transfer({s}, {r}, {amt}) directly")
        }
        73..=78 => {
            let (meth, args) = *rng.pick(&[
                ("ft_total_supply", "{}"),
                ("ft_total_supply", ""),
                ("ft_balance_of", "{\"account_id\":\"alice.near\"}"),
                ("ft_balance_of", "{\"account_id\":\"ghost.near\"}"),
                ("ft_balance_of", "{\"account_id\":\"Bad!Id\"}"),
                ("storage_balance_of", "{\"account_id\":\"bob.near\"}"),
                ("storage_balance_of", "{\"account_id\":\"ghost.near\"}"),
                ("storage_balance_bounds", "{}"),
                ("no_such_method", "{}"),
            ]);
            let d = *rng.pick(&[0u128, 1, 7]);
            sim.call(who, TOKEN, meth).args(args.as_bytes().to_vec()).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} calls {meth} as a transaction with {d}")
        }
        79 => {
            sim.call(who, TOKEN, init_method).args(init_args.as_bytes().to_vec()).submit();
            format!("{who} calls {init_method}() again")
        }
        80..=82 => {
            let amt = rng.upto(near(3));
            sim.tx(who, TOKEN).transfer(Balance::from_yoctonear(amt)).submit();
            format!("{who} sends {amt} yocto to the token")
        }
        _ => {
            let (meth, args) = *rng.pick(&[
                ("ft_transfer", "{\"receiver_id\":\"bob.near\"}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":5}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\"+5\"}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\"-1\"}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\" 5\"}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"memo\":7}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"extra\":1}"),
                ("ft_transfer_call", "{\"receiver_id\":\"recv1.near\",\"amount\":\"1\"}"),
                ("storage_unregister", ""),
                ("storage_unregister", "{\"force\":\"yes\"}"),
                ("storage_deposit", "{\"account_id\":\"UPPER.near\"}"),
                ("storage_withdraw", "{\"amount\":0}"),
            ]);
            sim.call(who, TOKEN, meth).args(args.as_bytes().to_vec()).deposit(Balance::from_yoctonear(1)).submit();
            format!("{who} {meth} raw args {args:?}")
        }
    }
}

fn status_text(r: &ReceiptOutcome) -> String {
    match r.failure() {
        Some(f) => format!("{f:?}"),
        None => "ok".into(),
    }
}

/// The promise result a callback read: the status of the same transaction's `ft_on_transfer`
/// (or evil.near's `nope`) receipt.
fn promise_result(r: &ReceiptOutcome, all: &[ReceiptOutcome]) -> Value {
    let on = all.iter().find(|x| {
        x.tx == r.tx && matches!(x.method_names.first().map(String::as_str), Some("ft_on_transfer") | Some("nope"))
    });
    match on {
        None => json!({"unknown": true}),
        Some(x) => match &x.status {
            ExecutionStatus::SuccessValue(v) => json!({"okhex": hex(v)}),
            ExecutionStatus::Failure(_) => json!({"failed": true}),
            _ => json!({"unknown": true}),
        },
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

struct Base {
    w: World,
    byte: u128,
}

fn run_trace(base: &Base, seed: u64, id: u64, init_method: &str, init_args: &str) -> Value {
    let mut sim = base.w.sim.clone();
    let prefix = &base.w.prefix;
    let min = base.w.min;
    let mut rng = Rng(seed ^ (id.wrapping_mul(0x9E3779B97F4A7C15)) | 1);
    let h0 = sim.height();
    let first = observe(&sim, prefix);
    let mut obs = vec![first.clone()];
    let mut ops = vec![];
    // funding prefix: most accounts register (themselves or by someone else), the owner hands
    // out tokens; part of the trace, replayed by the model like everything else
    for who in all_ids().into_iter().skip(1) {
        if rng.chance(85) {
            let payer = if rng.chance(70) { who } else { "bob.near" };
            let dep = *rng.pick(&[min, min, min + 7, near(1)]);
            sim.call(payer, TOKEN, "storage_deposit").args_json(json!({"account_id": who}))
                .deposit(Balance::from_yoctonear(dep)).submit();
            ops.push(format!("{payer} storage_deposit for {who} with {dep} (funding)"));
        }
    }
    for extra in [EVIL, GHOST] {
        if rng.chance(50) {
            sim.call("bob.near", TOKEN, "storage_deposit").args_json(json!({"account_id": extra}))
                .deposit(Balance::from_yoctonear(min)).submit();
            ops.push(format!("bob.near storage_deposit for {extra} (funding)"));
        }
    }
    while !sim.is_idle() {
        sim.step();
        obs.push(observe(&sim, prefix));
    }
    let ob = map(&sim, prefix).get(USERS[0]).copied().unwrap_or(0);
    let registered: Vec<String> = map(&sim, prefix).keys().cloned().collect();
    for who in registered.iter() {
        if who != USERS[0] && rng.chance(80) {
            let amt = rng.upto(ob / 8);
            sim.call(USERS[0], TOKEN, "ft_transfer").args_json(json!({"receiver_id": who, "amount": amt.to_string()}))
                .deposit(Balance::from_yoctonear(1)).submit();
            ops.push(format!("owner ft_transfer {amt} to {who} (funding)"));
        }
    }
    while !sim.is_idle() {
        sim.step();
        obs.push(observe(&sim, prefix));
    }
    let n_ops = 8 + rng.below(25);
    for _ in 0..n_ops {
        ops.push(submit_op(&mut sim, &mut rng, prefix, min, init_method, init_args));
        let gap = *rng.pick(&[0u64, 0, 1, 1, 1, 2, 3]);
        for _ in 0..gap {
            sim.step();
            obs.push(observe(&sim, prefix));
        }
    }
    let mut guard = 0;
    while !sim.is_idle() && guard < 200 {
        sim.step();
        obs.push(observe(&sim, prefix));
        guard += 1;
    }
    let all = sim.receipts_in(h0 + 1..);
    let by_id: HashMap<CryptoHash, &ReceiptOutcome> = all.iter().map(|r| (r.receipt_id, r)).collect();
    let mut steps = vec![];
    for r in &all {
        if r.receiver_id.as_str() != TOKEN {
            continue;
        }
        let deposit = r.deposit.as_yoctonear().to_string();
        if let Some(meth) = r.method_names.first() {
            let args = r.args.first().map(|a| String::from_utf8_lossy(a).to_string()).unwrap_or_default();
            let children: Vec<&&ReceiptOutcome> = r
                .receipt_ids
                .iter()
                .filter_map(|c| by_id.get(c))
                .filter(|c| c.predecessor_id.as_str() == TOKEN)
                .collect();
            let transfers: Vec<Value> = children
                .iter()
                .filter(|c| c.actions == ["Transfer"])
                .map(|c| json!([c.receiver_id.as_str(), c.deposit.as_yoctonear().to_string()]))
                .collect();
            let calls: Vec<Value> = children
                .iter()
                .filter(|c| c.actions.iter().any(|a| a == "FunctionCall"))
                .map(|c| {
                    json!({
                        "receiver": c.receiver_id.as_str(), "actions": c.actions,
                        "method": c.method_names.first(),
                        "args": c.args.first().map(|a| String::from_utf8_lossy(a).to_string()),
                        "gas": c.attached_gas.as_gas(), "deposit": c.deposit.as_yoctonear().to_string(),
                    })
                })
                .collect();
            let other_actions: Vec<Value> = children
                .iter()
                .filter(|c| c.actions != ["Transfer"] && !c.actions.iter().any(|a| a == "FunctionCall"))
                .map(|c| json!({"receiver": c.receiver_id.as_str(), "actions": c.actions}))
                .collect();
            let res = if meth == "ft_resolve_transfer" && r.is_callback() {
                promise_result(r, &all)
            } else {
                Value::Null
            };
            let oog = matches!(
                r.failure(),
                Some(near_contract_sim::Failure::OutOfGas) | Some(near_contract_sim::Failure::GasLimitExceeded)
            );
            steps.push(json!({
                "h": r.block_height, "k": "call", "tx": r.tx.to_string(), "rid": r.receipt_id.to_string(),
                "pred": r.predecessor_id.as_str(), "method": meth, "args": args, "deposit": deposit,
                "ok": r.is_success(), "oog": oog, "callback": r.is_callback(), "ret": ret_of(r),
                "res": res, "transfers": transfers, "calls": calls, "other_actions": other_actions,
                "children": r.receipt_ids.iter().map(|c| c.to_string()).collect::<Vec<_>>(),
                "logs": r.logs, "status": status_text(r), "gas_attached": r.attached_gas.as_gas(),
                "gas_burnt": r.gas_burnt.as_gas(),
            }));
        } else {
            steps.push(json!({
                "h": r.block_height, "k": "in", "pred": r.predecessor_id.as_str(), "deposit": deposit,
                "ok": r.is_success(), "refund": r.refund.map(|x| format!("{x:?}")), "actions": r.actions,
            }));
        }
    }
    // the receipts that call ft_on_transfer, for the receiver-behaviour statistics
    let on_status: Vec<Value> = all
        .iter()
        .filter(|r| r.method_names.first().map(String::as_str) == Some("ft_on_transfer"))
        .map(|r| json!({"receiver": r.receiver_id.as_str(), "ok": r.is_success()}))
        .collect();
    let init_map: BTreeMap<String, String> =
        serde_json::from_value(first["map"].clone()).unwrap_or_default();
    json!({
        "id": id, "self": TOKEN, "byte": base.byte.to_string(), "prefix_len": prefix.len(),
        "prefix_hex": hex(prefix), "init_method": init_method,
        "near0": first["near"], "storage0": first["storage"],
        "init": {"map": init_map, "supply": first["supply"]},
        "ops": ops, "steps": steps, "obs": obs, "on_transfer": on_status, "settled": sim.is_idle(),
    })
}

/// Deterministic checks of the settlement callback's caller check (P3) and re-init: each
/// foreign `ft_resolve_transfer` must fail and leave the state unchanged.
fn checks(w: &World) -> Value {
    let mut sim = w.sim.clone();
    let p = &w.prefix;
    let owner = USERS[0];
    for u in ["alice.near", "bob.near", RECVS[0]] {
        sim.call(u, TOKEN, "storage_deposit").args_json(json!({})).deposit(Balance::from_near(1)).transact();
    }
    sim.call("alice.near", TOKEN, "storage_deposit").args_json(json!({"account_id": EVIL}))
        .deposit(Balance::from_near(1)).transact();
    let ob = map(&sim, p).get(owner).copied().unwrap_or(0);
    sim.call(owner, TOKEN, "ft_transfer").args_json(json!({"receiver_id": "bob.near", "amount": (ob / 2).to_string()}))
        .deposit(Balance::from_yoctonear(1)).transact();
    let victim = "bob.near";
    let vb = map(&sim, p).get(victim).copied().unwrap_or(0);
    let args = json!({"sender_id": "alice.near", "receiver_id": victim, "amount": vb.to_string()});
    let mut out = serde_json::Map::new();
    let before = map(&sim, p);
    // 1. a user calls it directly
    let o = sim.call("alice.near", TOKEN, "ft_resolve_transfer").args_json(args.clone()).transact();
    out.insert("resolve_by_user".into(), json!(status_text_tx(o.failure())));
    // 2. another contract calls it
    sim.deploy_stub(RECVS[1], Stub::new().on("go", Reply::call(TOKEN, "ft_resolve_transfer", args.clone()).then(Reply::json("0"))));
    let o = sim.call("alice.near", RECVS[1], "go").transact();
    let r = o.receipts.iter().find(|r| r.method_names.first().map(String::as_str) == Some("ft_resolve_transfer"));
    out.insert("resolve_by_contract".into(), json!(r.map(status_text)));
    // 3. as another contract's promise_then callback with a Failed promise result
    let o = sim.call("alice.near", EVIL, "attack")
        .args_json(json!({"sender_id": EVIL, "receiver_id": victim, "amount": vb.to_string()})).transact();
    let r = o.receipts.iter().find(|r| r.method_names.first().map(String::as_str) == Some("ft_resolve_transfer"));
    out.insert("resolve_as_foreign_callback".into(), json!(r.map(|r| json!({
        "predecessor": r.predecessor_id.as_str(), "is_callback": r.is_callback(), "status": status_text(r)}))));
    // 4. a transaction signed with the token account's own key (no promise results)
    let o = sim.call(TOKEN, TOKEN, "ft_resolve_transfer").args_json(args.clone()).transact();
    out.insert("resolve_by_token_key".into(), json!(status_text_tx(o.failure())));
    let after = map(&sim, p);
    out.insert("balances_unchanged".into(), json!(before == after));
    out.insert("victim_balance_before_after".into(), json!([vb.to_string(), after.get(victim).copied().unwrap_or(0).to_string()]));
    Value::Object(out)
}

fn status_text_tx(f: Option<near_contract_sim::Failure>) -> String {
    match f {
        Some(f) => format!("{f:?}"),
        None => "ok".into(),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: ftcert-gen probe <wasm> <init_method> <init_args> | traces <wasm> <init_method> <init_args> <seed> <start> <count>";
    if args.len() < 5 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let wasm = wasm_bytes(&args[2]);
    let (init_method, init_args) = (args[3].as_str(), args[4].as_str());
    match args[1].as_str() {
        "probe" => {
            let out = match build_world(&wasm, init_method, init_args) {
                Ok(w) => {
                    let first = observe(&w.sim, &w.prefix);
                    let checks = checks(&w);
                    json!({
                        "ok": true, "wasm_sha256": sha256_hex(&wasm),
                        "wasm_sha256_base58": CryptoHash::hash_bytes(&wasm).to_string(),
                        "sim_code_hash": w.sim.account(TOKEN).unwrap().code_hash.to_string(),
                        "token": TOKEN, "prefix_hex": hex(&w.prefix), "storage_byte_cost": w.sim.storage_cost(1).as_yoctonear().to_string(),
                        "reported_storage_min": w.min.to_string(), "init_state": first, "checks": checks,
                    })
                }
                Err(e) => json!({"ok": false, "error": e, "wasm_sha256": sha256_hex(&wasm)}),
            };
            println!("{}", serde_json::to_string_pretty(&out).unwrap());
        }
        "traces" => {
            let seed: u64 = args[5].parse().unwrap();
            let start: u64 = args[6].parse().unwrap();
            let count: u64 = args[7].parse().unwrap();
            let w = build_world(&wasm, init_method, init_args).unwrap_or_else(|e| panic!("{e}"));
            let byte = w.sim.storage_cost(1).as_yoctonear();
            let base = Base { w, byte };
            for id in start..start + count {
                let t = run_trace(&base, seed, id, init_method, init_args);
                println!("{}", serde_json::to_string(&t).unwrap());
            }
        }
        _ => eprintln!("{usage}"),
    }
}
