//! Conformance harness for wrap.near: runs the exact deployed wasm (DL2f5xmZ…) on
//! near-contract-sim (nearcore 2.14.0 runtime) and records, per random trace, every receipt the
//! contract executed (in execution order) and the observed contract state after every block.
//! The Lean model (`wnearmodel`) replays the receipts; `compare.py` diffs the two.
//!
//! Usage:
//!   wnear-gen checks <wasm>                    deterministic checks (hash, private resolve, re-init, gas)
//!   wnear-gen traces <wasm> <seed> <start> <count>   one JSON trace per line on stdout

use near_contract_sim::prelude::*;
use near_contract_sim::{CryptoHash, ExecutionStatus, Fault, Receipts, ReceiptOutcome, Reply, Stub};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap};

const WRAP: &str = "wrap.near";
const DEPLOYED_HASH: &str = "DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1";
/// Plain accounts (no contract), ids of different lengths (the storage entry is 61 + len bytes).
const USERS: [&str; 4] = ["alice.near", "bob.near", "c1.near", "a-very-long-account-name-for-storage-tests.near"];
/// Receiver contracts: stubs whose `ft_on_transfer` reply each transaction scripts.
const RECVS: [&str; 2] = ["recv1.near", "recv2.near"];
/// Registered in wNEAR by others, but no NEAR account exists.
const GHOST: &str = "ghost.near";
/// A contract that makes wrap.near's `ft_resolve_transfer` the `promise_then` callback of its
/// own failing promise, with arguments it chooses: the SWEAT-class attack on a resolver whose
/// caller check is missing. `attack(args)`: p1 = self.nope() (no such method: Failed),
/// p2 = p1.then(wrap.near.ft_resolve_transfer(args)).
const EVIL: &str = "evil.near";
const EVIL_WAT: &str = r#"(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "current_account_id" (func $current_account_id (param i64)))
  (import "env" "promise_create" (func $promise_create (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $promise_then (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_return" (func $promise_return (param i64)))
  (memory (export "memory") 1)
  (data (i32.const 0) "wrap.near")
  (data (i32.const 16) "ft_resolve_transfer")
  (data (i32.const 48) "nope")
  (func (export "attack")
    (local $p1 i64) (local $inlen i64) (local $melen i64)
    (call $input (i64.const 0))
    (local.set $inlen (call $register_len (i64.const 0)))
    (call $read_register (i64.const 0) (i64.const 256))
    (call $current_account_id (i64.const 1))
    (local.set $melen (call $register_len (i64.const 1)))
    (call $read_register (i64.const 1) (i64.const 128))
    (local.set $p1 (call $promise_create (local.get $melen) (i64.const 128) (i64.const 4) (i64.const 48)
      (i64.const 0) (i64.const 0) (i64.const 64) (i64.const 5000000000000)))
    (call $promise_return (call $promise_then (local.get $p1) (i64.const 9) (i64.const 0) (i64.const 19)
      (i64.const 16) (local.get $inlen) (i64.const 256) (i64.const 64) (i64.const 20000000000000)))))"#;

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

fn world(wasm: &[u8]) -> Sim {
    world_with(wasm, DEPLOYED_HASH)
}

fn world_with(wasm: &[u8], expect: &str) -> Sim {
    let hash = CryptoHash::hash_bytes(wasm).to_string();
    assert_eq!(hash, expect, "wasm is not the expected code");
    let mut sim = Sim::new();
    for u in USERS {
        sim.create_account(u, Balance::from_near(1_000_000));
    }
    sim.deploy(WRAP, wasm.to_vec());
    sim.call(WRAP, WRAP, "new").transact().assert_success();
    for r in RECVS {
        sim.create_account(r, Balance::from_near(1_000));
        sim.deploy_stub(r, Stub::new().on("ft_on_transfer", Reply::json("0")));
    }
    sim.create_account(EVIL, Balance::from_near(1_000));
    sim.deploy(EVIL, wat::parse_str(EVIL_WAT).expect("evil.wat"));
    let code_hash = sim.account(WRAP).expect("wrap.near").code_hash.to_string();
    assert_eq!(code_hash, expect, "deployed code hash in the sim");
    sim
}

fn min_bal(sim: &Sim) -> u128 {
    let v: Value = sim.view(WRAP, "storage_balance_bounds", json!({})).json();
    v["min"].as_str().unwrap().parse().unwrap()
}

/// The contract's `accounts` LookupMap, read from storage: key = b"a" ++ borsh(String).
fn map(sim: &Sim) -> BTreeMap<String, u128> {
    let mut m = BTreeMap::new();
    for (k, v) in sim.view_state(WRAP, b"a") {
        if k.len() < 5 {
            continue;
        }
        let n = u32::from_le_bytes([k[1], k[2], k[3], k[4]]) as usize;
        if k.len() != 5 + n || v.len() != 16 {
            continue;
        }
        let id = String::from_utf8_lossy(&k[5..]).to_string();
        let mut b = [0u8; 16];
        b.copy_from_slice(&v);
        m.insert(id, u128::from_le_bytes(b));
    }
    m
}

fn observe(sim: &Sim) -> Value {
    let supply: String = sim.view(WRAP, "ft_total_supply", json!({})).json();
    let acc = sim.account(WRAP).expect("wrap.near");
    let m: BTreeMap<String, String> = map(sim).into_iter().map(|(k, v)| (k, v.to_string())).collect();
    json!({
        "h": sim.height(),
        "supply": supply,
        "near": sim.balance(WRAP).as_yoctonear().to_string(),
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
    v.extend([GHOST, WRAP, "Bad!Id", "x"]);
    v
}

/// An amount relative to a balance: the edges and a random middle.
fn amount_for(rng: &mut Rng, bal: u128) -> u128 {
    match rng.below(100) {
        0..=4 => 0,
        5..=34 => bal,
        35..=42 => bal + 1,
        43..=49 => 1,
        50..=52 => u128::MAX,
        _ => rng.upto(bal),
    }
}

/// What a receiver's `ft_on_transfer` does; also returned as a label for the trace.
fn receiver_reply(rng: &mut Rng, amount: u128, holder: &str) -> (Reply, String) {
    let num = |rng: &mut Rng| -> u128 {
        match rng.below(7) {
            0 => 0,
            1 => amount,
            2 => amount + 1,
            3 => amount / 2,
            4 => u128::MAX,
            _ => rng.upto(amount),
        }
    };
    match rng.below(100) {
        0..=34 => {
            let n = num(rng);
            (Reply::json(n.to_string()), format!("json {n}"))
        }
        35..=49 => {
            let g = *rng.pick(&[
                "{", "abc", "5", "\"-1\"", "\"+3\"", " \"7\" ", "\"\"", "null",
                "\"340282366920938463463374607431768211456\"", "\"12a\"", "[\"40\"]", "\"0007\"", "",
            ]);
            (Reply::bytes(g.as_bytes().to_vec()), format!("bytes {g:?}"))
        }
        50..=59 => (Reply::panic("receiver refuses"), "panic".into()),
        60..=74 => {
            // move tokens away before the resolve runs
            let to = *rng.pick(&all_ids());
            let amt = amount_for(rng, amount);
            let n = num(rng);
            (
                Reply::call(WRAP, "ft_transfer", json!({"receiver_id": to, "amount": amt.to_string()}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("ft_transfer {amt} to {to}, then json {n}"),
            )
        }
        75..=81 => {
            let n = num(rng);
            let force = rng.chance(70);
            (
                Reply::call(WRAP, "storage_unregister", json!({"force": force}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("storage_unregister force={force}, then json {n}"),
            )
        }
        82..=93 => {
            let amt = amount_for(rng, amount);
            let n = num(rng);
            (
                Reply::call(WRAP, "near_withdraw", json!({"amount": amt.to_string()}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("near_withdraw {amt} by {holder}, then json {n}"),
            )
        }
        94..=96 => (Reply::json("0").at_limit(), "json 0 padded to the return limit".into()),
        _ => {
            let n = num(rng);
            (Reply::json(n), format!("json number {n}"))
        }
    }
}

/// Submits one random operation; returns its label.
fn submit_op(sim: &mut Sim, rng: &mut Rng, min: u128) -> String {
    let m = map(sim);
    let ids = all_ids();
    let who = *rng.pick(&ids);
    let bal = m.get(who).copied().unwrap_or(0);
    let one = |rng: &mut Rng| -> u128 {
        if rng.chance(92) { 1 } else { *rng.pick(&[0u128, 2]) }
    };
    let roll = rng.below(100);
    match roll {
        0..=17 => {
            let amt = match rng.below(8) {
                0 => 0,
                1 => min - 1,
                2 => min,
                3 => min + 1,
                4 => 1,
                _ => near(rng.upto(20)) + rng.upto(near(1)),
            };
            sim.call(who, WRAP, "near_deposit").deposit(Balance::from_yoctonear(amt)).submit();
            format!("{who} near_deposit {amt}")
        }
        18..=29 => {
            let amt = amount_for(rng, bal);
            let d = one(rng);
            sim.call(who, WRAP, "near_withdraw")
                .args_json(json!({"amount": amt.to_string()}))
                .deposit(Balance::from_yoctonear(d))
                .submit();
            format!("{who} near_withdraw {amt} (deposit {d})")
        }
        30..=39 => {
            let to = *rng.pick(&targets());
            let amt = amount_for(rng, bal);
            let d = one(rng);
            let mut args = json!({"receiver_id": to, "amount": amt.to_string()});
            if rng.chance(30) {
                args["memo"] = json!("hi");
            }
            sim.call(who, WRAP, "ft_transfer").args_json(args).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} ft_transfer {amt} to {to} (deposit {d})")
        }
        40..=61 => {
            let to = if rng.chance(75) { *rng.pick(&RECVS) } else { *rng.pick(&targets()) };
            let amt = amount_for(rng, bal);
            let d = one(rng);
            let (reply, label) = receiver_reply(rng, amt, to);
            let mut tx = sim
                .call(who, WRAP, "ft_transfer_call")
                .args_json(json!({"receiver_id": to, "amount": amt.to_string(), "msg": "m"}))
                .deposit(Balance::from_yoctonear(d));
            if RECVS.contains(&to) {
                tx = tx.stub_reply(to, "ft_on_transfer", reply);
            }
            let mut extra = String::new();
            if rng.chance(20) {
                let k = 1 + rng.below(4);
                tx = tx.inject(Receipts::callback("ft_resolve_transfer"), Fault::Hold(k));
                extra = format!(", resolve held {k} blocks");
            } else if rng.chance(6) {
                tx = tx.inject(Receipts::callback("ft_resolve_transfer"), Fault::PromiseFailed);
                extra = ", ft_on_transfer forced to fail".into();
            }
            tx.submit();
            format!("{who} ft_transfer_call {amt} to {to} (deposit {d}); receiver: {label}{extra}")
        }
        62..=70 => {
            let acc: Option<&str> = match rng.below(5) {
                0 | 1 => None,
                2 => Some(GHOST),
                3 => Some(*rng.pick(&targets())),
                _ => Some(*rng.pick(&ids)),
            };
            let amt = *rng.pick(&[0, min - 1, min, min + 5, near(1)]);
            let args = match acc {
                Some(a) => json!({"account_id": a}),
                None => json!({}),
            };
            sim.call(who, WRAP, "storage_deposit").args_json(args).deposit(Balance::from_yoctonear(amt)).submit();
            format!("{who} storage_deposit for {acc:?} with {amt}")
        }
        71..=73 => {
            let args = match rng.below(3) {
                0 => json!({}),
                1 => json!({"amount": "0"}),
                _ => json!({"amount": "1"}),
            };
            let d = one(rng);
            sim.call(who, WRAP, "storage_withdraw").args_json(args.clone()).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} storage_withdraw {args} (deposit {d})")
        }
        74..=80 => {
            let args = match rng.below(4) {
                0 => json!({}),
                1 => json!({"force": false}),
                _ => json!({"force": true}),
            };
            let d = one(rng);
            sim.call(who, WRAP, "storage_unregister").args_json(args.clone()).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} storage_unregister {args} (deposit {d})")
        }
        81 | 82 => {
            let victim = *rng.pick(&ids);
            let vb = m.get(victim).copied().unwrap_or(0);
            let amt = if rng.chance(70) { vb } else { rng.upto(vb + 1) };
            sim.call(who, EVIL, "attack")
                .args_json(json!({"sender_id": EVIL, "receiver_id": victim, "amount": amt.to_string()}))
                .submit();
            format!("{who} has evil.near run ft_resolve_transfer({EVIL}, {victim}, {amt}) as its callback")
        }
        83 => {
            let s = *rng.pick(&ids);
            let r = *rng.pick(&ids);
            let amt = rng.upto(near(5));
            sim.call(who, WRAP, "ft_resolve_transfer")
                .args_json(json!({"sender_id": s, "receiver_id": r, "amount": amt.to_string()}))
                .submit();
            format!("{who} calls ft_resolve_transfer({s}, {r}, {amt}) directly")
        }
        84..=87 => {
            let (meth, args) = *rng.pick(&[
                ("ft_total_supply", "{}"),
                ("ft_balance_of", "{\"account_id\":\"alice.near\"}"),
                ("ft_balance_of", "{\"account_id\":\"Bad!Id\"}"),
                ("storage_balance_of", "{\"account_id\":\"bob.near\"}"),
                ("storage_balance_bounds", "{}"),
                ("ft_metadata", "{}"),
                ("storage_minimum_balance", "{}"),
                ("ft_on_transfer", "{}"),
            ]);
            let d = *rng.pick(&[0u128, 1, 7]);
            sim.call(who, WRAP, meth).args(args.as_bytes().to_vec()).deposit(Balance::from_yoctonear(d)).submit();
            format!("{who} calls {meth} as a transaction with {d}")
        }
        88 => {
            sim.call(who, WRAP, "new").submit();
            format!("{who} calls new()")
        }
        89..=91 => {
            let amt = rng.upto(near(3));
            sim.tx(who, WRAP).transfer(Balance::from_yoctonear(amt)).submit();
            format!("{who} sends {amt} yocto to wrap.near")
        }
        _ => {
            let (meth, args) = *rng.pick(&[
                ("near_withdraw", "{\"amount\":\"abc\"}"),
                ("near_withdraw", "{\"amount\":\"+5\"}"),
                ("near_withdraw", "{\"amount\":\"-1\"}"),
                ("near_withdraw", "{\"amount\":5}"),
                ("near_withdraw", "{\"amount\":\" 5\"}"),
                ("near_withdraw", "{}"),
                ("ft_transfer", "{\"receiver_id\":\"bob.near\"}"),
                ("ft_transfer_call", "{\"receiver_id\":\"recv1.near\",\"amount\":\"1\"}"),
                ("storage_unregister", ""),
                ("storage_unregister", "{\"force\":\"yes\"}"),
                ("storage_deposit", "{\"account_id\":\"UPPER.near\"}"),
                ("near_withdraw", "{\"amount\":\"0\",\"extra\":1}"),
            ]);
            sim.call(who, WRAP, meth).args(args.as_bytes().to_vec()).deposit(Balance::from_yoctonear(1)).submit();
            format!("{who} {meth} raw args {args:?}")
        }
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn status_text(r: &ReceiptOutcome) -> String {
    match r.failure() {
        Some(f) => format!("{f:?}"),
        None => "ok".into(),
    }
}

/// The promise result a resolve callback read: the status of the same transaction's
/// `ft_on_transfer` receipt.
fn promise_result(r: &ReceiptOutcome, all: &[ReceiptOutcome]) -> Value {
    let on = all
        .iter()
        .find(|x| {
            x.tx == r.tx
                && matches!(x.method_names.first().map(String::as_str), Some("ft_on_transfer") | Some("nope"))
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

fn run_trace(base: &Sim, seed: u64, id: u64, min: u128, byte: u128) -> Value {
    let mut sim = base.clone();
    let mut rng = Rng(seed ^ (id.wrapping_mul(0x9E3779B97F4A7C15)) | 1);
    let h0 = sim.height();
    let first = observe(&sim);
    let mut obs = vec![first.clone()];
    let mut ops = vec![];
    // funding prefix: most accounts wrap some NEAR (registering on the way), in one block
    for who in all_ids() {
        if rng.chance(85) {
            let amt = min + near(rng.upto(30)) + rng.upto(near(1));
            sim.call(who, WRAP, "near_deposit").deposit(Balance::from_yoctonear(amt)).submit();
            ops.push(format!("{who} near_deposit {amt} (funding)"));
        }
    }
    if rng.chance(50) {
        sim.call("bob.near", WRAP, "storage_deposit").args_json(json!({"account_id": EVIL}))
            .deposit(Balance::from_yoctonear(min)).submit();
        ops.push("bob.near storage_deposit for evil.near (funding)".into());
    }
    if rng.chance(50) {
        sim.call("bob.near", WRAP, "storage_deposit").args_json(json!({"account_id": GHOST}))
            .deposit(Balance::from_yoctonear(min)).submit();
        ops.push("bob.near storage_deposit for ghost.near (funding)".into());
    }
    while !sim.is_idle() {
        sim.step();
        obs.push(observe(&sim));
    }
    let n_ops = 8 + rng.below(25);
    for _ in 0..n_ops {
        ops.push(submit_op(&mut sim, &mut rng, min));
        let gap = *rng.pick(&[0u64, 0, 1, 1, 1, 2, 3]);
        for _ in 0..gap {
            sim.step();
            obs.push(observe(&sim));
        }
    }
    let mut guard = 0;
    while !sim.is_idle() && guard < 200 {
        sim.step();
        obs.push(observe(&sim));
        guard += 1;
    }
    let all = sim.receipts_in(h0 + 1..);
    let by_id: HashMap<CryptoHash, &ReceiptOutcome> = all.iter().map(|r| (r.receipt_id, r)).collect();
    let mut steps = vec![];
    let mut resolve_gas = vec![];
    for r in &all {
        if r.receiver_id.as_str() != WRAP {
            continue;
        }
        let deposit = r.deposit.as_yoctonear().to_string();
        if let Some(meth) = r.method_names.first() {
            let args = r.args.first().map(|a| String::from_utf8_lossy(a).to_string()).unwrap_or_default();
            let transfers: Vec<Value> = r
                .receipt_ids
                .iter()
                .filter_map(|c| by_id.get(c))
                .filter(|c| c.predecessor_id.as_str() == WRAP && c.actions == ["Transfer"])
                .map(|c| json!([c.receiver_id.as_str(), c.deposit.as_yoctonear().to_string()]))
                .collect();
            let res = if meth == "ft_resolve_transfer" && r.predecessor_id.as_str() == WRAP {
                resolve_gas.push(json!([r.attached_gas.as_gas(), r.gas_burnt.as_gas(), r.is_success()]));
                promise_result(r, &all)
            } else if meth == "ft_resolve_transfer" && r.predecessor_id.as_str() == EVIL {
                promise_result(r, &all)
            } else {
                Value::Null
            };
            let oog = matches!(
                r.failure(),
                Some(near_contract_sim::Failure::OutOfGas) | Some(near_contract_sim::Failure::GasLimitExceeded)
            );
            steps.push(json!({
                "h": r.block_height, "k": "call", "tx": r.tx.to_string(), "pred": r.predecessor_id.as_str(), "method": meth,
                "args": args, "deposit": deposit, "ok": r.is_success(), "oog": oog,
                "ret": r.value().map(|v| String::from_utf8_lossy(v).to_string()),
                "res": res, "transfers": transfers, "status": status_text(r),
            }));
        } else {
            steps.push(json!({
                "h": r.block_height, "k": "in", "pred": r.predecessor_id.as_str(), "deposit": deposit,
                "ok": r.is_success(), "refund": r.refund.map(|x| format!("{x:?}")), "actions": r.actions,
            }));
        }
    }
    // every action of every receipt wrap.near sent (it must only ever be Transfer / FunctionCall)
    let mut wrap_actions: BTreeMap<String, u64> = BTreeMap::new();
    for r in &all {
        if r.predecessor_id.as_str() == WRAP {
            for a in &r.actions {
                *wrap_actions.entry(a.clone()).or_default() += 1;
            }
        }
    }
    json!({
        "id": id, "self": WRAP, "min": min.to_string(), "byte": byte.to_string(), "wrap_actions": wrap_actions,
        "near0": first["near"], "storage0": first["storage"], "ops": ops,
        "steps": steps, "obs": obs, "resolve_gas": resolve_gas, "settled": sim.is_idle(),
    })
}

fn checks(wasm: &[u8]) {
    let mut sim = world(wasm);
    let min = min_bal(&sim);
    let mut out = BTreeMap::new();
    out.insert("wasm_sha256_base58", json!(CryptoHash::hash_bytes(wasm).to_string()));
    out.insert("sim_code_hash", json!(sim.account(WRAP).unwrap().code_hash.to_string()));
    out.insert("min_storage_balance", json!(min.to_string()));
    out.insert("storage_byte_cost", json!(sim.storage_cost(1).as_yoctonear().to_string()));
    // fund alice and bob with wNEAR, recv1 registered
    for (u, d) in [("alice.near", near(10)), ("bob.near", near(5)), ("recv1.near", near(1))] {
        sim.call(u, WRAP, "near_deposit").deposit(Balance::from_yoctonear(d)).transact().assert_success();
    }
    // 1. ft_resolve_transfer from a foreign account fails, from a user and from a contract
    let direct = sim
        .call("alice.near", WRAP, "ft_resolve_transfer")
        .args_json(json!({"sender_id": "alice.near", "receiver_id": "bob.near", "amount": "1000"}))
        .transact();
    out.insert("resolve_by_user", json!(format!("{:?}", direct.failure())));
    sim.deploy_stub(
        "recv2.near",
        Stub::new().on(
            "go",
            Reply::call(WRAP, "ft_resolve_transfer", json!({"sender_id": "recv2.near", "receiver_id": "bob.near", "amount": "1000"}))
                .then(Reply::json("0")),
        ),
    );
    let via = sim.call("alice.near", "recv2.near", "go").transact();
    let inner = via.receipts.iter().find(|r| r.method_names.first().map(String::as_str) == Some("ft_resolve_transfer"));
    out.insert("resolve_by_contract", json!(inner.map(|r| format!("{:?}", r.failure()))));
    sim.call("alice.near", WRAP, "storage_deposit").args_json(json!({"account_id": EVIL}))
        .deposit(Balance::from_yoctonear(min)).transact().assert_success();
    let bob_before = map(&sim)["bob.near"];
    let atk = sim
        .call("alice.near", EVIL, "attack")
        .args_json(json!({"sender_id": EVIL, "receiver_id": "bob.near", "amount": bob_before.to_string()}))
        .transact();
    let cb = atk.receipts.iter().find(|r| r.method_names.first().map(String::as_str) == Some("ft_resolve_transfer"));
    out.insert("resolve_as_foreign_callback", json!(cb.map(|r| json!({
        "receiver": r.receiver_id.as_str(), "predecessor": r.predecessor_id.as_str(),
        "is_callback": r.is_callback(), "status": status_text(r)}))));
    out.insert("bob_balance_before_after_attack", json!([bob_before.to_string(), map(&sim)["bob.near"].to_string()]));
    let m = map(&sim);
    out.insert("balances_after_foreign_resolves", json!(m.iter().map(|(k, v)| (k.clone(), v.to_string())).collect::<BTreeMap<_, _>>()));
    // 2. re-initialisation fails
    let again = sim.call("alice.near", WRAP, "new").transact();
    out.insert("new_again", json!(format!("{:?}", again.failure())));
    // 3. gas of the resolve callback (5 Tgas attached), normal and padded replies
    for (label, reply) in [
        ("json 0", Reply::json("0")),
        ("json 0 at return limit", Reply::json("0").at_limit()),
        ("panic", Reply::panic("no")),
    ] {
        let mut s2 = sim.clone();
        let o = s2
            .call("alice.near", WRAP, "ft_transfer_call")
            .args_json(json!({"receiver_id": "recv1.near", "amount": "1000", "msg": ""}))
            .deposit(Balance::from_yoctonear(1))
            .stub_reply("recv1.near", "ft_on_transfer", reply)
            .transact();
        let r = o.receipts.iter().find(|r| r.method_names.first().map(String::as_str) == Some("ft_resolve_transfer"));
        out.insert(
            Box::leak(format!("resolve_gas[{label}]").into_boxed_str()),
            json!(r.map(|r| json!({"attached": r.attached_gas.as_gas(), "burnt": r.gas_burnt.as_gas(), "status": status_text(r)}))),
        );
        out.insert(
            Box::leak(format!("alice_after[{label}]").into_boxed_str()),
            json!(map(&s2).get("alice.near").map(|v| v.to_string())),
        );
    }
    // 4. full exit: withdraw everything, unregister, NEAR received
    let mut s3 = sim.clone();
    let b = map(&s3)["alice.near"];
    let w = s3
        .call("alice.near", WRAP, "near_withdraw")
        .args_json(json!({"amount": b.to_string()}))
        .deposit(Balance::from_yoctonear(1))
        .transact();
    let u = s3.call("alice.near", WRAP, "storage_unregister").args_json(json!({})).deposit(Balance::from_yoctonear(1)).transact();
    out.insert("exit_gas_burnt", json!({"near_withdraw": w.gas_burnt().as_gas(), "storage_unregister": u.gas_burnt().as_gas()}));
    out.insert("exit_withdraw", json!({"ok": w.is_success(), "near_to_alice": w.effects().near_paid(WRAP, "alice.near").as_yoctonear().to_string(), "balance": b.to_string()}));
    out.insert("exit_unregister", json!({"ok": u.is_success(), "near_to_alice": u.effects().near_paid(WRAP, "alice.near").as_yoctonear().to_string(), "registered_after": map(&s3).contains_key("alice.near")}));
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
}

/// The pre-upgrade code (9kQaNisc…, wrap.near from its creation to height 35,438,885): no
/// model, only the invariant after every block — supply = sum of the stored balances, and
/// NEAR ≥ supply + accounts × minimum storage balance + the stake at init.
fn old_invariant(wasm: &[u8], seed: u64, count: u64) {
    let base = world_with(wasm, "9kQaNiscuPh69vRs1GyzfnkEjpUPGLjJhT6RaJBQyG7p");
    let min: u128 = base.view(WRAP, "storage_minimum_balance", json!({})).json::<String>().parse().unwrap();
    let byte = base.storage_cost(1).as_yoctonear();
    let stake0 = base.account(WRAP).unwrap().storage_usage as u128 * byte;
    let (mut blocks, mut bad, mut ok_calls, mut calls) = (0u64, vec![], Counter::default(), Counter::default());
    for id in 0..count {
        let mut sim = base.clone();
        let mut rng = Rng(seed ^ (id.wrapping_mul(0x9E3779B97F4A7C15)) | 1);
        let h0 = sim.height();
        let check = |sim: &Sim, blocks: &mut u64, bad: &mut Vec<String>| {
            *blocks += 1;
            let m = map(sim);
            let sum: u128 = m.values().sum();
            let supply: u128 = sim.view(WRAP, "ft_total_supply", json!({})).json::<String>().parse().unwrap();
            let nearb = sim.balance(WRAP).as_yoctonear();
            if sum != supply {
                bad.push(format!("trace {id} h{}: supply {supply} != sum {sum}", sim.height()));
            }
            if supply + m.len() as u128 * min + stake0 > nearb {
                bad.push(format!("trace {id} h{}: insolvent: supply {supply} + {} x min + stake0 > {nearb}", sim.height(), m.len()));
            }
        };
        // the old code registers only through storage_deposit of exactly the minimum
        for who in all_ids() {
            if rng.chance(90) {
                sim.call(who, WRAP, "storage_deposit").args_json(json!({}))
                    .deposit(Balance::from_yoctonear(min)).submit();
            }
        }
        while !sim.is_idle() { sim.step(); check(&sim, &mut blocks, &mut bad); }
        for who in all_ids() {
            if rng.chance(85) {
                let amt = near(rng.upto(30)) + rng.upto(near(1)) + 1;
                sim.call(who, WRAP, "near_deposit").deposit(Balance::from_yoctonear(amt)).submit();
            }
        }
        while !sim.is_idle() { sim.step(); check(&sim, &mut blocks, &mut bad); }
        for _ in 0..(8 + rng.below(25)) {
            let who = *rng.pick(&all_ids());
            match rng.below(10) {
                0 => {
                    sim.call(who, WRAP, "storage_withdraw").args_json(json!({"amount": min.to_string()}))
                        .deposit(Balance::from_yoctonear(1)).submit();
                }
                1 => {
                    let acc = *rng.pick(&targets());
                    sim.call(who, WRAP, "storage_deposit").args_json(json!({"account_id": acc}))
                        .deposit(Balance::from_yoctonear(min)).submit();
                }
                _ => {
                    submit_op(&mut sim, &mut rng, min);
                }
            }
            for _ in 0..*rng.pick(&[0u64, 0, 1, 1, 1, 2, 3]) { sim.step(); check(&sim, &mut blocks, &mut bad); }
        }
        let mut guard = 0;
        while !sim.is_idle() && guard < 200 { sim.step(); check(&sim, &mut blocks, &mut bad); guard += 1; }
        for r in sim.receipts_in(h0 + 1..) {
            if r.receiver_id.as_str() == WRAP {
                if let Some(m) = r.method_names.first() {
                    calls.add(m);
                    if r.is_success() { ok_calls.add(m); }
                }
            }
        }
    }
    println!("{}", serde_json::to_string_pretty(&json!({
        "code": "9kQaNiscuPh69vRs1GyzfnkEjpUPGLjJhT6RaJBQyG7p", "traces": count, "blocks_checked": blocks,
        "min_storage_balance": min.to_string(), "violations": bad.len(), "first_violations": &bad[..bad.len().min(10)],
        "calls": calls.0, "succeeded": ok_calls.0,
    })).unwrap());
}

#[derive(Default)]
struct Counter(BTreeMap<String, u64>);
impl Counter {
    fn add(&mut self, k: &str) { *self.0.entry(k.to_string()).or_default() += 1; }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("checks") => checks(&wasm_bytes(&args[2])),
        Some("traces") => {
            let wasm = wasm_bytes(&args[2]);
            let seed: u64 = args[3].parse().unwrap();
            let start: u64 = args[4].parse().unwrap();
            let count: u64 = args[5].parse().unwrap();
            let base = world(&wasm);
            let min = min_bal(&base);
            let byte = base.storage_cost(1).as_yoctonear();
            for id in start..start + count {
                let t = run_trace(&base, seed, id, min, byte);
                println!("{}", serde_json::to_string(&t).unwrap());
            }
        }
        Some("oldinv") => old_invariant(&wasm_bytes(&args[2]), args[3].parse().unwrap(), args[4].parse().unwrap()),
        _ => eprintln!("usage: wnear-gen checks <wasm> | traces <wasm> <seed> <start> <count> | oldinv <wasm> <seed> <count>"),
    }
}
