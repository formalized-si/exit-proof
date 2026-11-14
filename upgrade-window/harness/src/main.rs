//! Conformance harness for the `Upgradable` plugin of near-plugins v0.5.1.
//!
//! Deploys the example vault (v1 build) on near-contract-sim (nearcore runtime), initializes it,
//! and runs random traces: code staging and deployment, staging-duration initialisation and
//! updates, jumps of the block timestamp to the edges of every delay, role grants and revocations,
//! vault deposits and withdrawals, and calls by accounts without roles. For every trace it records
//! every receipt the vault executed (in execution order, with its block timestamp, arguments,
//! outcome and the receipts it created) and the vault's observed state after every block: the
//! plugin's storage slots, the plugin's views, the account's code hash, the role grants and the
//! vault balances. The Lean model (`uwmodel`) replays the receipts; `scripts/compare.py` diffs.
//!
//! Usage:
//!   uw-gen info   <v1.wasm> <v2.wasm> <v3.wasm>
//!   uw-gen traces <v1.wasm> <v2.wasm> <v3.wasm> <seed> <start> <count>
//!   uw-gen witness <v1.wasm> <v2.wasm> <v3.wasm> [<unchecked v1> <unchecked v2> <unchecked v3>]

use near_contract_sim::prelude::*;
use near_contract_sim::{CryptoHash, ExecutionStatus, ReceiptOutcome};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap};

const VAULT: &str = "vault.near";
/// Accounts that may hold roles (the first four get "their" role in most traces).
const DAO: &str = "dao.near";
const STAGER: &str = "stager.near";
const DEPLOYER: &str = "deployer.near";
const DURMGR: &str = "durmgr.near";
/// Accounts that normally hold no role.
const USERS: [&str; 3] = ["alice.near", "bob.near", "carol.near"];
const ROLES: [&str; 4] = ["DAO", "CodeStager", "CodeDeployer", "DurationManager"];
/// The plugin's storage prefix and slot indices (`__UpgradableStorageKey`).
const UP_PREFIX: &[u8] = b"__up__";
/// A realistic starting block timestamp (2026-11-12T00:00:00Z in nanoseconds).
const T_START: u64 = 1_794_441_600_000_000_000;
const SEC: u64 = 1_000_000_000;

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
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// The contract codes the traces stage: three builds of the vault (same plugin, different
/// `version()`), byte strings that are not wasm, and a module that exports `up_verify_state` and
/// nothing else (deploying it removes the vault's code).
struct Codes {
    list: Vec<(String, Vec<u8>)>,
}

impl Codes {
    fn new(v1: Vec<u8>, v2: Vec<u8>, v3: Vec<u8>) -> Self {
        let stub = wat::parse_str(r#"(module (func (export "up_verify_state")))"#).expect("stub wat");
        let list = vec![
            ("v1".to_string(), v1),
            ("v2".to_string(), v2),
            ("v3".to_string(), v3),
            ("junk1".to_string(), b"not a wasm module".to_vec()),
            ("junk2".to_string(), vec![0u8; 3]),
            ("junk3".to_string(), b"\0asm\x01\0\0\0 truncated".to_vec()),
            ("stub".to_string(), stub),
        ];
        Codes { list }
    }
    fn bytes(&self, label: &str) -> &[u8] {
        &self.list.iter().find(|(l, _)| l == label).expect("label").1
    }
    fn hash(&self, label: &str) -> String {
        CryptoHash::hash_bytes(self.bytes(label)).to_string()
    }
    fn label_of(&self, bytes: &[u8]) -> String {
        if bytes.is_empty() {
            return String::new();
        }
        self.list.iter().find(|(_, b)| b == bytes).map(|(l, _)| l.clone()).unwrap_or_else(|| "?".into())
    }
    fn label_of_hash(&self, h: &str) -> String {
        self.list.iter().find(|(l, _)| self.hash(l) == h).map(|(l, _)| l.clone()).unwrap_or_else(|| "?".into())
    }
    fn table(&self) -> Value {
        let m: BTreeMap<String, String> = self.list.iter().map(|(l, _)| (l.clone(), self.hash(l))).collect();
        json!(m)
    }
}

fn accounts() -> Vec<&'static str> {
    let mut v = vec![DAO, STAGER, DEPLOYER, DURMGR];
    v.extend(USERS);
    v
}

fn base_world(codes: &Codes) -> Sim {
    let mut sim = Sim::new();
    sim.set_timestamp_ns(T_START);
    for a in accounts() {
        sim.create_account(a, Balance::from_near(1_000_000));
    }
    sim.create_account(VAULT, Balance::from_near(10_000));
    sim.deploy(VAULT, codes.bytes("v1").to_vec());
    sim
}

fn slot(sim: &Sim, idx: u8) -> Option<Vec<u8>> {
    let mut key = UP_PREFIX.to_vec();
    key.push(idx);
    sim.view_state(VAULT, &key).into_iter().find(|(k, _)| *k == key).map(|(_, v)| v)
}

fn slot_u64(sim: &Sim, idx: u8) -> Value {
    match slot(sim, idx) {
        Some(v) if v.len() == 8 => {
            let mut b = [0u8; 8];
            b.copy_from_slice(&v);
            json!(u64::from_le_bytes(b).to_string())
        }
        Some(v) => json!(format!("bad:{}", hex(&v))),
        None => Value::Null,
    }
}

fn view_json(sim: &Sim, method: &str, args: Value) -> Option<Value> {
    let v = sim.view(VAULT, method, args);
    v.value().and_then(|b| serde_json::from_slice::<Value>(b).ok())
}

fn num_or_null(v: &Value) -> Value {
    match v {
        Value::Null => Value::Null,
        other => json!(other.to_string()),
    }
}

/// The vault's state after a block: the plugin's storage slots (read from the trie, whatever
/// code is deployed), the same through the plugin's views, the account's code hash, the role
/// grants and the vault balances.
fn observe(sim: &Sim, codes: &Codes) -> Value {
    let acc = sim.account(VAULT).expect("vault account");
    let code_hash = acc.code_hash.to_string();
    let staged = slot(sim, 0);
    let storage = json!({
        "staged": staged.as_ref().map(|b| codes.label_of(b)),
        "status": {
            "staging_timestamp": slot_u64(sim, 1),
            "staging_duration": slot_u64(sim, 2),
            "new_staging_duration": slot_u64(sim, 3),
            "new_staging_duration_timestamp": slot_u64(sim, 4),
        },
    });
    let status_view = view_json(sim, "up_get_delay_status", json!({})).map(|s| {
        json!({
            "staging_duration": num_or_null(&s["staging_duration"]),
            "staging_timestamp": num_or_null(&s["staging_timestamp"]),
            "new_staging_duration": num_or_null(&s["new_staging_duration"]),
            "new_staging_duration_timestamp": num_or_null(&s["new_staging_duration_timestamp"]),
        })
    });
    let hash_view = sim.view(VAULT, "up_staged_code_hash", json!({}));
    let staged_hash = match hash_view.value().and_then(|b| serde_json::from_slice::<Value>(b).ok()) {
        Some(v) => json!({"ok": true, "hash": v}),
        None => json!({"ok": false}),
    };
    let version = view_json(sim, "version", json!({}));
    let mut roles: Vec<String> = vec![];
    let perms = view_json(sim, "acl_get_permissioned_accounts", json!({}));
    let mut super_admins = Value::Null;
    if let Some(p) = &perms {
        super_admins = p["super_admins"].clone();
        if let Some(m) = p["roles"].as_object() {
            for (role, v) in m {
                for g in v["grantees"].as_array().into_iter().flatten() {
                    roles.push(format!("{}:{}", g.as_str().unwrap_or("?"), role));
                }
                for a in v["admins"].as_array().into_iter().flatten() {
                    roles.push(format!("{}:admin-of-{}", a.as_str().unwrap_or("?"), role));
                }
            }
        }
    }
    roles.sort();
    let mut bal = serde_json::Map::new();
    for a in accounts() {
        if let Some(Value::String(s)) = view_json(sim, "balance_of", json!({"account_id": a})) {
            bal.insert(a.to_string(), json!(s));
        }
    }
    json!({
        "h": sim.height(), "t": sim.timestamp_ns().to_string(),
        "code_hash": code_hash, "code": codes.label_of_hash(&code_hash),
        "storage": storage,
        "views": {"status": status_view, "staged_hash": staged_hash, "version": version,
                   "roles": if perms.is_some() { json!(roles) } else { Value::Null },
                   "super_admins": super_admins, "bal": if perms.is_some() { Value::Object(bal) } else { Value::Null }},
        "near": sim.balance(VAULT).as_yoctonear().to_string(),
    })
}

fn obs_u64(o: &Value, field: &str) -> Option<u64> {
    o["storage"]["status"][field].as_str().and_then(|s| s.parse().ok())
}

/// Staging durations: zero, sub-block, a few blocks, long, and values at the u64 edges.
fn pick_duration(rng: &mut Rng, now: u64) -> u64 {
    match rng.below(100) {
        0..=11 => 0,
        12..=17 => 1,
        18..=37 => *rng.pick(&[SEC / 2, SEC, 2 * SEC, 3 * SEC, 5 * SEC, 8 * SEC]),
        38..=57 => *rng.pick(&[20 * SEC, 60 * SEC, 3600 * SEC, 86_400 * SEC, 7 * 86_400 * SEC]),
        58..=67 => rng.below(30 * SEC),
        68..=77 => {
            // `now + duration` lands on, or just past, u64::MAX a few blocks from now
            let k = rng.below(5);
            (u64::MAX - now).wrapping_sub(k * SEC).wrapping_add(rng.below(3)).wrapping_sub(1)
        }
        78..=83 => u64::MAX,
        84..=89 => u64::MAX - rng.below(4 * SEC),
        90..=94 => u64::MAX / 2,
        _ => rng.next(),
    }
}

fn caller_for(rng: &mut Rng, usual: &'static str) -> &'static str {
    match rng.below(100) {
        0..=59 => usual,
        60..=74 => DAO,
        75..=89 => *rng.pick(&USERS),
        _ => *rng.pick(&accounts()),
    }
}

/// Submits one random operation; returns its label.
fn submit_op(sim: &mut Sim, rng: &mut Rng, codes: &Codes, last: &Value, aim: Aim) -> String {
    let now = sim.timestamp_ns();
    let gas = Gas::from_teragas(300);
    // after a clock jump aimed at a delay's edge, usually make the call that delay guards
    let roll = match aim {
        Aim::Deploy if rng.chance(75) => 16,
        Aim::Apply if rng.chance(75) => 51,
        _ => rng.below(100),
    };
    match roll {
        // ---- stage code
        0..=15 => {
            let who = caller_for(rng, STAGER);
            let label = match rng.below(100) {
                0..=24 => "v2",
                25..=39 => "v3",
                40..=51 => "v1",
                52..=63 => "junk1",
                64..=69 => "junk2",
                70..=75 => "junk3",
                76..=79 => "stub",
                _ => "",
            };
            let bytes = if label.is_empty() { vec![] } else { codes.bytes(label).to_vec() };
            let d = if rng.chance(4) { 1 } else { 0 };
            sim.call(who, VAULT, "up_stage_code").args(bytes).deposit(Balance::from_yoctonear(d)).gas(gas).submit();
            format!("{who} up_stage_code({}) deposit {d}", if label.is_empty() { "<empty>" } else { label })
        }
        // ---- deploy code
        16..=33 => {
            let who = if aim == Aim::Deploy && rng.chance(85) { *rng.pick(&[DEPLOYER, DAO]) } else { caller_for(rng, DEPLOYER) };
            let staged = last["storage"]["staged"].as_str().unwrap_or("");
            let hash = match rng.below(100) {
                _ if aim == Aim::Deploy && !staged.is_empty() && staged != "?" => codes.hash(staged),
                0..=77 if !staged.is_empty() && staged != "?" => codes.hash(staged),
                0..=87 => codes.hash(*rng.pick(&["v1", "v2", "v3", "junk1", "stub"])),
                88..=93 => "not-a-hash".to_string(),
                _ => String::new(),
            };
            let fc = match rng.below(100) {
                0..=54 => Value::Null,
                55..=69 => json!({"function_name": "migrate_ok", "arguments": [], "amount": "0", "gas": "5000000000000"}),
                70..=79 => json!({"function_name": "migrate_fail", "arguments": [1, 2, 255], "amount": "0", "gas": "5000000000000"}),
                80..=86 => json!({"function_name": "no_such_method", "arguments": [], "amount": "0", "gas": "3000000000000"}),
                87..=92 => json!({"function_name": "up_verify_state", "arguments": [123, 125], "amount": "0", "gas": "4000000000000"}),
                _ => json!({"function_name": "migrate_ok", "arguments": [], "amount": "1", "gas": "5000000000000"}),
            };
            let args = match rng.below(100) {
                0..=91 => json!({"hash": hash, "function_call_args": fc}),
                92..=94 => json!({"hash": hash}),
                95..=96 => json!({}),
                97 => json!({"hash": 5}),
                98 => json!({"hash": hash, "function_call_args": {"function_name": "migrate_ok", "arguments": [], "amount": 0, "gas": "5000000000000"}}),
                _ => json!({"hash": hash, "function_call_args": {"function_name": "migrate_ok", "arguments": [256], "amount": "0", "gas": "5000000000000"}}),
            };
            let d = if rng.chance(3) { 1 } else { 0 };
            sim.call(who, VAULT, "up_deploy_code").args_json(args.clone()).deposit(Balance::from_yoctonear(d)).gas(gas).submit();
            format!("{who} up_deploy_code({args}) deposit {d}")
        }
        // ---- staging duration: init / stage update / apply update
        34..=39 => {
            let who = caller_for(rng, DURMGR);
            let dur = pick_duration(rng, now);
            let args = match rng.below(100) {
                0..=93 => json!({"staging_duration": dur}),
                94..=95 => json!({"staging_duration": dur.to_string()}),
                96..=97 => json!({}),
                _ => json!({"staging_duration": -1}),
            };
            sim.call(who, VAULT, "up_init_staging_duration").args_json(args.clone()).gas(gas).submit();
            format!("{who} up_init_staging_duration({args})")
        }
        40..=50 => {
            let who = caller_for(rng, DURMGR);
            let dur = pick_duration(rng, now);
            let args = match rng.below(100) {
                0..=95 => json!({"staging_duration": dur}),
                96..=97 => json!({"staging_duration": dur.to_string()}),
                _ => json!({"staging_duration": 1.5}),
            };
            let d = if rng.chance(3) { 1 } else { 0 };
            sim.call(who, VAULT, "up_stage_update_staging_duration").args_json(args.clone())
                .deposit(Balance::from_yoctonear(d)).gas(gas).submit();
            format!("{who} up_stage_update_staging_duration({args}) deposit {d}")
        }
        51..=61 => {
            let who = if aim == Aim::Apply && rng.chance(85) { *rng.pick(&[DURMGR, DAO]) } else { caller_for(rng, DURMGR) };
            sim.call(who, VAULT, "up_apply_update_staging_duration").args_json(json!({})).gas(gas).submit();
            format!("{who} up_apply_update_staging_duration()")
        }
        // ---- roles
        62..=69 => {
            let role = *rng.pick(&ROLES);
            let target = *rng.pick(&accounts());
            let by = if rng.chance(75) { VAULT } else { *rng.pick(&accounts()) };
            let method = if rng.chance(50) { "acl_grant_role" } else { "acl_revoke_role" };
            let args = if rng.chance(95) {
                json!({"role": role, "account_id": target})
            } else {
                json!({"role": "Owner", "account_id": target})
            };
            sim.call(by, VAULT, method).args_json(args.clone()).gas(gas).submit();
            format!("{by} {method}({args})")
        }
        70..=72 => {
            let who = *rng.pick(&accounts());
            let role = *rng.pick(&ROLES);
            sim.call(who, VAULT, "acl_renounce_role").args_json(json!({"role": role})).gas(gas).submit();
            format!("{who} acl_renounce_role({role})")
        }
        73..=75 => {
            // admin-only ACL methods, called by accounts that are not admins
            let who = *rng.pick(&accounts());
            let role = *rng.pick(&ROLES);
            let (method, args) = match rng.below(6) {
                0 => ("acl_add_super_admin", json!({"account_id": who})),
                1 => ("acl_add_admin", json!({"role": role, "account_id": who})),
                2 => ("acl_revoke_admin", json!({"role": role, "account_id": VAULT})),
                3 => ("acl_revoke_super_admin", json!({"account_id": VAULT})),
                4 => ("acl_transfer_super_admin", json!({"account_id": who})),
                _ => ("acl_renounce_admin", json!({"role": role})),
            };
            sim.call(who, VAULT, method).args_json(args.clone()).gas(gas).submit();
            format!("{who} {method}({args})")
        }
        // ---- the vault
        76..=81 => {
            let who = *rng.pick(&accounts());
            let amt = *rng.pick(&[0u128, 1, 5_000_000_000_000_000_000_000_000, 1_000_000_000_000_000_000_000_000]);
            sim.call(who, VAULT, "deposit").args_json(json!({})).deposit(Balance::from_yoctonear(amt)).gas(gas).submit();
            format!("{who} deposit {amt}")
        }
        82..=88 => {
            let who = *rng.pick(&accounts());
            let bal: u128 = last["views"]["bal"][who].as_str().and_then(|s| s.parse().ok()).unwrap_or(0);
            let amt = match rng.below(10) {
                0..=4 => bal,
                5 => bal.saturating_add(1),
                6 => 0,
                7 => bal / 2,
                _ => 1,
            };
            sim.call(who, VAULT, "withdraw").args_json(json!({"amount": amt.to_string()})).gas(gas).submit();
            format!("{who} withdraw {amt}")
        }
        // ---- everything else
        _ => {
            let who = *rng.pick(&accounts());
            let (method, args, by): (&str, Value, &str) = match rng.below(12) {
                0 => ("up_get_delay_status", json!({}), who),
                1 => ("up_staged_code_hash", json!({}), who),
                2 => ("up_verify_state", json!({}), who),
                3 => ("version", json!({}), who),
                4 => ("new", json!({"staging_duration": 0}), who),
                5 => ("new", json!({"staging_duration": null}), VAULT),
                6 => ("migrate_ok", json!({}), who),
                7 => ("migrate_ok", json!({}), VAULT),
                8 => ("migrate_fail", json!({}), VAULT),
                9 => ("acl_init_super_admin", json!({"account_id": who}), if rng.chance(50) { VAULT } else { who }),
                10 => ("no_such_method", json!({}), who),
                _ => ("withdraw", json!({"amount": 5}), who),
            };
            let d = if rng.chance(10) { 1 } else { 0 };
            sim.call(by, VAULT, method).args_json(args.clone()).deposit(Balance::from_yoctonear(d)).gas(gas).submit();
            format!("{by} {method}({args}) deposit {d}")
        }
    }
}

/// Moves the clock so that the next transaction's first receipt runs at a chosen block
/// timestamp: on, one nanosecond before, or one after the staging timestamp or the staged
/// duration update's timestamp, or some time ahead. Only forward, and never near u64::MAX.
fn maybe_jump(sim: &mut Sim, rng: &mut Rng, last: &Value) -> Option<(String, Aim)> {
    let now = sim.timestamp_ns();
    let floor = now + 3 * SEC;
    let cap = 1u64 << 62;
    let around = |rng: &mut Rng, t: u64| -> u64 {
        match rng.below(5) {
            0 => t.saturating_sub(1),
            1 | 2 => t,
            3 => t.saturating_add(1),
            _ => t.saturating_add(rng.below(3 * SEC)),
        }
    };
    let (target, aim) = match rng.below(100) {
        0..=34 => (obs_u64(last, "staging_timestamp").map(|t| around(rng, t)), Aim::Deploy),
        35..=59 => (obs_u64(last, "new_staging_duration_timestamp").map(|t| around(rng, t)), Aim::Apply),
        60..=79 => (Some(now + rng.below(40 * SEC)), Aim::None),
        80..=89 => (Some(now + *rng.pick(&[3600 * SEC, 86_400 * SEC, 8 * 86_400 * SEC])), Aim::None),
        _ => (None, Aim::None),
    };
    let target = target?;
    if target < floor || target > cap {
        return None;
    }
    sim.set_timestamp_ns(target);
    Some((format!("clock: next receipt at {target}"), aim))
}

/// What the clock jump before an operation was aimed at.
#[derive(Clone, Copy, PartialEq)]
enum Aim {
    None,
    Deploy,
    Apply,
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

fn status_text(r: &ReceiptOutcome) -> String {
    match r.failure() {
        Some(f) => format!("{f:?}"),
        None => "ok".into(),
    }
}

fn run_trace(base: &Sim, codes: &Codes, seed: u64, id: u64) -> Value {
    let mut sim = base.clone();
    let mut rng = Rng(seed ^ (id.wrapping_mul(0x9E3779B97F4A7C15)) | 1);
    // the contract's own #[init]: with or without a staging duration
    let init_dur: Option<u64> = match rng.below(100) {
        0..=34 => None,
        35..=44 => Some(0),
        _ => Some(*rng.pick(&[1, SEC, 2 * SEC, 5 * SEC, 20 * SEC, 3600 * SEC, 7 * 86_400 * SEC])),
    };
    let init = sim.call(VAULT, VAULT, "new").args_json(json!({"staging_duration": init_dur})).transact();
    assert!(init.is_success(), "init failed: {:?}", init.failure());
    let h0 = sim.height();
    let first = observe(&sim, codes);
    let mut obs = vec![first.clone()];
    let mut ops: Vec<String> = vec![];
    let gas = Gas::from_teragas(300);
    // prefix: the usual role holders get their roles in most traces, users deposit
    for (who, role) in [(DAO, "DAO"), (STAGER, "CodeStager"), (DEPLOYER, "CodeDeployer"), (DURMGR, "DurationManager")] {
        if rng.chance(85) {
            sim.call(VAULT, VAULT, "acl_grant_role").args_json(json!({"role": role, "account_id": who})).gas(gas).submit();
            ops.push(format!("{VAULT} acl_grant_role({role}, {who}) (prefix)"));
        }
    }
    for who in USERS {
        if rng.chance(70) {
            let amt = Balance::from_near(1 + rng.below(20) as u128);
            sim.call(who, VAULT, "deposit").args_json(json!({})).deposit(amt).gas(gas).submit();
            ops.push(format!("{who} deposit {} (prefix)", amt.as_yoctonear()));
        }
    }
    while !sim.is_idle() {
        sim.step();
        obs.push(observe(&sim, codes));
    }
    let n_ops = 12 + rng.below(40);
    for _ in 0..n_ops {
        let last = obs.last().unwrap().clone();
        let mut aim = Aim::None;
        if rng.chance(45) {
            if let Some((l, a)) = maybe_jump(&mut sim, &mut rng, &last) {
                ops.push(l);
                aim = a;
            }
        }
        ops.push(submit_op(&mut sim, &mut rng, codes, &last, aim));
        let gap = *rng.pick(&[0u64, 1, 1, 1, 2, 2, 3]);
        for _ in 0..gap {
            sim.step();
            obs.push(observe(&sim, codes));
        }
    }
    let mut guard = 0;
    while !sim.is_idle() && guard < 200 {
        sim.step();
        obs.push(observe(&sim, codes));
        guard += 1;
    }
    let all = sim.receipts_in(h0 + 1..);
    let by_id: HashMap<CryptoHash, &ReceiptOutcome> = all.iter().map(|r| (r.receipt_id, r)).collect();
    let is_batch = |r: &ReceiptOutcome| r.actions.first().map(String::as_str) == Some("DeployContract");
    let mut steps = vec![];
    for r in &all {
        if r.receiver_id.as_str() != VAULT {
            continue;
        }
        let t = r.block_timestamp_ns.to_string();
        if is_batch(r) {
            steps.push(json!({
                "h": r.block_height, "t": t, "k": "batch", "rid": r.receipt_id.to_string(),
                "pred": r.predecessor_id.as_str(), "ok": r.is_success(), "status": status_text(r),
                "actions": r.actions, "methods": r.method_names,
            }));
            continue;
        }
        let Some(meth) = r.method_names.first() else { continue };
        let raw = r.args.first().cloned().unwrap_or_default();
        let children: Vec<&&ReceiptOutcome> = r
            .receipt_ids
            .iter()
            .filter_map(|c| by_id.get(c))
            .filter(|c| c.predecessor_id.as_str() == VAULT)
            .collect();
        let eff: Vec<Value> = children
            .iter()
            .map(|c| {
                json!({
                    "receiver": c.receiver_id.as_str(), "actions": c.actions, "methods": c.method_names,
                    "args": c.args.iter().map(|a| hex(a)).collect::<Vec<_>>(),
                    "gas": c.attached_gas.as_gas().to_string(), "deposit": c.deposit.as_yoctonear().to_string(),
                    "rid": c.receipt_id.to_string(),
                })
            })
            .collect();
        let deploy_rid = children.iter().find(|c| is_batch(c)).map(|c| c.receipt_id.to_string());
        let mut step = json!({
            "h": r.block_height, "t": t, "k": "call", "rid": r.receipt_id.to_string(),
            "pred": r.predecessor_id.as_str(), "method": meth,
            "deposit": r.deposit.as_yoctonear().to_string(),
            "ok": r.is_success(), "status": status_text(r), "ret": ret_of(r), "eff": eff,
            "deploy_rid": deploy_rid, "logs": r.logs,
        });
        if meth == "up_stage_code" {
            step["code"] = json!(codes.label_of(&raw));
            step["args"] = json!("");
        } else {
            step["args"] = json!(String::from_utf8_lossy(&raw).to_string());
        }
        steps.push(step);
    }
    json!({
        "id": id, "self": VAULT, "codes": codes.table(), "users": accounts(),
        "init_dur": init_dur.map(|d| d.to_string()), "init_code": "v1",
        "t0": first["t"], "ops": ops, "steps": steps, "obs": obs, "settled": sim.is_idle(),
    })
}

// ---------------------------------------------------------------------------------------------
// Witness scenarios: the statements of the README executed on the wasm, step by step, with a
// stopped clock so that every receipt runs at a chosen block timestamp.

fn vault_receipts(o: &near_contract_sim::TxOutcome) -> Vec<Value> {
    o.receipts
        .iter()
        .filter(|r| r.receiver_id.as_str() == VAULT && r.refund.is_none() && !r.actions.is_empty())
        .map(|r| {
            json!({
                "block": r.block_height, "block_timestamp": r.block_timestamp_ns.to_string(),
                "predecessor": r.predecessor_id.as_str(), "actions": r.actions, "methods": r.method_names,
                "ok": r.is_success(), "status": status_text(r),
            })
        })
        .collect()
}

fn snap(sim: &Sim, codes: &Codes) -> Value {
    let o = observe(sim, codes);
    json!({
        "block_timestamp": o["t"], "code": o["code"], "version": o["views"]["version"],
        "up_get_delay_status": o["views"]["status"], "up_staged_code_hash": o["views"]["staged_hash"]["hash"],
        "staged": o["storage"]["staged"],
    })
}

fn setup(base: &Sim, dur: Option<u64>, roles: &[(&str, &str)]) -> Sim {
    let mut sim = base.clone();
    sim.call(VAULT, VAULT, "new").args_json(json!({"staging_duration": dur})).transact().assert_success();
    for (who, role) in roles {
        sim.call(VAULT, VAULT, "acl_grant_role").args_json(json!({"role": role, "account_id": who})).transact().assert_success();
    }
    sim.call("alice.near", VAULT, "deposit").args_json(json!({})).deposit(Balance::from_near(5)).transact().assert_success();
    let t = sim.timestamp_ns() + 10 * SEC;
    sim.pause_clock_at(t);
    sim
}

struct Scenario {
    name: &'static str,
    statement: &'static str,
    steps: Vec<Value>,
    checks: Vec<(String, bool)>,
}

impl Scenario {
    fn new(name: &'static str, statement: &'static str) -> Self {
        Scenario { name, statement, steps: vec![], checks: vec![] }
    }
    /// Runs a transaction with the clock stopped at `t`, records what the vault executed.
    fn at(&mut self, sim: &mut Sim, codes: &Codes, t: u64, what: &str, tx: impl FnOnce(&mut Sim) -> near_contract_sim::TxOutcome) -> Vec<Value> {
        sim.pause_clock_at(t);
        let o = tx(sim);
        sim.settle();
        let rs = vault_receipts(&o);
        self.steps.push(json!({"clock": t.to_string(), "step": what, "receipts": rs, "after": snap(sim, codes)}));
        rs
    }
    fn check(&mut self, what: &str, ok: bool) {
        self.checks.push((what.to_string(), ok));
    }
    fn done(self) -> Value {
        let ok = self.checks.iter().all(|(_, b)| *b);
        json!({
            "scenario": self.name, "statement": self.statement, "ok": ok,
            "checks": self.checks.iter().map(|(w, b)| json!({"check": w, "holds": b})).collect::<Vec<_>>(),
            "steps": self.steps,
        })
    }
}

fn r_ok(rs: &[Value], i: usize) -> bool {
    rs.get(i).and_then(|r| r["ok"].as_bool()).unwrap_or(false)
}

fn r_status(rs: &[Value], i: usize) -> String {
    rs.get(i).and_then(|r| r["status"].as_str()).unwrap_or("").to_string()
}

fn r_time(rs: &[Value], i: usize) -> u64 {
    rs.get(i).and_then(|r| r["block_timestamp"].as_str()).and_then(|s| s.parse().ok()).unwrap_or(0)
}

fn code_of(sim: &Sim, codes: &Codes) -> String {
    codes.label_of_hash(&sim.account(VAULT).unwrap().code_hash.to_string())
}

fn witness(base: &Sim, codes: &Codes, unchecked: Option<&Codes>) -> Value {
    let g = Gas::from_teragas(140);
    let five = Balance::from_near(5).as_yoctonear().to_string();
    let mut out = vec![];

    // W4: no staging duration -> stage and deploy in one transaction; funds are stuck one block later
    {
        let mut sc = Scenario::new("W4_no_window", "With no staging duration, one transaction stages and deploys new code; here the new code has no withdraw method.");
        let mut sim = setup(base, None, &[(DAO, "DAO")]);
        let t = sim.timestamp_ns();
        let (stub, h) = (codes.bytes("stub").to_vec(), codes.hash("stub"));
        let rs = sc.at(&mut sim, codes, t, "dao.near: one transaction [up_stage_code(stub), up_deploy_code(hash of stub)]", |sim| {
            sim.tx(DAO, VAULT).call("up_stage_code").args(stub).gas(g).call("up_deploy_code").args_json(json!({"hash": h})).gas(g).transact()
        });
        sc.check("both calls ran in one receipt and succeeded", r_ok(&rs, 0) && rs[0]["methods"] == json!(["up_stage_code", "up_deploy_code"]));
        sc.check("the deploy batch ran at the same block timestamp and succeeded", r_ok(&rs, 1) && rs[1]["actions"][0] == "DeployContract" && r_time(&rs, 1) == r_time(&rs, 0));
        sc.check("the account now runs the staged code", code_of(&sim, codes) == "stub");
        let amt = five.clone();
        let rs = sc.at(&mut sim, codes, t, "alice.near: withdraw(5 NEAR)", |sim| sim.call("alice.near", VAULT, "withdraw").args_json(json!({"amount": amt})).transact());
        sc.check("alice's withdrawal fails: the method is gone", !r_ok(&rs, 0) && r_status(&rs, 0).contains("MethodNotFound"));
        out.push(sc.done());
    }

    // W1 + W2 + W5: a duration D; exit inside the window; deploy refused 1 ns early, accepted at t + D
    {
        let d = 3600 * SEC;
        let mut sc = Scenario::new("W1_W2_W5_window", "With staging duration D = 1 h: the staged hash is visible from staging to deploy, a user withdraws inside the window, the deploy is refused one nanosecond before staging + D and accepted at staging + D.");
        let mut sim = setup(base, Some(d), &[(STAGER, "CodeStager"), (DEPLOYER, "CodeDeployer")]);
        let t = sim.timestamp_ns();
        let (v2, h) = (codes.bytes("v2").to_vec(), codes.hash("v2"));
        let rs = sc.at(&mut sim, codes, t, "stager.near: up_stage_code(v2)", |sim| sim.call(STAGER, VAULT, "up_stage_code").args(v2).gas(g).transact());
        let ts = r_time(&rs, 0);
        let s1 = snap(&sim, codes);
        sc.check("staging timestamp = block timestamp of staging + D", s1["up_get_delay_status"]["staging_timestamp"] == json!((ts + d).to_string()));
        sc.check("up_staged_code_hash shows the hash of v2", s1["up_staged_code_hash"] == json!(h));
        let amt = five.clone();
        let rs = sc.at(&mut sim, codes, ts + d / 2, "alice.near: withdraw(5 NEAR), half-way through the window", |sim| sim.call("alice.near", VAULT, "withdraw").args_json(json!({"amount": amt})).transact());
        sc.check("alice's withdrawal succeeds inside the window", r_ok(&rs, 0));
        let hh = h.clone();
        let rs = sc.at(&mut sim, codes, ts + d - 1, "deployer.near: up_deploy_code(hash of v2), 1 ns before staging + D", |sim| sim.call(DEPLOYER, VAULT, "up_deploy_code").args_json(json!({"hash": hh})).gas(g).transact());
        sc.check("refused: Deploy code too early", !r_ok(&rs, 0) && r_status(&rs, 0).contains("Deploy code too early"));
        sc.check("the staged hash is still the hash of v2, the code is still v1", snap(&sim, codes)["up_staged_code_hash"] == json!(h) && code_of(&sim, codes) == "v1");
        let hw = codes.hash("v3");
        let rs = sc.at(&mut sim, codes, ts + d, "deployer.near: up_deploy_code(hash of v3) at staging + D", |sim| sim.call(DEPLOYER, VAULT, "up_deploy_code").args_json(json!({"hash": hw})).gas(g).transact());
        sc.check("refused: wrong hash", !r_ok(&rs, 0) && r_status(&rs, 0).contains("wrong hash"));
        let hh = h.clone();
        let rs = sc.at(&mut sim, codes, ts + d, "deployer.near: up_deploy_code(hash of v2) at staging + D", |sim| sim.call(DEPLOYER, VAULT, "up_deploy_code").args_json(json!({"hash": hh})).gas(g).transact());
        sc.check("accepted at exactly staging + D; the batch deploys v2", r_ok(&rs, 0) && r_ok(&rs, 1) && code_of(&sim, codes) == "v2");
        // the staged copy stays; much later the deployer re-deploys it with a #[private] call attached
        let hh = h.clone();
        let rs = sc.at(&mut sim, codes, ts + 30 * 86_400 * SEC, "deployer.near, 30 days later, nothing newly staged: up_deploy_code(hash of v2, function call migrate_ok)", |sim| {
            sim.call(DEPLOYER, VAULT, "up_deploy_code").args_json(json!({"hash": hh, "function_call_args": {"function_name": "migrate_ok", "arguments": [], "amount": "0", "gas": "5000000000000"}})).gas(g).transact()
        });
        sc.check("accepted at once: the staged copy left after the upgrade is deployable at any time, and the #[private] method runs with the contract as caller", r_ok(&rs, 0) && r_ok(&rs, 1) && rs[1]["methods"] == json!(["migrate_ok", "up_verify_state"]));
        let rs = sc.at(&mut sim, codes, ts + 30 * 86_400 * SEC, "deployer.near: migrate_ok() directly", |sim| sim.call(DEPLOYER, VAULT, "migrate_ok").args_json(json!({})).transact());
        sc.check("the same method called directly is refused (private)", !r_ok(&rs, 0) && r_status(&rs, 0).contains("is private"));
        out.push(sc.done());
    }

    // W3 shortcut 1: code staged before the duration was initialised
    {
        let d = 7 * 86_400 * SEC;
        let mut sc = Scenario::new("W3_prestaged", "Code staged while no duration is set stays deployable at once after up_init_staging_duration(7 days).");
        let mut sim = setup(base, None, &[(DAO, "DAO")]);
        let t = sim.timestamp_ns();
        let (v2, h) = (codes.bytes("v2").to_vec(), codes.hash("v2"));
        sc.at(&mut sim, codes, t, "dao.near: up_stage_code(v2), no duration set", |sim| sim.call(DAO, VAULT, "up_stage_code").args(v2).gas(g).transact());
        let rs = sc.at(&mut sim, codes, t, "dao.near: up_init_staging_duration(7 days)", |sim| sim.call(DAO, VAULT, "up_init_staging_duration").args_json(json!({"staging_duration": d})).transact());
        let s = snap(&sim, codes);
        sc.check("the status now shows a 7-day duration and a staging timestamp that is not in the future", r_ok(&rs, 0) && s["up_get_delay_status"]["staging_duration"] == json!(d.to_string()) && s["up_get_delay_status"]["staging_timestamp"] == json!(t.to_string()));
        let rs = sc.at(&mut sim, codes, t, "dao.near: up_deploy_code(hash of v2), same block timestamp", |sim| sim.call(DAO, VAULT, "up_deploy_code").args_json(json!({"hash": h})).gas(g).transact());
        sc.check("accepted; the account runs v2", r_ok(&rs, 0) && r_ok(&rs, 1) && code_of(&sim, codes) == "v2");
        out.push(sc.done());
    }

    // W3 shortcut 2: shrink the duration first
    {
        let d = 3600 * SEC;
        let mut sc = Scenario::new("W3_shrink", "From duration D = 1 h: a duration update to 0 is staged, applicable only D later; once applied, new code is staged and deployed in one transaction. The warning visible for D was the staged duration update, not the code.");
        let mut sim = setup(base, Some(d), &[(DAO, "DAO")]);
        let t = sim.timestamp_ns();
        let rs = sc.at(&mut sim, codes, t, "dao.near: up_stage_update_staging_duration(0)", |sim| sim.call(DAO, VAULT, "up_stage_update_staging_duration").args_json(json!({"staging_duration": 0})).transact());
        let s = snap(&sim, codes);
        sc.check("the status shows the staged update and its timestamp = now + D", r_ok(&rs, 0) && s["up_get_delay_status"]["new_staging_duration"] == json!("0") && s["up_get_delay_status"]["new_staging_duration_timestamp"] == json!((t + d).to_string()));
        let rs = sc.at(&mut sim, codes, t + d - 1, "dao.near: up_apply_update_staging_duration(), 1 ns early", |sim| sim.call(DAO, VAULT, "up_apply_update_staging_duration").args_json(json!({})).transact());
        sc.check("refused: Update duration too early", !r_ok(&rs, 0) && r_status(&rs, 0).contains("Update duration too early"));
        let rs = sc.at(&mut sim, codes, t + d, "dao.near: up_apply_update_staging_duration() at now + D", |sim| sim.call(DAO, VAULT, "up_apply_update_staging_duration").args_json(json!({})).transact());
        sc.check("accepted; the duration is 0", r_ok(&rs, 0) && snap(&sim, codes)["up_get_delay_status"]["staging_duration"] == json!("0"));
        let (v3, h) = (codes.bytes("v3").to_vec(), codes.hash("v3"));
        let rs = sc.at(&mut sim, codes, t + d, "dao.near: one transaction [up_stage_code(v3), up_deploy_code(hash of v3)]", |sim| {
            sim.tx(DAO, VAULT).call("up_stage_code").args(v3).gas(g).call("up_deploy_code").args_json(json!({"hash": h})).gas(g).transact()
        });
        sc.check("accepted at the block timestamp of staging; the account runs v3", r_ok(&rs, 0) && r_ok(&rs, 1) && code_of(&sim, codes) == "v3");
        out.push(sc.done());
    }

    // W3 shortcut 3: the same source built without overflow checks
    if let Some(uc) = unchecked {
        let mut sc = Scenario::new("W3_unchecked_build", "The same contract built without overflow checks (cargo's default release profile), duration D = u64::MAX - 10: staging an update to 0 wraps its timestamp into the past, so it is applicable at once; the checked build panics instead.");
        let d = u64::MAX - 10;
        let ubase = base_world(uc);
        let mut sim = setup(&ubase, Some(d), &[(DAO, "DAO")]);
        let t = sim.timestamp_ns();
        let rs = sc.at(&mut sim, uc, t, "unchecked build, dao.near: up_stage_update_staging_duration(0)", |sim| sim.call(DAO, VAULT, "up_stage_update_staging_duration").args_json(json!({"staging_duration": 0})).transact());
        let s = snap(&sim, uc);
        let wrapped = t.wrapping_add(d);
        sc.check("accepted; the update's timestamp wrapped to (now + D) mod 2^64, which is in the past", r_ok(&rs, 0) && s["up_get_delay_status"]["new_staging_duration_timestamp"] == json!(wrapped.to_string()) && wrapped < t);
        let rs = sc.at(&mut sim, uc, t, "unchecked build, dao.near: up_apply_update_staging_duration(), same block timestamp", |sim| sim.call(DAO, VAULT, "up_apply_update_staging_duration").args_json(json!({})).transact());
        sc.check("accepted at once; the duration is 0", r_ok(&rs, 0) && snap(&sim, uc)["up_get_delay_status"]["staging_duration"] == json!("0"));
        let (v2, h) = (uc.bytes("v2").to_vec(), uc.hash("v2"));
        let rs = sc.at(&mut sim, uc, t, "unchecked build, dao.near: one transaction [up_stage_code(v2), up_deploy_code(hash of v2)]", |sim| {
            sim.tx(DAO, VAULT).call("up_stage_code").args(v2).gas(g).call("up_deploy_code").args_json(json!({"hash": h})).gas(g).transact()
        });
        sc.check("accepted; the code is replaced with all calls at one block timestamp", r_ok(&rs, 0) && r_ok(&rs, 1) && code_of(&sim, uc) == "v2");
        // the checked build
        let mut sim = setup(base, Some(d), &[(DAO, "DAO")]);
        let t = sim.timestamp_ns();
        let rs = sc.at(&mut sim, codes, t, "checked build (the example), dao.near: up_stage_update_staging_duration(0)", |sim| sim.call(DAO, VAULT, "up_stage_update_staging_duration").args_json(json!({"staging_duration": 0})).transact());
        sc.check("the checked build panics: attempt to add with overflow", !r_ok(&rs, 0) && r_status(&rs, 0).contains("attempt to add with overflow"));
        out.push(sc.done());
    }

    // A5: the exit hypothesis of W5 is about the host. Staged code is stored by the contract and
    // its storage is paid from the contract's own balance, depositors' NEAR included.
    {
        let mut sc = Scenario::new("A5_storage_staking", "The vault holds its storage cost, alice's 5 NEAR and 0.1 NEAR more. Staging 199 KB of code locks about 2 NEAR as storage stake: alice's full withdrawal fails until the staged code is removed.");
        let mut sim = setup(base, Some(3600 * SEC), &[(STAGER, "CodeStager")]);
        let t = sim.timestamp_ns();
        let stake = sim.storage_cost(sim.account(VAULT).unwrap().storage_usage).as_yoctonear();
        let spare = Balance::from_near(1).as_yoctonear() / 10;
        sim.set_balance(VAULT, Balance::from_yoctonear(stake + Balance::from_near(5).as_yoctonear() + spare));
        let v3 = codes.bytes("v3").to_vec();
        let rs = sc.at(&mut sim, codes, t, "stager.near: up_stage_code(v3)", |sim| sim.call(STAGER, VAULT, "up_stage_code").args(v3).gas(g).transact());
        sc.check("staging succeeds: the deposits cover the new storage", r_ok(&rs, 0));
        let amt = five.clone();
        let rs = sc.at(&mut sim, codes, t + 60 * SEC, "alice.near: withdraw(5 NEAR)", |sim| sim.call("alice.near", VAULT, "withdraw").args_json(json!({"amount": amt})).transact());
        sc.check("alice's full withdrawal fails: LackBalanceForState", !r_ok(&rs, 0) && r_status(&rs, 0).contains("LackBalanceForState"));
        let three = Balance::from_near(3).as_yoctonear().to_string();
        let rs = sc.at(&mut sim, codes, t + 60 * SEC, "alice.near: withdraw(3 NEAR)", |sim| sim.call("alice.near", VAULT, "withdraw").args_json(json!({"amount": three})).transact());
        sc.check("a partial withdrawal that leaves the storage stake succeeds", r_ok(&rs, 0));
        let rs = sc.at(&mut sim, codes, t + 120 * SEC, "stager.near: up_stage_code(<empty>)", |sim| sim.call(STAGER, VAULT, "up_stage_code").gas(g).transact());
        sc.check("the staged code is removed", r_ok(&rs, 0) && snap(&sim, codes)["staged"].is_null());
        let two = Balance::from_near(2).as_yoctonear().to_string();
        let rs = sc.at(&mut sim, codes, t + 120 * SEC, "alice.near: withdraw(2 NEAR)", |sim| sim.call("alice.near", VAULT, "withdraw").args_json(json!({"amount": two})).transact());
        sc.check("the rest can be withdrawn again", r_ok(&rs, 0));
        out.push(sc.done());
    }

    // A deploy batch in flight does not show in the views: a quiet reading right after a
    // deploy says nothing about it.
    {
        let d = 7 * 86_400 * SEC;
        let mut sc = Scenario::new("inflight_invisible", "With no duration set, one transaction stages v2, deploys it, removes the staged code and initialises a 7-day duration. The reading one block later shows a 7-day duration, nothing staged, the old code; the block after that the code is v2.");
        let mut sim = setup(base, None, &[(DAO, "DAO")]);
        let t = sim.timestamp_ns();
        sim.pause_clock_at(t);
        let (v2, h) = (codes.bytes("v2").to_vec(), codes.hash("v2"));
        let q = Gas::from_teragas(70);
        let hash = sim
            .tx(DAO, VAULT)
            .call("up_stage_code").args(v2).gas(q)
            .call("up_deploy_code").args_json(json!({"hash": h})).gas(q)
            .call("up_stage_code").gas(q)
            .call("up_init_staging_duration").args_json(json!({"staging_duration": d})).gas(q)
            .submit();
        sim.step(); // the transaction becomes a receipt
        sim.step(); // the four calls run; the deploy batch is created
        let reading = snap(&sim, codes);
        sc.steps.push(json!({"clock": t.to_string(), "step": "dao.near: one transaction [up_stage_code(v2), up_deploy_code(hash of v2), up_stage_code(<empty>), up_init_staging_duration(7 days)]; reading after the block in which the calls ran", "after": reading}));
        sc.check("the reading is quiet: 7-day duration, no staging timestamp, nothing staged, no staged update",
            reading["up_get_delay_status"]["staging_duration"] == json!(d.to_string())
                && reading["up_get_delay_status"]["staging_timestamp"].is_null()
                && reading["up_get_delay_status"]["new_staging_duration"].is_null()
                && reading["up_staged_code_hash"].is_null());
        sc.check("the account still runs v1 at that reading", reading["code"] == json!("v1"));
        sim.settle();
        let o = sim.outcome(hash);
        let rs = vault_receipts(&o);
        let after = snap(&sim, codes);
        sc.steps.push(json!({"clock": t.to_string(), "step": "next block: the deploy batch runs", "receipts": rs, "after": after}));
        sc.check("one block later the account runs v2, with the status still quiet", after["code"] == json!("v2") && r_ok(&rs, 1) && after["up_staged_code_hash"].is_null());
        out.push(sc.done());
    }

    let ok = out.iter().all(|s| s["ok"] == json!(true));
    json!({"ok": ok, "scenarios": out})
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: uw-gen info|witness <v1.wasm> <v2.wasm> <v3.wasm> [<unchecked builds>] | traces <v1.wasm> <v2.wasm> <v3.wasm> <seed> <start> <count>";
    if args.len() < 5 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let read = |p: &str| std::fs::read(p).unwrap_or_else(|e| panic!("{p}: {e}"));
    let codes = Codes::new(read(&args[2]), read(&args[3]), read(&args[4]));
    match args[1].as_str() {
        "info" => {
            let sim = base_world(&codes);
            println!(
                "{}",
                serde_json::to_string_pretty(&json!({
                    "codes": codes.table(),
                    "sim_code_hash": sim.account(VAULT).unwrap().code_hash.to_string(),
                    "block_time_ns": SEC, "t_start": T_START.to_string(),
                }))
                .unwrap()
            );
        }
        "witness" => {
            // optional: the three builds made without overflow checks
            let unchecked = if args.len() >= 8 { Some(Codes::new(read(&args[5]), read(&args[6]), read(&args[7]))) } else { None };
            let base = base_world(&codes);
            let w = witness(&base, &codes, unchecked.as_ref());
            println!("{}", serde_json::to_string_pretty(&w).unwrap());
            if w["ok"] != json!(true) {
                std::process::exit(1);
            }
        }
        "traces" => {
            let seed: u64 = args[5].parse().unwrap();
            let start: u64 = args[6].parse().unwrap();
            let count: u64 = args[7].parse().unwrap();
            let base = base_world(&codes);
            for id in start..start + count {
                let t = run_trace(&base, &codes, seed, id);
                println!("{}", serde_json::to_string(&t).unwrap());
            }
        }
        _ => eprintln!("{usage}"),
    }
}
