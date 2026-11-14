//! Conformance harness: runs random traces of the deployed staking-pool wasm
//! (core-contracts 1cacc9d, code hash J1arLz48...) on near-contract-sim and
//! records, after every step, the raw contract state, the contract's own view
//! results and the pool account's balances. Output: one JSON line per trace.

use near_contract_sim::nearcore::near_primitives::account::Account;
use near_contract_sim::prelude::*;
use near_contract_sim::{StateRecord, nearcore};
use serde_json::{Map, Value, json};
use std::collections::BTreeSet;
use std::io::Write;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

const POOL: &str = "pool.near";
const OWNER: &str = "owner.near";
const FACTORY: &str = "factory.near";
const USERS: [&str; 6] =
    ["alice.near", "bob.near", "carol.near", "dave.near", "owner.near", "eve.near"];
const NEAR: u128 = 1_000_000_000_000_000_000_000_000;
/// Default location of the wasm (relative to the working directory); `--wasm <path>` or the
/// `POOL_WASM` environment variable override it. Its code hash must equal `WASM_HASH`.
const DEFAULT_WASM_PATH: &str = "wasm/staking_pool.wasm";
const WASM_HASH: &str = "J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY";
const EPOCH_LENGTH: u64 = 50;

// ---------------------------------------------------------------- PRNG

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
    fn u128_below(&mut self, n: u128) -> u128 {
        if n == 0 {
            return 0;
        }
        let x = ((self.next() as u128) << 64) | self.next() as u128;
        x % n
    }
    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

// ---------------------------------------------------------------- state decoding

struct Reader<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> &'a [u8] {
        let s = &self.b[self.i..self.i + n];
        self.i += n;
        s
    }
    fn u8(&mut self) -> u8 {
        self.take(1)[0]
    }
    fn u32(&mut self) -> u32 {
        u32::from_le_bytes(self.take(4).try_into().unwrap())
    }
    fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.take(8).try_into().unwrap())
    }
    fn u128(&mut self) -> u128 {
        u128::from_le_bytes(self.take(16).try_into().unwrap())
    }
    fn vec(&mut self) -> Vec<u8> {
        let n = self.u32() as usize;
        self.take(n).to_vec()
    }
    fn string(&mut self) -> String {
        String::from_utf8(self.vec()).expect("utf8")
    }
    fn done(&self) -> bool {
        self.i == self.b.len()
    }
}

fn key_string(bytes: &[u8]) -> String {
    match borsh::from_slice::<PublicKey>(bytes) {
        Ok(k) => k.to_string(),
        Err(_) => format!("raw:{}", bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()),
    }
}

/// Raw contract state (near-sdk 1.0.0 borsh layout of `StakingContract`).
fn raw_state(sim: &Sim) -> Value {
    let raw = sim.state(POOL, b"STATE").expect("STATE key");
    let mut r = Reader { b: &raw, i: 0 };
    let owner_id = r.string();
    let key = r.vec();
    let last_epoch_height = r.u64();
    let last_total_balance = r.u128();
    let total_stake_shares = r.u128();
    let total_staked_balance = r.u128();
    let numerator = r.u32();
    let denominator = r.u32();
    let _map_prefix = r.vec();
    let keys_len = r.u64();
    let keys_prefix = r.vec();
    let values_len = r.u64();
    let values_prefix = r.vec();
    let paused = r.u8() != 0;
    assert!(r.done(), "STATE has trailing bytes");
    assert_eq!(keys_len, values_len, "UnorderedMap keys/values length");
    let mut accounts = Map::new();
    for i in 0..keys_len {
        let k = [&keys_prefix[..], &i.to_le_bytes()[..]].concat();
        let v = [&values_prefix[..], &i.to_le_bytes()[..]].concat();
        let kb = sim.state(POOL, &k).expect("account key element");
        let vb = sim.state(POOL, &v).expect("account value element");
        let id = Reader { b: &kb, i: 0 }.string();
        let mut a = Reader { b: &vb, i: 0 };
        let unstaked = a.u128();
        let shares = a.u128();
        let avail = a.u64();
        assert!(a.done(), "Account has trailing bytes");
        accounts.insert(
            id,
            json!({"unstaked": unstaked.to_string(), "stake_shares": shares.to_string(),
                   "unstaked_available_epoch_height": avail}),
        );
    }
    json!({
        "owner_id": owner_id,
        "stake_public_key": key_string(&key),
        "last_epoch_height": last_epoch_height,
        "last_total_balance": last_total_balance.to_string(),
        "total_stake_shares": total_stake_shares.to_string(),
        "total_staked_balance": total_staked_balance.to_string(),
        "reward_fee_fraction": {"numerator": numerator, "denominator": denominator},
        "paused": paused,
        "accounts": Value::Object(accounts),
    })
}

fn view_value(sim: &Sim, method: &str, args: Value) -> Value {
    let v = sim.view(POOL, method, args);
    match &v.result {
        Ok(bytes) => serde_json::from_slice(bytes).unwrap_or(Value::Null),
        Err(f) => json!({"view_error": err_text(f)}),
    }
}

fn observe(sim: &Sim, ok: bool, err: Option<String>) -> Value {
    let state = raw_state(sim);
    let mut ids: BTreeSet<String> = USERS.iter().map(|s| s.to_string()).collect();
    if let Some(m) = state["accounts"].as_object() {
        ids.extend(m.keys().cloned());
    }
    let mut views = Map::new();
    for id in &ids {
        let v = view_value(sim, "get_account", json!({"account_id": id}));
        let entry = if v.get("view_error").is_some() {
            v
        } else {
            json!({"unstaked_balance": v["unstaked_balance"], "staked_balance": v["staked_balance"],
                   "can_withdraw": v["can_withdraw"]})
        };
        views.insert(id.clone(), entry);
    }
    let acc = sim.account(POOL).expect("pool account");
    json!({
        "ok": ok,
        "err": err,
        "state": state,
        "views": Value::Object(views),
        "total_staked_view": view_value(sim, "get_total_staked_balance", json!({})),
        "num_accounts": view_value(sim, "get_number_of_accounts", json!({})),
        "owner_view": view_value(sim, "get_owner_id", json!({})),
        "fee_view": view_value(sim, "get_reward_fee_fraction", json!({})),
        "key_view": view_value(sim, "get_staking_key", json!({})),
        "paused_view": view_value(sim, "is_staking_paused", json!({})),
        "env": {"amount": acc.amount.as_yoctonear().to_string(),
                "locked": acc.locked.as_yoctonear().to_string(),
                "epoch": sim.epoch_height(), "height": sim.height(),
                "storage_usage": acc.storage_usage},
    })
}

fn err_text(f: &Failure) -> String {
    match f {
        Failure::Panic(m) => m.clone(),
        Failure::Host(m) => m.clone(),
        other => format!("{other} | {other:?}"),
    }
}

// ---------------------------------------------------------------- amounts

fn near_scale(rng: &mut Rng) -> u128 {
    rng.u128_below(1000) * NEAR + rng.u128_below(NEAR)
}

fn deposit_amount(rng: &mut Rng) -> u128 {
    match rng.below(12) {
        0 => 0,
        1 | 2 => rng.u128_below(1000) + 1,
        3 => rng.u128_below(1_000_000_000_000_000),
        4..=8 => near_scale(rng),
        9 => rng.u128_below(100_000) * NEAR + rng.u128_below(NEAR),
        _ => (rng.u128_below(10) + 1) * NEAR,
    }
}

/// An amount near `x` (a balance the actor currently has), or a random one.
fn around(rng: &mut Rng, x: u128) -> u128 {
    match rng.below(12) {
        0 | 1 => x,
        2 => x.saturating_add(1),
        3 => x.saturating_sub(1),
        4 => x / 2,
        5 => 0,
        6 => rng.u128_below(1000) + 1,
        7 => rng.u128_below(1_000_000_000_000),
        8 => rng.u128_below(x.max(1)),
        9 => near_scale(rng),
        10 => x.saturating_add(rng.u128_below(1000)),
        _ => x,
    }
}

fn view_amount(obs: &Value, id: &str, field: &str) -> u128 {
    obs["views"][id][field].as_str().and_then(|s| s.parse().ok()).unwrap_or(0)
}

// ---------------------------------------------------------------- traces

struct Keys {
    valid: Vec<String>,
    invalid: String,
}

fn keys() -> Keys {
    let valid = (0..3)
        .map(|i| SecretKey::from_seed(KeyType::ED25519, &format!("pool-key-{i}")).public_key())
        .map(|k| k.to_string())
        .collect();
    let invalid =
        SecretKey::from_seed(KeyType::SECP256K1, "pool-key-secp").public_key().to_string();
    Keys { valid, invalid }
}

fn random_fee(rng: &mut Rng, allow_invalid: bool) -> (u32, u32) {
    if allow_invalid && rng.chance(25) {
        return if rng.chance(50) {
            (rng.below(5) as u32, 0)
        } else {
            let d = *rng.pick(&[1u32, 10, 100, 4_294_967_294]);
            (d + 1, d)
        };
    }
    let d = *rng.pick(&[1u32, 3, 7, 10, 100, 1000, 10007, 4_294_967_295]);
    let n = match rng.below(5) {
        0 => 0,
        1 => d,
        _ => rng.below(d as u64 + 1) as u32,
    };
    (n, d)
}

enum Plan {
    Call { pred: String, method: String, args: Value, deposit: u128 },
    Epochs(u64),
    Reward(u128),
}

const PAYABLE: [&str; 2] = ["deposit", "deposit_and_stake"];

/// Mostly an actor whose `field` view is positive (so the call has something
/// to act on), else any actor.
fn holder(rng: &mut Rng, last: &Value, field: &str) -> String {
    let with: Vec<&str> =
        USERS.iter().copied().filter(|u| view_amount(last, u, field) > 0).collect();
    if !with.is_empty() && rng.chance(75) {
        rng.pick(&with).to_string()
    } else {
        rng.pick(&USERS).to_string()
    }
}

fn plan(rng: &mut Rng, last: &Value, keys: &Keys) -> Plan {
    let delegator = |rng: &mut Rng| rng.pick(&USERS).to_string();
    let owner_pred = |rng: &mut Rng| {
        if rng.chance(80) { OWNER.to_string() } else { rng.pick(&USERS).to_string() }
    };
    // (weight, op)
    let table: [(u64, &str); 18] = [
        (12, "deposit"),
        (12, "deposit_and_stake"),
        (8, "withdraw"),
        (6, "withdraw_all"),
        (8, "stake"),
        (5, "stake_all"),
        (8, "unstake"),
        (6, "unstake_all"),
        (5, "ping"),
        (2, "pause_staking"),
        (2, "resume_staking"),
        (3, "update_reward_fee_fraction"),
        (2, "update_staking_key"),
        (2, "vote"),
        (1, "on_stake_action"),
        (1, "new"),
        (11, "env_epochs"),
        (2, "env_reward"),
    ];
    let total: u64 = table.iter().map(|(w, _)| w).sum();
    let mut x = rng.below(total);
    let mut op = table[0].1;
    for (w, o) in table {
        if x < w {
            op = o;
            break;
        }
        x -= w;
    }
    let (pred, args) = match op {
        "env_epochs" => {
            let n = *rng.pick(&[1u64, 1, 1, 2, 3, 3, 4, 4, 5, 6]);
            return Plan::Epochs(n);
        }
        "env_reward" => {
            let r = match rng.below(3) {
                0 => rng.u128_below(1_000_000) + 1,
                1 => rng.u128_below(NEAR) | 1,
                _ => rng.u128_below(50 * NEAR) | 1,
            };
            return Plan::Reward(r);
        }
        "deposit" | "deposit_and_stake" | "ping" | "on_stake_action" => (delegator(rng), json!({})),
        "withdraw_all" | "stake_all" => (holder(rng, last, "unstaked_balance"), json!({})),
        "unstake_all" => (holder(rng, last, "staked_balance"), json!({})),
        "withdraw" => {
            let p = holder(rng, last, "unstaked_balance");
            let a = around(rng, view_amount(last, &p, "unstaked_balance"));
            (p, json!({"amount": a.to_string()}))
        }
        "stake" => {
            let p = holder(rng, last, "unstaked_balance");
            let a = around(rng, view_amount(last, &p, "unstaked_balance"));
            (p, json!({"amount": a.to_string()}))
        }
        "unstake" => {
            let p = holder(rng, last, "staked_balance");
            let a = around(rng, view_amount(last, &p, "staked_balance"));
            (p, json!({"amount": a.to_string()}))
        }
        "pause_staking" | "resume_staking" => (owner_pred(rng), json!({})),
        "update_reward_fee_fraction" => {
            let (n, d) = random_fee(rng, true);
            (owner_pred(rng), json!({"reward_fee_fraction": {"numerator": n, "denominator": d}}))
        }
        "update_staking_key" => {
            let k = if rng.chance(25) { keys.invalid.clone() } else { rng.pick(&keys.valid).clone() };
            (owner_pred(rng), json!({"stake_public_key": k}))
        }
        "vote" => {
            let v = *rng.pick(&["vote.near", "owner.near", "A!", "x", "a-.near", "voting.poolv1.near"]);
            (owner_pred(rng), json!({"voting_account_id": v, "is_vote": rng.chance(50)}))
        }
        "new" => (
            delegator(rng),
            json!({"owner_id": "eve.near", "stake_public_key": keys.valid[0],
                   "reward_fee_fraction": {"numerator": 1, "denominator": 10}}),
        ),
        _ => unreachable!(),
    };
    let deposit = if PAYABLE.contains(&op) {
        deposit_amount(rng)
    } else if rng.chance(3) {
        1
    } else {
        0
    };
    Plan::Call { pred, method: op.to_string(), args, deposit }
}

fn pool_env(sim: &Sim) -> (u128, u128) {
    let a = sim.account(POOL).expect("pool");
    (a.amount.as_yoctonear(), a.locked.as_yoctonear())
}

/// Runs one call to the pool and settles. Returns (ok, err, epoch the
/// function call ran in, crossed: whether the chain left that epoch while
/// the call's receipts ran).
fn run_call(sim: &mut Sim, pred: &str, method: &str, args: &Value, deposit: u128)
    -> (bool, Option<String>, u64, bool) {
    let out = sim
        .call(pred, POOL, method)
        .args_json(args)
        .deposit(Balance::from_yoctonear(deposit))
        .gas(Gas::from_teragas(300))
        .transact();
    sim.settle();
    let fc = match out.first_call() {
        Some(fc) => fc.clone(),
        None => {
            let f = out.failure().map(|f| err_text(&f)).unwrap_or_else(|| "no receipt".into());
            return (false, Some(format!("TX-NOT-CONVERTED: {f}")), sim.epoch_height(), false);
        }
    };
    let epoch = sim.epoch_of(fc.block_height);
    let crossed = sim.epoch_height() != epoch;
    match fc.failure() {
        None => (true, None, epoch, crossed),
        Some(f) => (false, Some(err_text(&f)), epoch, crossed),
    }
}

/// Forces pool.near's liquid balance below what `pred` is about to withdraw,
/// if that withdraw would otherwise reach its transfer. Returns the kind.
fn inject_fault(sim: &mut Sim, rng: &mut Rng, last: &Value, pred: &str, method: &str, args: &Value)
    -> Option<&'static str> {
    let acct = &last["state"]["accounts"][pred];
    let unstaked: u128 = acct["unstaked"].as_str().and_then(|s| s.parse().ok()).unwrap_or(0);
    let avail = acct["unstaked_available_epoch_height"].as_u64().unwrap_or(0);
    let w: u128 = if method == "withdraw_all" {
        unstaked
    } else {
        args["amount"].as_str().and_then(|s| s.parse().ok()).unwrap_or(0)
    };
    if w == 0 || w > unstaked || avail > sim.epoch_height() {
        return None; // fails before the transfer anyway
    }
    let a = sim.account(POOL).unwrap();
    let (amount, locked) = (a.amount.as_yoctonear(), a.locked.as_yoctonear());
    let storage = sim.storage_cost(a.storage_usage).as_yoctonear();
    let top = w.min(amount); // the new liquid balance stays < w and < amount
    let hold = locked > 0 && rng.chance(67);
    let lo = if hold { 0 } else { storage.saturating_sub(locked) };
    if lo >= top {
        return None;
    }
    let new_amount = lo + rng.u128_below(top - lo);
    if hold {
        let account = sim
            .state_records([POOL])
            .into_iter()
            .find_map(|r| match r {
                StateRecord::Account { account, .. } => Some(account),
                _ => None,
            })
            .expect("pool account record");
        let moved = amount - new_amount;
        let new = Account::new(
            Balance::from_yoctonear(new_amount),
            account.locked().checked_add(Balance::from_yoctonear(moved)).unwrap(),
            account.contract().into_owned(),
            account.storage_usage(),
        );
        sim.apply_state_records([StateRecord::Account { account_id: POOL.parse().unwrap(), account: new }]);
        Some("hold")
    } else {
        sim.set_balance(POOL, Balance::from_yoctonear(new_amount));
        Some("drain")
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Family {
    /// The protocol model's environment: the default 1000-trace run.
    Normal,
    /// Before some withdraws, the pool's liquid balance is forced below the
    /// amount (outside the protocol model): "hold" moves it to locked (a
    /// protocol that has not released the stake; total kept), "drain" lowers
    /// it with `set_balance` (total lost, kept lowered).
    Faults,
    /// Balances near 2^128: three users hold ~1.1e38 yocto each and deposit
    /// most of it; arguments include u128::MAX; injections fill the headroom.
    Overflow,
}

impl Family {
    fn name(self) -> &'static str {
        match self {
            Family::Normal => "normal",
            Family::Faults => "faults",
            Family::Overflow => "overflow",
        }
    }
}

const BIG_USERS: [&str; 3] = ["alice.near", "bob.near", "carol.near"];

/// u128::MAX minus everything the known accounts hold, minus a margin: what
/// can still be minted without the chain's total supply passing u128::MAX.
fn headroom(sim: &Sim) -> u128 {
    let mut held: u128 = 0;
    for id in USERS.iter().copied().chain([FACTORY, POOL, "validator.near"]) {
        if let Some(a) = sim.account(id) {
            held = held.saturating_add(a.amount.as_yoctonear()).saturating_add(a.locked.as_yoctonear());
        }
    }
    u128::MAX.saturating_sub(held).saturating_sub(1_000_000_000_000 * NEAR)
}

fn run_trace(id: u64, seed: u64, steps_min: u64, steps_max: u64, wasm: &[u8], family: Family)
    -> Value {
    let mut rng = Rng(seed);
    let keys = keys();
    let mut sim = Sim::new();
    sim.config.epoch_length = EPOCH_LENGTH;
    let big = family == Family::Overflow;
    let reward = if big {
        0
    } else if rng.chance(30) {
        0
    } else {
        match rng.below(3) {
            0 => rng.u128_below(1_000_000_000) | 1,
            1 => rng.u128_below(NEAR / 1000) | 1,
            _ => rng.u128_below(NEAR) | 1,
        }
    };
    sim.config.epoch_reward = Balance::from_yoctonear(reward);
    // ~10% of traces: a minimum stake, so some stake actions fail and the
    // pool's on_stake_action callback unstakes (exercises the env path).
    let minimum_stake = if rng.chance(10) { (10 + rng.u128_below(60)) * NEAR } else { 0 };
    sim.config.minimum_stake = Balance::from_yoctonear(minimum_stake);
    for u in USERS {
        let b = if big && BIG_USERS.contains(&u) {
            // 3 x (1.0e38 + up to 1.2e37) < u128::MAX ~ 3.4028e38
            100_000_000_000_000 * NEAR + rng.u128_below(12_000_000_000_000 * NEAR)
        } else {
            1_000_000_000 * NEAR
        };
        sim.create_account(u, Balance::from_yoctonear(b));
    }
    sim.create_account(FACTORY, Balance::from_near(100));
    let pool_balance = (5 + rng.u128_below(56)) * NEAR + rng.u128_below(NEAR);
    sim.create_account(POOL, Balance::from_yoctonear(pool_balance));
    sim.deploy(POOL, wasm.to_vec());
    sim.settle();

    // init
    let (fn_, fd) = random_fee(&mut rng, false);
    let k0 = rng.pick(&keys.valid).clone();
    let init_args = json!({"owner_id": OWNER, "stake_public_key": k0,
                           "reward_fee_fraction": {"numerator": fn_, "denominator": fd}});
    let (a0, l0) = pool_env(&sim);
    let (ok, err, epoch, crossed) = run_call(&mut sim, FACTORY, "new", &init_args, 0);
    assert!(ok, "init failed: {err:?}");
    let init_obs = observe(&sim, ok, err);
    let init = json!({"pred": FACTORY, "owner": OWNER, "key": k0,
                      "fee": {"numerator": fn_, "denominator": fd},
                      "epoch": epoch, "balance": a0.to_string(), "locked": l0.to_string(),
                      "crossed": crossed, "sim": init_obs.clone()});

    let n_steps = steps_min + rng.below(steps_max - steps_min + 1);
    let mut steps = Vec::new();
    let mut last = init_obs;
    let mut i = 0;
    while i < n_steps {
        let p = plan(&mut rng, &last, &keys);
        // A call must not straddle an epoch boundary.
        if let Plan::Call { .. } = p {
            if sim.height() + 8 >= sim.epoch_start(sim.epoch_height() + 1) {
                let target = sim.epoch_start(sim.epoch_height() + 1);
                sim.advance_to(target);
                last = observe(&sim, true, None);
                steps.push(json!({"kind": "env", "what": "epochs", "n": 1, "amount": "0",
                                  "forced": true, "sim": last.clone()}));
            }
        }
        match p {
            Plan::Epochs(n) => {
                let target = sim.epoch_start(sim.epoch_height() + n);
                sim.advance_to(target);
                last = observe(&sim, true, None);
                steps.push(json!({"kind": "env", "what": "epochs", "n": n, "amount": "0",
                                  "sim": last.clone()}));
            }
            Plan::Reward(r) => {
                let r = if big {
                    let h = headroom(&sim);
                    if rng.chance(50) { h } else { rng.u128_below(h) | 1 }
                } else {
                    r
                };
                if r == 0 {
                    continue;
                }
                let (_, locked) = pool_env(&sim);
                let books: u128 =
                    last["state"]["total_staked_balance"].as_str().unwrap().parse().unwrap();
                if locked == 0 || locked > books {
                    // Injecting stake into an unstaked account would make it a
                    // validator the pool never asked to be; injecting while a
                    // stake is being returned adds locked balance that is
                    // neither a requested stake nor a reward of a continuing
                    // one (nearcore pays a leaving stake's rewards liquid).
                    // Both are outside the protocol model; skip.
                    continue;
                }
                let recs = sim.state_records([POOL]);
                let account = recs
                    .into_iter()
                    .find_map(|r| match r {
                        StateRecord::Account { account, .. } => Some(account),
                        _ => None,
                    })
                    .expect("pool account record");
                let new = Account::new(
                    account.amount(),
                    account.locked().checked_add(Balance::from_yoctonear(r)).unwrap(),
                    account.contract().into_owned(),
                    account.storage_usage(),
                );
                sim.apply_state_records([StateRecord::Account {
                    account_id: POOL.parse().unwrap(),
                    account: new,
                }]);
                last = observe(&sim, true, None);
                steps.push(json!({"kind": "env", "what": "reward", "n": 0, "amount": r.to_string(),
                                  "sim": last.clone()}));
            }
            Plan::Call { pred, method, mut args, mut deposit } => {
                if big {
                    // Most of the predecessor's liquid balance (minus a gas
                    // reserve), and amounts at the u128 edge.
                    let liquid = sim.balance(pred.as_str()).as_yoctonear();
                    let spendable = liquid.saturating_sub(1000 * NEAR);
                    if PAYABLE.contains(&method.as_str()) && rng.chance(60) {
                        deposit = if rng.chance(50) { spendable } else { rng.u128_below(spendable + 1) };
                    }
                    // never more than the signer can pay (a refused transaction
                    // is not a contract call)
                    deposit = deposit.min(spendable);
                    if args.get("amount").is_some() && rng.chance(30) {
                        let edge = [u128::MAX, u128::MAX - 1, 1u128 << 127, (1u128 << 127) + 1];
                        args = json!({"amount": rng.pick(&edge).to_string()});
                    }
                }
                let mut fault: Option<&str> = None;
                if family == Family::Faults
                    && (method == "withdraw" || method == "withdraw_all")
                    && rng.chance(33)
                {
                    fault = inject_fault(&mut sim, &mut rng, &last, &pred, &method, &args);
                    if fault.is_some() {
                        deposit = 0;
                    }
                }
                let (a0, l0) = pool_env(&sim);
                let (ok, err, epoch, crossed) = run_call(&mut sim, &pred, &method, &args, deposit);
                last = observe(&sim, ok, err);
                let mut step = json!({"kind": "call", "pred": pred, "method": method, "args": args,
                                  "deposit": deposit.to_string(), "epoch": epoch,
                                  "balance": (a0 + deposit).to_string(), "locked": l0.to_string(),
                                  "crossed": crossed, "sim": last.clone()});
                if let Some(kind) = fault {
                    step["fault"] = json!(true);
                    step["fault_kind"] = json!(kind);
                }
                steps.push(step);
            }
        }
        i += 1;
    }
    // Overflow family, 1 trace in 3: push the pool's amount + locked past
    // u128::MAX (outside any real chain: NEAR's total supply is ~1.2e33), the
    // only way the contract's own `locked + balance` in ping can overflow;
    // then a new epoch and a few calls.
    if big && rng.chance(33) {
        let (_, locked) = pool_env(&sim);
        let over = u128::MAX - locked + 1 + rng.u128_below(1_000_000 * NEAR);
        sim.set_balance(POOL, Balance::from_yoctonear(over));
        last = observe(&sim, true, None);
        steps.push(json!({"kind": "env", "what": "overflow", "n": 0, "amount": over.to_string(),
                          "fault": true, "sim": last.clone()}));
        let target = sim.epoch_start(sim.epoch_height() + 1);
        sim.advance_to(target);
        last = observe(&sim, true, None);
        steps.push(json!({"kind": "env", "what": "epochs", "n": 1, "amount": "0", "sim": last.clone()}));
        for (pred, method, args, deposit) in [
            ("alice.near", "ping", json!({}), 0u128),
            ("bob.near", "deposit", json!({}), 1u128),
            ("carol.near", "withdraw_all", json!({}), 0u128),
            ("owner.near", "pause_staking", json!({}), 0u128),
        ] {
            let (a0, l0) = pool_env(&sim);
            let (ok, err, epoch, crossed) = run_call(&mut sim, pred, method, &args, deposit);
            last = observe(&sim, ok, err);
            steps.push(json!({"kind": "call", "pred": pred, "method": method, "args": args,
                              "deposit": deposit.to_string(), "epoch": epoch,
                              "balance": a0.saturating_add(deposit).to_string(), "locked": l0.to_string(),
                              "crossed": crossed, "sim": last.clone()}));
        }
    }
    let mut valid_keys = keys.valid.clone();
    valid_keys.sort();
    json!({"id": id, "seed": seed, "family": family.name(), "epoch_length": EPOCH_LENGTH,
           "epoch_reward": reward.to_string(), "minimum_stake": minimum_stake.to_string(),
           "pool_initial_balance": pool_balance.to_string(),
           "valid_keys": valid_keys, "invalid_keys": [keys.invalid],
           "init": init, "steps": steps})
}

// ---------------------------------------------------------------- main

fn arg<T: std::str::FromStr>(args: &[String], name: &str, default: T) -> T {
    match args.iter().position(|a| a == name) {
        Some(i) => args[i + 1].parse().ok().unwrap_or_else(|| panic!("bad value for {name}")),
        None => default,
    }
}

/// One-off: what the runtime does when the pool's amount + locked passes
/// u128::MAX (the only way the contract's `locked + balance` in ping could
/// overflow). Prints what happened.
fn probe_overflow(wasm: &[u8]) {
    let mut sim = Sim::new();
    sim.config.epoch_length = EPOCH_LENGTH;
    sim.create_account("alice.near", Balance::from_near(1000));
    sim.create_account(FACTORY, Balance::from_near(100));
    sim.create_account(POOL, Balance::from_near(30));
    sim.deploy(POOL, wasm.to_vec());
    sim.settle();
    let k = keys().valid[0].clone();
    let init = json!({"owner_id": OWNER, "stake_public_key": k,
                      "reward_fee_fraction": {"numerator": 1, "denominator": 10}});
    println!("init: {:?}", run_call(&mut sim, FACTORY, "new", &init, 0));
    println!("deposit_and_stake: {:?}",
             run_call(&mut sim, "alice.near", "deposit_and_stake", &json!({}), 10 * NEAR));
    let a = sim.account(POOL).unwrap();
    let locked = a.locked.as_yoctonear();
    for (label, amount) in [("amount+locked = MAX", u128::MAX - locked),
                            ("amount+locked = MAX+5", u128::MAX - locked + 5)] {
        let mut s2 = sim.clone();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            s2.set_balance(POOL, Balance::from_yoctonear(amount));
            let target = s2.epoch_start(s2.epoch_height() + 1);
            s2.advance_to(target);
            let p = run_call(&mut s2, "alice.near", "ping", &json!({}), 0);
            let a = s2.account(POOL).unwrap();
            (p, a.amount.as_yoctonear(), a.locked.as_yoctonear())
        }));
        match r {
            Ok(v) => println!("{label}: ping -> {v:?}"),
            Err(e) => {
                let msg = e.downcast_ref::<String>().cloned()
                    .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default();
                println!("{label}: SIM PANIC {}", &msg[..msg.len().min(600)]);
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let normal: u64 = arg(&args, "--traces", 3);
    let faults: u64 = arg(&args, "--faults", 0);
    let overflow: u64 = arg(&args, "--overflow", 0);
    let traces = normal + faults + overflow;
    let steps_min: u64 = arg(&args, "--steps-min", 30);
    let steps_max: u64 = arg(&args, "--steps-max", 80);
    let threads: usize = arg(&args, "--threads", 8);
    let seed: u64 = arg(&args, "--seed", 1);
    let start: u64 = arg(&args, "--start-id", 0);
    let out: String = arg(&args, "--out", "out/traces.jsonl".to_string());

    let wasm_path: String = arg(
        &args,
        "--wasm",
        std::env::var("POOL_WASM").unwrap_or_else(|_| DEFAULT_WASM_PATH.to_string()),
    );
    let wasm = std::fs::read(&wasm_path).unwrap_or_else(|e| panic!("read wasm {wasm_path}: {e}"));
    let hash = nearcore::near_primitives::hash::CryptoHash::hash_bytes(&wasm).to_string();
    eprintln!("wasm {} bytes, sha256 (base58) {}", wasm.len(), hash);
    assert_eq!(hash, WASM_HASH, "deployed code hash mismatch");
    if args.iter().any(|a| a == "--probe-overflow") {
        probe_overflow(&wasm);
        return;
    }

    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<String>>> = Mutex::new(vec![None; traces as usize]);
    let errors: Mutex<Vec<String>> = Mutex::new(vec![]);
    let t0 = Instant::now();
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| loop {
                let k = next.fetch_add(1, Ordering::SeqCst);
                if k >= traces as usize {
                    break;
                }
                let id = start + k as u64;
                let family = if (k as u64) < normal {
                    Family::Normal
                } else if (k as u64) < normal + faults {
                    Family::Faults
                } else {
                    Family::Overflow
                };
                let tseed = Rng(seed ^ id.wrapping_mul(0x9E37_79B9_7F4A_7C15)).next();
                let t = Instant::now();
                let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    run_trace(id, tseed, steps_min, steps_max, &wasm, family)
                }));
                match r {
                    Ok(v) => {
                        let n = v["steps"].as_array().map(|s| s.len()).unwrap_or(0);
                        results.lock().unwrap()[k] = Some(v.to_string());
                        eprintln!("trace {id} ({}): {n} steps in {:.2}s", family.name(),
                                  t.elapsed().as_secs_f64());
                    }
                    Err(e) => {
                        let msg = e
                            .downcast_ref::<String>()
                            .cloned()
                            .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                            .unwrap_or_default();
                        eprintln!("trace {id}: PANIC {msg}");
                        errors.lock().unwrap().push(
                            json!({"id": id, "seed": tseed, "family": family.name(), "panic": msg})
                                .to_string(),
                        );
                    }
                }
            });
        }
    });
    let mut f = std::io::BufWriter::new(std::fs::File::create(&out).expect("create out"));
    let mut written = 0;
    for line in results.into_inner().unwrap().into_iter().flatten() {
        writeln!(f, "{line}").unwrap();
        written += 1;
    }
    let errs = errors.into_inner().unwrap();
    if !errs.is_empty() {
        let mut e = std::fs::File::create(format!("{out}.errors")).unwrap();
        for l in &errs {
            writeln!(e, "{l}").unwrap();
        }
    }
    eprintln!(
        "wrote {written} traces to {out} ({} panicked) in {:.1}s",
        errs.len(),
        t0.elapsed().as_secs_f64()
    );
}
