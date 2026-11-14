//! Conformance harness for the token deposit and withdrawal paths of the `intents.near` contract.
//!
//! Deploys the given wasm on near-contract-sim (nearcore runtime), initialises it with its own
//! `new`, and runs random multi-account traces over the NEP-141 and NEP-245 deposit/withdraw
//! paths, the internal `mt_transfer` family, the role-guarded entry points (pause, lock, forced
//! withdrawal and forced transfer, the auth-by-predecessor switch, role grants) called by holders
//! of every role and by accounts without one, and direct calls to the private callbacks. For every trace it writes one JSON line: every executed receipt with its arguments,
//! outcome, the promise results it read and the observable state after it. `scripts/monitor.py`
//! checks the traces; FORMAT.md describes the records.
//!
//! Usage:
//!   intents-gen probe  <intents.wasm> <ft.wasm> <wnear.wasm>
//!   intents-gen traces <intents.wasm> <ft.wasm> <wnear.wasm> <seed> <start> <count> [mock]
//!
//! With `mock`, `<ft.wasm>` is a token that does not follow NEP-141 (used to show that the
//! backing monitor can fire); the trace header then carries `"mock": true`.

use near_contract_sim::prelude::*;
use near_contract_sim::{ExecutionStatus, ReceiptOutcome, Token};
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// The contract under test.
const INTENTS: &str = "intents.near";
/// Reference NEP-141 token (or the mock, in mock mode).
const TOKEN: &str = "token.near";
/// The wNEAR bytes.
const WRAP: &str = "wrap.near";
/// A second deployment of the same wasm, used as the NEP-245 token contract.
const MT: &str = "mt.near";
/// Plain accounts, registered with both tokens and funded.
const USERS: [&str; 4] = ["owner.near", "alice.near", "bob.near", "carol.near"];
/// Receiver contracts: stubs whose `ft_on_transfer` / `mt_on_transfer` reply each transaction scripts.
const RECVS: [&str; 2] = ["recv1.near", "recv2.near"];
/// An account that exists but is registered with no token.
const UNREG: &str = "unreg.near";
/// No such account exists; it can still own ledger balances.
const GHOST: &str = "ghost.near";
/// Makes a private callback of the contract the `promise_then` callback of its own promise.
const EVIL: &str = "evil.near";
const PAUSER: &str = "pauser.near";
const FORCER: &str = "forcer.near";
const LOCKER: &str = "locker.near";
const ADMIN: &str = "admin.near";
/// A scripted "token": a stub that keeps no balances. Each transaction chooses what its
/// `ft_transfer` / `ft_transfer_call` return, and it calls `ft_on_transfer` when told to.
/// Nothing backs its ledger id.
const STUB: &str = "stub.near";
/// Holders of exactly one role each, so that a neighbouring role can be told from the right one.
const DAO: &str = "dao.near";
const PAUSE1: &str = "pause1.near";
const UNPAUSE1: &str = "unpause1.near";
const LOCK1: &str = "lock1.near";
const UNLOCK1: &str = "unlock1.near";
const ACCTMGR: &str = "acctmgr.near";
/// One holder for each role that guards nothing on the token paths.
const FEES1: &str = "fees1.near";
const RELAY1: &str = "relayer1.near";
const UPGR1: &str = "upgrader1.near";
const SALT1: &str = "salt1.near";
const GC1: &str = "gc1.near";
/// For every role the account that holds it and no other role.
const SINGLE: [(&str, &str); 12] = [
    ("DAO", DAO),
    ("FeesManager", FEES1),
    ("RelayerKeysManager", RELAY1),
    ("UnrestrictedWithdrawer", FORCER),
    ("PauseManager", PAUSE1),
    ("Upgrader", UPGR1),
    ("UnpauseManager", UNPAUSE1),
    ("UnrestrictedAccountLocker", LOCK1),
    ("UnrestrictedAccountUnlocker", UNLOCK1),
    ("SaltManager", SALT1),
    ("GarbageCollector", GC1),
    ("UnrestrictedAccountManager", ACCTMGR),
];
/// The role-guarded methods of the wasm (24).
const GUARDED: [&str; 24] = [
    "pa_pause_feature", "pa_unpause_feature", "force_lock_account", "force_unlock_account",
    "force_disable_auth_by_predecessor_ids", "force_enable_auth_by_predecessor_ids", "ft_force_withdraw", "mt_force_withdraw",
    "nft_force_withdraw", "mt_force_transfer", "mt_force_batch_transfer", "mt_force_transfer_call", "mt_force_batch_transfer_call",
    "set_fee", "set_fee_collector", "add_full_access_key", "delete_key", "add_relayer_key", "delete_relayer_key", "cleanup_nonces",
    "update_current_salt", "invalidate_salts", "admin_call", "upgrade",
];
/// Admin (not grantee) of the roles in `ROLEADMIN_OF`.
const ROLEADMIN: &str = "roleadmin.near";
/// Holds nothing at the start; the only account whose permissions change in a trace.
const TEMP: &str = "temp.near";
const ROLE_NAMES: [&str; 12] = [
    "DAO",
    "FeesManager",
    "RelayerKeysManager",
    "UnrestrictedWithdrawer",
    "PauseManager",
    "Upgrader",
    "UnpauseManager",
    "UnrestrictedAccountLocker",
    "UnrestrictedAccountUnlocker",
    "SaltManager",
    "GarbageCollector",
    "UnrestrictedAccountManager",
];
const ROLEADMIN_OF: [&str; 3] = ["PauseManager", "UnrestrictedWithdrawer", "UnrestrictedAccountLocker"];
/// The accounts that call role-guarded methods.
const ACTORS: [&str; 19] = [
    DAO, PAUSER, PAUSE1, UNPAUSE1, FORCER, LOCKER, LOCK1, UNLOCK1, ACCTMGR, FEES1, RELAY1, UPGR1, SALT1, GC1, ROLEADMIN, ADMIN,
    TEMP, "alice.near", UNREG,
];
/// The accounts whose lock flag and auth-by-predecessor flag the views read.
const FLAG_WATCH: [&str; 9] = [
    "owner.near", "alice.near", "bob.near", "carol.near", "recv1.near", "recv2.near", UNREG, GHOST, EVIL,
];
/// 2^128: one more than the largest `u128`.
const U128_OVER: &str = "340282366920938463463374607431768211456";

/// Methods the contract marks `#[private]`.
const PRIVATE: [&str; 9] = [
    "ft_resolve_withdraw",
    "ft_resolve_deposit",
    "do_ft_withdraw",
    "mt_resolve_withdraw",
    "mt_resolve_deposit",
    "mt_resolve_transfer",
    "do_mt_withdraw",
    "do_native_withdraw",
    "do_storage_deposit",
];
/// Further `#[private]` methods of the wasm, outside the token paths; only called directly.
const PRIVATE_MORE: [&str; 7] = [
    "do_nft_withdraw",
    "nft_resolve_deposit",
    "nft_resolve_withdraw",
    "do_auth_call",
    "do_add_relayer_key",
    "state_migrate",
    "acl_init_super_admin",
];
const PAUSE_KEYS: [&str; 6] = ["ft_on_transfer", "ft_withdraw", "mt_transfer", "mt_on_transfer", "mt_withdraw", "intents"];

fn ft_id(t: &str) -> String {
    format!("nep141:{t}")
}
fn mt_id(c: &str, t: &str) -> String {
    format!("nep245:{c}:{t}")
}

/// A ledger token id whose balance is held for the contract by another contract.
#[derive(Clone)]
struct Asset {
    ledger: String,
    contract: &'static str,
    /// The token id inside a NEP-245 contract; `None` for a NEP-141 token.
    inner: Option<String>,
}

struct Cfg {
    assets: Vec<Asset>,
    /// Every ledger token id a trace can create: the assets, then ids that no contract backs.
    ids: Vec<String>,
    holders: Vec<String>,
    mock: bool,
}

fn cfg(mock: bool) -> Cfg {
    let assets = vec![
        Asset { ledger: ft_id(TOKEN), contract: TOKEN, inner: None },
        Asset { ledger: ft_id(WRAP), contract: WRAP, inner: None },
        Asset { ledger: mt_id(MT, &ft_id(TOKEN)), contract: MT, inner: Some(ft_id(TOKEN)) },
        Asset { ledger: mt_id(MT, &ft_id(WRAP)), contract: MT, inner: Some(ft_id(WRAP)) },
    ];
    let mut ids: Vec<String> = assets.iter().map(|a| a.ledger.clone()).collect();
    ids.extend([ft_id("alice.near"), ft_id("bob.near"), mt_id("alice.near", "x"), ft_id(STUB)]);
    let mut holders: Vec<String> = USERS.iter().chain(RECVS.iter()).map(|s| s.to_string()).collect();
    for a in [UNREG, GHOST, EVIL, PAUSER, FORCER, LOCKER, ADMIN, INTENTS, TOKEN, WRAP, MT] {
        holders.push(a.to_string());
    }
    Cfg { assets, ids, holders, mock }
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

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn evil_wat() -> String {
    let mut data = String::new();
    let mut funcs = String::new();
    let mut off = 64;
    for m in PRIVATE {
        data += &format!("  (data (i32.const {off}) \"{m}\")\n");
        for (pre, ok) in [("f", 0), ("s", 1)] {
            funcs += &format!(
                "  (func (export \"{pre}_{m}\") (call $go (i64.const {ok}) (i64.const {off}) (i64.const {})))\n",
                m.len()
            );
        }
        off += m.len();
    }
    assert!(off < 512);
    format!(
        r#"(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "current_account_id" (func $current_account_id (param i64)))
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (import "env" "promise_create" (func $promise_create (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $promise_then (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_return" (func $promise_return (param i64)))
  (memory (export "memory") 1)
  (data (i32.const 0) "{intents}")
{data}  (data (i32.const 512) "nope")
  (data (i32.const 520) "yes")
  (data (i32.const 528) "\"0\"")
  (func $go (param $ok i64) (param $moff i64) (param $mlen i64)
    (local $p1 i64) (local $inlen i64) (local $melen i64)
    (call $input (i64.const 0))
    (local.set $inlen (call $register_len (i64.const 0)))
    (call $read_register (i64.const 0) (i64.const 2048))
    (call $current_account_id (i64.const 1))
    (local.set $melen (call $register_len (i64.const 1)))
    (call $read_register (i64.const 1) (i64.const 1024))
    (local.set $p1 (call $promise_create (local.get $melen) (i64.const 1024)
      (select (i64.const 3) (i64.const 4) (i64.ne (local.get $ok) (i64.const 0)))
      (select (i64.const 520) (i64.const 512) (i64.ne (local.get $ok) (i64.const 0)))
      (i64.const 0) (i64.const 0) (i64.const 600) (i64.const 5000000000000)))
    (call $promise_return (call $promise_then (local.get $p1) (i64.const {len}) (i64.const 0)
      (local.get $mlen) (local.get $moff) (local.get $inlen) (i64.const 2048) (i64.const 600)
      (i64.const 60000000000000))))
  (func (export "yes") (call $value_return (i64.const 3) (i64.const 528)))
{funcs})"#,
        intents = INTENTS,
        len = INTENTS.len()
    )
}

fn vj(sim: &Sim, id: &str, method: &str, args: Value) -> Result<Value, String> {
    let v = sim.view(id, method, args);
    match v.value() {
        Some(b) => serde_json::from_slice(b).map_err(|e| format!("{id}::{method}: not JSON: {e}")),
        None => Err(format!("{id}::{method}: {:?}", v.failure())),
    }
}

fn amt(v: &Value) -> u128 {
    v.as_str().and_then(|s| s.parse().ok()).unwrap_or(0)
}

/// The role table (`acl_get_permissioned_accounts`), empty sets left out.
#[derive(Clone, Default, PartialEq, Debug)]
struct Acl {
    super_admins: BTreeSet<String>,
    admins: BTreeMap<String, BTreeSet<String>>,
    grantees: BTreeMap<String, BTreeSet<String>>,
}

impl Acl {
    fn json(&self) -> Value {
        json!({"super_admins": self.super_admins, "admins": self.admins, "grantees": self.grantees})
    }
    fn set(map: &mut BTreeMap<String, BTreeSet<String>>, role: &str, who: &str, on: bool) {
        if on {
            map.entry(role.to_string()).or_default().insert(who.to_string());
        } else if let Some(m) = map.get_mut(role) {
            m.remove(who);
            if m.is_empty() {
                map.remove(role);
            }
        }
    }
}

/// What the views show.
#[derive(Clone, Default, PartialEq, Debug)]
struct State {
    /// ledger token id -> account -> balance (`mt_balance_of`), nonzero entries only.
    ledger: BTreeMap<String, BTreeMap<String, u128>>,
    /// ledger token id -> `mt_supply`, nonzero entries only.
    supply: BTreeMap<String, u128>,
    /// asset ledger id -> what the token contract says the contract holds, nonzero entries only.
    held: BTreeMap<String, u128>,
    paused: BTreeSet<String>,
    locked: BTreeSet<String>,
    /// Accounts of `FLAG_WATCH` with authentication by predecessor id disabled.
    auth_off: BTreeSet<String>,
    acl: Acl,
}

impl State {
    fn json(&self) -> Value {
        let m = |x: &BTreeMap<String, u128>| -> Value {
            Value::Object(x.iter().map(|(k, v)| (k.clone(), json!(v.to_string()))).collect())
        };
        json!({
            "ledger": Value::Object(self.ledger.iter().map(|(k, v)| (k.clone(), m(v))).collect()),
            "supply": m(&self.supply),
            "held": m(&self.held),
            "paused": self.paused,
            "locked": self.locked,
            "auth_off": self.auth_off,
            "acl": self.acl.json(),
        })
    }
}

fn bump(map: &mut BTreeMap<String, u128>, key: &str, neg: bool, abs: u128) -> bool {
    let cur = map.get(key).copied().unwrap_or(0);
    let new = if neg { cur.checked_sub(abs) } else { cur.checked_add(abs) };
    match new {
        Some(0) => {
            map.remove(key);
            true
        }
        Some(n) => {
            map.insert(key.to_string(), n);
            true
        }
        None => false,
    }
}

/// Reads the state through views. The second value lists every ledger token id the contract
/// enumerates (`mt_tokens`) and errors of views.
fn observe(sim: &Sim, c: &Cfg) -> (State, Vec<String>, Vec<String>) {
    let mut st = State::default();
    let mut errs = vec![];
    for a in &c.holders {
        match vj(sim, INTENTS, "mt_batch_balance_of", json!({"account_id": a, "token_ids": c.ids})) {
            Ok(Value::Array(v)) if v.len() == c.ids.len() => {
                for (tid, x) in c.ids.iter().zip(v.iter()) {
                    let n = amt(x);
                    if n > 0 {
                        st.ledger.entry(tid.clone()).or_default().insert(a.clone(), n);
                    }
                }
            }
            other => errs.push(format!("mt_batch_balance_of({a}): {other:?}")),
        }
    }
    match vj(sim, INTENTS, "mt_batch_supply", json!({"token_ids": c.ids})) {
        Ok(Value::Array(v)) if v.len() == c.ids.len() => {
            for (tid, x) in c.ids.iter().zip(v.iter()) {
                let n = amt(x);
                if n > 0 {
                    st.supply.insert(tid.clone(), n);
                }
            }
        }
        other => errs.push(format!("mt_batch_supply: {other:?}")),
    }
    for a in &c.assets {
        let r = match &a.inner {
            None => vj(sim, a.contract, "ft_balance_of", json!({"account_id": INTENTS})),
            Some(t) => vj(sim, a.contract, "mt_balance_of", json!({"account_id": INTENTS, "token_id": t})),
        };
        match r {
            Ok(v) => {
                let n = amt(&v);
                if n > 0 {
                    st.held.insert(a.ledger.clone(), n);
                }
            }
            Err(e) => errs.push(e),
        }
    }
    match vj(sim, INTENTS, "pa_all_paused", json!({})) {
        Ok(Value::Array(v)) => st.paused = v.iter().filter_map(|x| x.as_str().map(String::from)).collect(),
        Ok(Value::Null) => {}
        other => errs.push(format!("pa_all_paused: {other:?}")),
    }
    for a in FLAG_WATCH {
        match vj(sim, INTENTS, "is_account_locked", json!({"account_id": a})) {
            Ok(Value::Bool(true)) => {
                st.locked.insert(a.to_string());
            }
            Ok(Value::Bool(false)) => {}
            other => errs.push(format!("is_account_locked({a}): {other:?}")),
        }
        match vj(sim, INTENTS, "is_auth_by_predecessor_id_enabled", json!({"account_id": a})) {
            Ok(Value::Bool(false)) => {
                st.auth_off.insert(a.to_string());
            }
            Ok(Value::Bool(true)) => {}
            other => errs.push(format!("is_auth_by_predecessor_id_enabled({a}): {other:?}")),
        }
    }
    match vj(sim, INTENTS, "acl_get_permissioned_accounts", json!({})) {
        Ok(v) if v["roles"].is_object() => {
            let names = |x: &Value| -> BTreeSet<String> {
                x.as_array().map(|l| l.iter().filter_map(|a| a.as_str().map(String::from)).collect()).unwrap_or_default()
            };
            st.acl.super_admins = names(&v["super_admins"]);
            for (role, per) in v["roles"].as_object().unwrap() {
                for (key, map) in [("admins", &mut st.acl.admins), ("grantees", &mut st.acl.grantees)] {
                    let who = names(&per[key]);
                    if !who.is_empty() {
                        map.insert(role.clone(), who);
                    }
                }
            }
        }
        other => errs.push(format!("acl_get_permissioned_accounts: {other:?}")),
    }
    let tokens = match vj(sim, INTENTS, "mt_tokens", json!({})) {
        Ok(Value::Array(v)) => v.iter().filter_map(|t| t["token_id"].as_str().map(String::from)).collect(),
        other => {
            errs.push(format!("mt_tokens: {other:?}"));
            vec![]
        }
    };
    (st, tokens, errs)
}

/// Applies what one receipt did, as the simulator measured it with the views just before and
/// just after the receipt (balances), and as the contract's own events say (pause, lock).
fn apply(st: &mut State, r: &ReceiptOutcome, c: &Cfg) -> Vec<String> {
    let mut errs = vec![];
    for m in &r.token_moves {
        let (neg, abs) = (m.delta < 0i128, m.delta.magnitude());
        let ok = match (m.token.as_str(), &m.token_id, &m.holder) {
            (INTENTS, Some(tid), Some(h)) => {
                let e = st.ledger.entry(tid.clone()).or_default();
                let ok = bump(e, h.as_str(), neg, abs);
                let empty = e.is_empty();
                if empty {
                    st.ledger.remove(tid);
                }
                ok
            }
            (INTENTS, Some(tid), None) => bump(&mut st.supply, tid, neg, abs),
            (t, tid, Some(h)) if h.as_str() == INTENTS => {
                match c.assets.iter().find(|a| a.contract == t && a.inner == *tid) {
                    Some(a) => bump(&mut st.held, &a.ledger, neg, abs),
                    None => true,
                }
            }
            _ => true,
        };
        if !ok {
            errs.push(format!("a measured move does not fit the state in {}", r.receipt_id));
        }
    }
    if r.is_success() && r.receiver_id.as_str() == INTENTS {
        for e in events(r) {
            let (ev, data) = (e["event"].as_str().unwrap_or(""), &e["data"]);
            match (e["standard"].as_str().unwrap_or(""), ev) {
                ("Pausable", "pause") => {
                    if let Some(k) = data["key"].as_str() {
                        st.paused.insert(k.to_string());
                    }
                }
                ("Pausable", "unpause") => {
                    if let Some(k) = data["key"].as_str() {
                        st.paused.remove(k);
                    }
                }
                (_, "account_locked") => {
                    if let Some(a) = data["account_id"].as_str() {
                        st.locked.insert(a.to_string());
                    }
                }
                (_, "account_unlocked") => {
                    if let Some(a) = data["account_id"].as_str() {
                        st.locked.remove(a);
                    }
                }
                (_, "set_auth_by_predecessor_id") => {
                    if let (Some(a), Some(on)) = (data["account_id"].as_str(), data["enabled"].as_bool()) {
                        if FLAG_WATCH.contains(&a) {
                            if on {
                                st.auth_off.remove(a);
                            } else {
                                st.auth_off.insert(a.to_string());
                            }
                        }
                    }
                }
                ("AccessControllable", _) => {
                    let (role, acct) = (data["role"].as_str().unwrap_or(""), data["account"].as_str().unwrap_or(""));
                    match ev {
                        "super_admin_added" => {
                            st.acl.super_admins.insert(acct.to_string());
                        }
                        "super_admin_revoked" => {
                            st.acl.super_admins.remove(acct);
                        }
                        "admin_added" => Acl::set(&mut st.acl.admins, role, acct, true),
                        "admin_revoked" => Acl::set(&mut st.acl.admins, role, acct, false),
                        "role_granted" => Acl::set(&mut st.acl.grantees, role, data["to"].as_str().unwrap_or(""), true),
                        "role_revoked" => Acl::set(&mut st.acl.grantees, role, data["from"].as_str().unwrap_or(""), false),
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }
    errs
}

fn events(r: &ReceiptOutcome) -> Vec<Value> {
    r.logs
        .iter()
        .filter_map(|l| l.strip_prefix("EVENT_JSON:"))
        .filter_map(|j| serde_json::from_str::<Value>(j).ok())
        .collect()
}

struct World {
    sim: Sim,
    cfg: Cfg,
    /// The two NEP-141 tokens at the start of every trace (the same for all traces).
    tokens_state: Value,
    /// account -> the public keys it registered in the contract before the trace starts.
    keys: Value,
}

/// Balances, supply and registration of every holder in the NEP-141 tokens.
fn tokens_state(sim: &Sim, c: &Cfg) -> Value {
    let mut out = Map::new();
    for t in [TOKEN, WRAP] {
        let mut bals = Map::new();
        let mut reg = vec![];
        for h in &c.holders {
            let b = vj(sim, t, "ft_balance_of", json!({"account_id": h})).map(|v| amt(&v)).unwrap_or(0);
            bals.insert(h.clone(), json!(b.to_string()));
            if let Ok(v) = vj(sim, t, "storage_balance_of", json!({"account_id": h})) {
                if !v.is_null() {
                    reg.push(h.clone());
                }
            }
        }
        let supply = vj(sim, t, "ft_total_supply", json!({})).map(|v| amt(&v)).unwrap_or(0);
        out.insert(t.to_string(), json!({"supply": supply.to_string(), "balances": bals, "registered": reg}));
    }
    Value::Object(out)
}

fn must(o: TxOutcome, what: &str) {
    if !o.is_success() || o.receipts.iter().any(|r| !r.is_success() && !r.is_refund()) {
        panic!("setup step failed: {what}\n{o}");
    }
}

fn build_world(intents: &[u8], ft: &[u8], wnear: &[u8], mock: bool) -> World {
    let c = cfg(mock);
    let mut sim = Sim::new();
    for u in USERS.iter().chain([UNREG, PAUSER, FORCER, LOCKER, ADMIN].iter()) {
        sim.create_account(*u, Balance::from_near(1_000_000));
    }
    for u in [DAO, PAUSE1, UNPAUSE1, LOCK1, UNLOCK1, ACCTMGR, FEES1, RELAY1, UPGR1, SALT1, GC1, ROLEADMIN, TEMP] {
        sim.create_account(u, Balance::from_near(1_000_000));
    }
    sim.create_account(WRAP, Balance::from_near(100));
    sim.deploy(WRAP, wnear.to_vec());
    must(sim.call(WRAP, WRAP, "new").transact(), "wrap.new");
    sim.create_account(TOKEN, Balance::from_near(100));
    sim.deploy(TOKEN, ft.to_vec());
    must(
        sim.call(TOKEN, TOKEN, "new_default_meta")
            .args_json(json!({"owner_id": USERS[0], "total_supply": "1000000000000000000000000000000"}))
            .transact(),
        "token.new_default_meta",
    );
    let mut admins = Map::new();
    for r in ROLEADMIN_OF {
        admins.insert(r.to_string(), json!([ROLEADMIN]));
    }
    let roles = json!({
        "super_admins": [ADMIN],
        "admins": admins,
        "grantees": {
            "DAO": [DAO],
            "PauseManager": [PAUSER, PAUSE1], "UnpauseManager": [PAUSER, UNPAUSE1],
            "UnrestrictedWithdrawer": [FORCER],
            "UnrestrictedAccountLocker": [LOCKER, LOCK1], "UnrestrictedAccountUnlocker": [LOCKER, UNLOCK1],
            "UnrestrictedAccountManager": [ACCTMGR],
            "FeesManager": [FEES1], "RelayerKeysManager": [RELAY1], "Upgrader": [UPGR1], "SaltManager": [SALT1],
            "GarbageCollector": [GC1],
        }
    });
    for id in [INTENTS, MT] {
        sim.create_account(id, Balance::from_near(100));
        sim.deploy(id, intents.to_vec());
        must(
            sim.call(id, id, "new")
                .args_json(json!({"config": {
                    "wnear_id": WRAP, "fees": {"fee": 0, "fee_collector": ADMIN}, "roles": roles
                }}))
                .transact(),
            "new",
        );
    }
    for u in USERS {
        let pk = sim.secret_key(u).public_key().to_string();
        must(
            sim.call(u, INTENTS, "add_public_key").args_json(json!({"public_key": pk}))
                .deposit(Balance::from_yoctonear(1)).transact(),
            "add_public_key",
        );
    }
    for r in RECVS {
        sim.create_account(r, Balance::from_near(1_000_000));
        sim.deploy_stub(
            r,
            Stub::new().on("ft_on_transfer", Reply::json("0")).on("mt_on_transfer", Reply::json(["0"])),
        );
    }
    sim.create_account(EVIL, Balance::from_near(1_000));
    sim.deploy(EVIL, wat::parse_str(evil_wat()).expect("evil.wat"));
    sim.create_account(STUB, Balance::from_near(1_000_000));
    sim.deploy_stub(
        STUB,
        Stub::new()
            .on("ft_transfer", Reply::json(()))
            .on("ft_transfer_call", Reply::json("0"))
            .on("storage_deposit", Reply::json(()))
            .on("mint", Reply::json(())),
    );
    // registration with both tokens; UNREG and the role holders stay unregistered
    let wmin = vj(&sim, WRAP, "storage_balance_bounds", json!({})).ok().map(|v| amt(&v["min"])).unwrap_or(near(1) / 800);
    for who in USERS.iter().skip(1).chain(RECVS.iter()).chain([INTENTS, MT, EVIL, FORCER].iter()) {
        must(
            sim.call(USERS[0], TOKEN, "storage_deposit").args_json(json!({"account_id": who}))
                .deposit(Balance::from_near(1)).transact(),
            "token.storage_deposit",
        );
    }
    for who in USERS.iter().chain(RECVS.iter()).chain([INTENTS, MT, EVIL, FORCER].iter()) {
        must(
            sim.call(USERS[0], WRAP, "storage_deposit").args_json(json!({"account_id": who}))
                .deposit(Balance::from_yoctonear(wmin)).transact(),
            "wrap.storage_deposit",
        );
    }
    let unit: u128 = 1_000_000_000_000_000_000_000_000_000; // 1e27
    for who in USERS.iter().skip(1).chain(RECVS.iter()) {
        must(
            sim.call(USERS[0], TOKEN, "ft_transfer")
                .args_json(json!({"receiver_id": who, "amount": unit.to_string()}))
                .deposit(Balance::from_yoctonear(1)).transact(),
            "fund token",
        );
    }
    for who in USERS.iter().chain(RECVS.iter()) {
        must(sim.call(*who, WRAP, "near_deposit").deposit(Balance::from_near(1000)).transact(), "near_deposit");
    }
    // balances inside the NEP-245 contract: its own NEP-141 deposits
    for who in USERS {
        for t in [TOKEN, WRAP] {
            must(
                sim.call(who, t, "ft_transfer_call")
                    .args_json(json!({"receiver_id": MT, "amount": (unit / 10_000).to_string(), "msg": ""}))
                    .deposit(Balance::from_yoctonear(1)).transact(),
                "deposit into mt.near",
            );
        }
    }
    sim.watch(Token::nep245_ids(INTENTS, c.ids.clone()).holders([GHOST]).pure());
    sim.watch(Token::nep141(TOKEN).pure());
    sim.watch(Token::nep141(WRAP).pure());
    sim.watch(Token::nep245_ids(MT, [ft_id(TOKEN), ft_id(WRAP)]).holders([GHOST]).pure());
    sim.step();
    let tokens_state = tokens_state(&sim, &c);
    let keys = Value::Object(USERS.iter().map(|u| (u.to_string(), json!([sim.secret_key(*u).public_key().to_string()]))).collect());
    World { sim, cfg: c, tokens_state, keys }
}

/// One submitted transaction.
struct Op {
    kind: &'static str,
    signer: String,
    recv: String,
    method: String,
    args: Vec<u8>,
    deposit: u128,
    gas: Option<u64>,
    /// Scripted stub replies: (stub, method, reply, label).
    replies: Vec<(String, String, Reply, String)>,
    faults: Vec<(Receipts, Fault, String)>,
    label: String,
}

impl Op {
    fn new(kind: &'static str, signer: &str, recv: &str, method: &str, args: Value) -> Op {
        Op {
            kind,
            signer: signer.into(),
            recv: recv.into(),
            method: method.into(),
            args: serde_json::to_vec(&args).unwrap(),
            deposit: 0,
            gas: None,
            replies: vec![],
            faults: vec![],
            label: String::new(),
        }
    }
    fn dep(mut self, d: u128) -> Op {
        self.deposit = d;
        self
    }
}

fn amount_for(rng: &mut Rng, bal: u128) -> u128 {
    match rng.below(100) {
        0..=3 => 0,
        4..=23 => bal,
        24..=30 => bal.saturating_add(1),
        31..=35 => 1,
        36 => u128::MAX - 1,
        37..=38 => u128::MAX,
        _ => 1 + rng.upto(bal.saturating_sub(1)),
    }
}

fn one(rng: &mut Rng) -> u128 {
    if rng.chance(93) { 1 } else { *rng.pick(&[0u128, 2]) }
}

fn opt(v: &mut Value, key: &str, val: Option<Value>) {
    if let Some(x) = val {
        v[key] = x;
    }
}

/// A message for a deposit: who gets the ledger credit.
fn deposit_msg(rng: &mut Rng) -> String {
    let ids = [USERS[1], USERS[2], USERS[3], RECVS[0], GHOST, UNREG, INTENTS, MT, TOKEN];
    match rng.below(100) {
        0..=49 => String::new(),
        50..=69 => rng.pick(&ids).to_string(),
        70..=77 => json!({"receiver_id": rng.pick(&ids)}).to_string(),
        78..=84 => json!({"receiver_id": rng.pick(&ids), "execute_intents": [], "refund_if_fails": rng.chance(50)}).to_string(),
        _ => rng
            .pick(&[
                "Bad!Id",
                "{",
                "{\"receiver_id\":5}",
                "{\"receiver_id\":\"alice.near\",\"execute_intents\":[{\"bogus\":1}]}",
                "{\"receiver_id\":\"alice.near\",\"execute_intents\":[{\"bogus\":1}],\"refund_if_fails\":true}",
                "x",
                "UPPER.near",
                "{\"receiver_id\":\"alice.near\",\"msg\":\"hello\"}",
            ])
            .to_string(),
    }
}

/// What a NEP-141 receiver stub does when it gets `amount` of `token`; `holder` is the stub.
fn ft_reply(rng: &mut Rng, amount: u128, token: &str, holder: &str) -> (Reply, String) {
    let num = |rng: &mut Rng| -> u128 {
        match rng.below(7) {
            0 | 1 => 0,
            2 => amount,
            3 => amount / 2,
            4 => amount.saturating_add(1),
            5 => u128::MAX,
            _ => rng.upto(amount),
        }
    };
    let part = |rng: &mut Rng| -> u128 { if rng.chance(40) { amount } else { rng.upto(amount) } };
    match rng.below(100) {
        0..=31 => {
            let n = num(rng);
            (Reply::json(n.to_string()), format!("returns \"{n}\""))
        }
        32..=41 => {
            let g = *rng.pick(&["{", "abc", "5", "\"-1\"", "null", "[\"40\"]", "", "\"12a\"", "{\"x\":1}"]);
            (Reply::bytes(g.as_bytes().to_vec()), format!("returns the bytes {g:?}"))
        }
        42..=51 => (Reply::panic("receiver refuses"), "panics".into()),
        52..=61 => {
            let (to, a, n) = (*rng.pick(&USERS), part(rng), num(rng));
            (
                Reply::call(token, "ft_transfer", json!({"receiver_id": to, "amount": a.to_string()}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("sends {a} on to {to}, then returns \"{n}\""),
            )
        }
        62..=73 => {
            let (a, n, m) = (part(rng), num(rng), deposit_msg(rng));
            (
                Reply::call(token, "ft_transfer_call", json!({"receiver_id": INTENTS, "amount": a.to_string(), "msg": m}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("deposits {a} back with msg {m:?}, then returns \"{n}\""),
            )
        }
        74..=81 => {
            let (to, a, n) = (*rng.pick(&USERS), part(rng), num(rng));
            (
                Reply::call(INTENTS, "ft_withdraw", json!({"token": token, "receiver_id": to, "amount": a.to_string()}))
                    .deposit(Balance::from_yoctonear(1))
                    .then(Reply::json(n.to_string())),
                format!("calls ft_withdraw({token}, {to}, {a}) as {holder}, then returns \"{n}\""),
            )
        }
        82..=87 => {
            let n = num(rng);
            let args = json!({"token": token, "sender_id": holder, "amount": amount.to_string(), "is_call": rng.chance(50)});
            (
                Reply::call(INTENTS, "ft_resolve_withdraw", args).then(Reply::json(n.to_string())),
                format!("calls the private ft_resolve_withdraw for itself, then returns \"{n}\""),
            )
        }
        88..=93 => {
            let n = num(rng);
            (Reply::json(n), format!("returns the number {n}"))
        }
        _ => (Reply::json("0").at_limit(), "returns \"0\" padded to the return limit".into()),
    }
}

/// What a NEP-245 receiver stub answers for `amounts`.
fn mt_reply(rng: &mut Rng, amounts: &[u128]) -> (Reply, String) {
    let num = |rng: &mut Rng, a: u128| -> u128 {
        match rng.below(6) {
            0 | 1 => 0,
            2 => a,
            3 => a / 2,
            4 => a.saturating_add(1),
            _ => rng.upto(a),
        }
    };
    match rng.below(100) {
        0..=54 => {
            let v: Vec<String> = amounts.iter().map(|a| num(rng, *a).to_string()).collect();
            let l = format!("returns {v:?}");
            (Reply::json(v), l)
        }
        55..=64 => (Reply::panic("receiver refuses"), "panics".into()),
        65..=74 => {
            let g = *rng.pick(&["{", "[]", "[\"0\",\"0\",\"0\"]", "\"0\"", "null", "[5]", "", "[\"x\"]"]);
            (Reply::bytes(g.as_bytes().to_vec()), format!("returns the bytes {g:?}"))
        }
        75..=84 => {
            let v: Vec<String> = amounts.iter().map(|_| "0".to_string()).collect();
            (Reply::json(v).at_limit(), "returns zeros padded to the return limit".into())
        }
        _ => {
            let v: Vec<String> = amounts.iter().map(|a| num(rng, *a).to_string()).collect();
            let args = json!({"token": MT, "sender_id": RECVS[0], "token_ids": [ft_id(TOKEN)], "amounts": ["1"], "is_call": false});
            let l = format!("calls the private mt_resolve_withdraw, then returns {v:?}");
            (Reply::call(INTENTS, "mt_resolve_withdraw", args).then(Reply::json(v)), l)
        }
    }
}

fn ledger_of(st: &State, tid: &str, who: &str) -> u128 {
    st.ledger.get(tid).and_then(|m| m.get(who)).copied().unwrap_or(0)
}

/// An account that can sign and owns some `tid` in the ledger, or any signer.
fn owner_of(rng: &mut Rng, st: &State, tid: &str) -> &'static str {
    let signers = [USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0], RECVS[1], UNREG];
    let have: Vec<&'static str> = signers.iter().copied().filter(|s| ledger_of(st, tid, s) > 0).collect();
    if !have.is_empty() && rng.chance(88) { *rng.pick(&have) } else { *rng.pick(&signers) }
}

fn token_balance(sim: &Sim, token: &str, who: &str) -> u128 {
    vj(sim, token, "ft_balance_of", json!({"account_id": who})).map(|v| amt(&v)).unwrap_or(0)
}

/// Random delays and failures of the receipts a transaction spawns.
fn faults(rng: &mut Rng, op: &mut Op, slots: &[(Receipts, &str, bool)]) {
    for (at, name, can_fail) in slots {
        if rng.chance(14) {
            let k = 1 + rng.below(4);
            op.faults.push((at.clone(), Fault::Hold(k), format!("{name} held {k} blocks")));
        } else if *can_fail && rng.chance(5) {
            op.faults.push((at.clone(), Fault::OutOfGas, format!("{name} runs out of gas")));
        }
    }
}

/// The roles one of which a guarded method requires (contract source at 16d04f6e).
fn guard_roles(method: &str) -> &'static [&'static str] {
    match method {
        "pa_pause_feature" => &["DAO", "PauseManager"],
        "pa_unpause_feature" => &["DAO", "UnpauseManager"],
        "force_lock_account" | "force_disable_auth_by_predecessor_ids" => {
            &["DAO", "UnrestrictedAccountLocker", "UnrestrictedAccountManager"]
        }
        "force_unlock_account" | "force_enable_auth_by_predecessor_ids" => {
            &["DAO", "UnrestrictedAccountUnlocker", "UnrestrictedAccountManager"]
        }
        "ft_force_withdraw" | "mt_force_withdraw" | "nft_force_withdraw" | "mt_force_transfer" | "mt_force_batch_transfer"
        | "mt_force_transfer_call" | "mt_force_batch_transfer_call" => &["DAO", "UnrestrictedWithdrawer"],
        "upgrade" => &["DAO", "Upgrader"],
        "set_fee" | "set_fee_collector" => &["DAO", "FeesManager"],
        "add_relayer_key" | "delete_relayer_key" => &["DAO", "RelayerKeysManager"],
        "cleanup_nonces" => &["DAO", "GarbageCollector"],
        "update_current_salt" | "invalidate_salts" => &["DAO", "SaltManager"],
        _ => &["DAO"],
    }
}

fn has_any(st: &State, who: &str, roles: &[&str]) -> bool {
    roles.iter().any(|r| st.acl.grantees.get(*r).is_some_and(|s| s.contains(who)))
}

/// Who calls a guarded method: with `pct_right` percent a holder of one of the required roles (as
/// the last views show), otherwise an actor that holds none of them: a holder of other roles, an
/// admin of the role that is no grantee, the super-admin, or an account with no role.
fn pick_caller(rng: &mut Rng, st: &State, method: &str, pct_right: u64) -> &'static str {
    let need = guard_roles(method);
    let (right, wrong): (Vec<&'static str>, Vec<&'static str>) = ACTORS.iter().copied().partition(|a| has_any(st, a, need));
    if (!right.is_empty() && rng.chance(pct_right)) || wrong.is_empty() { *rng.pick(&right) } else { *rng.pick(&wrong) }
}

fn pause_op(by: &str, key: &str, pause: bool) -> Op {
    let m = if pause { "pa_pause_feature" } else { "pa_unpause_feature" };
    let mut op = Op::new(if pause { "pause" } else { "unpause" }, by, INTENTS, m, json!({"key": key}));
    op.label = format!("{by} calls {m}({key})");
    op
}

fn lock_op(by: &str, at: &str, who: &str, lock: bool) -> Op {
    let m = if lock { "force_lock_account" } else { "force_unlock_account" };
    let mut op = Op::new("lock", by, at, m, json!({"account_id": who})).dep(1);
    op.label = format!("{by} calls {at}::{m}({who})");
    op
}

/// `force_disable_auth_by_predecessor_ids` / `force_enable_auth_by_predecessor_ids`.
fn auth_force_op(by: &str, whom: &[&str], enable: bool) -> Op {
    let m = if enable { "force_enable_auth_by_predecessor_ids" } else { "force_disable_auth_by_predecessor_ids" };
    let mut op = Op::new("auth", by, INTENTS, m, json!({"account_ids": whom})).dep(1);
    op.label = format!("{by} calls {m}({whom:?})");
    op
}

fn auth_self_op(who: &str) -> Op {
    let mut op = Op::new("auth", who, INTENTS, "disable_auth_by_predecessor_id", json!({})).dep(1);
    op.label = format!("{who} disables authentication by predecessor id for itself");
    op
}

/// A near-plugins `acl_*` call. `role` and `account` are left out when the method takes none.
fn acl_op(by: &str, method: &str, role: Option<&str>, account: Option<&str>) -> Op {
    let mut args = json!({});
    opt(&mut args, "role", role.map(|r| json!(r)));
    opt(&mut args, "account_id", account.map(|a| json!(a)));
    let mut op = Op::new("acl", by, INTENTS, method, args);
    op.label = format!("{by} calls {method}({}{})", role.unwrap_or(""), account.map(|a| format!(" {a}")).unwrap_or_default());
    op
}

/// The scripted token "receives" `amount` from `who`: it calls `ft_on_transfer` of the contract.
fn stub_deposit_op(who: &str, amount: &str, msg: &str) -> Op {
    let mut op = Op::new("stub_deposit", who, STUB, "mint", json!({"amount": amount}));
    let l = format!("calls ft_on_transfer(sender {who}, amount {amount}, msg {msg:?})");
    let call = Reply::call(INTENTS, "ft_on_transfer", json!({"sender_id": who, "amount": amount, "msg": msg}));
    op.replies.push((STUB.into(), "mint".into(), call.then(Reply::json(())), l));
    op.label = format!("{who} has the scripted token notify a deposit of {amount} with msg {msg:?}");
    op
}

/// `content` padded with JSON whitespace to exactly `len` bytes (unchanged if longer).
fn padded(content: &str, len: usize, style: u64) -> Vec<u8> {
    let mut b = content.as_bytes().to_vec();
    let mut k = 0;
    while b.len() < len {
        match style {
            0 => b.push(b' '),
            1 => b.insert(0, b' '),
            _ => {
                let ws = [b' ', b'\n', b'\t', b'\r'][k % 4];
                if k % 2 == 0 { b.push(ws) } else { b.insert(0, ws) }
            }
        }
        k += 1;
    }
    b
}

/// A named answer of the scripted token to `ft_transfer_call` (`call`) or `ft_transfer`.
fn stub_reply_mode(mode: &str, amount: u128, rng: &mut Rng) -> (Reply, String) {
    let less = if amount > 1 { *rng.pick(&[amount / 2, amount - 1, 0, 1]) } else { 0 };
    let style = rng.below(3);
    let exact = |content: String, len: usize| -> (Reply, String) {
        let b = padded(&content, len, style);
        let l = format!("returns {content} padded with whitespace to {} bytes", b.len());
        (Reply::bytes(b), l)
    };
    match mode {
        "len43" => exact(format!("\"{less}\""), 43),
        "len44" => exact(format!("\"{less}\""), 44),
        "len45" => exact(format!("\"{less}\""), 45),
        "len46" => exact(format!("\"{less}\""), 46),
        "bad44" => exact((*rng.pick(&["\"x\"", "7", "{}", "\"-1\""])).to_string(), 44),
        "bad45" => exact((*rng.pick(&["\"x\"", "7", "{}", "\"-1\""])).to_string(), 45),
        "full44" => exact(format!("\"+{}\"", u128::MAX), 44),
        "over" => {
            let n = *rng.pick(&[amount.saturating_add(1), amount.saturating_mul(2), u128::MAX]);
            (Reply::json(n.to_string()), format!("returns \"{n}\" (the amount is {amount})"))
        }
        "plus" => (Reply::bytes(format!("\"+{less}\"")), format!("returns \"+{less}\"")),
        "void" => (Reply::json(()), "returns nothing".into()),
        "value" => {
            let g = *rng.pick(&["\"0\"", "true", "null", " ", "\"\"", "0", "[]", "\"1\""]);
            (Reply::bytes(g.as_bytes().to_vec()), format!("succeeds and returns the bytes {g:?}"))
        }
        "panic" => (Reply::panic("token refuses"), "panics".into()),
        "all" => (Reply::json(amount.to_string()), format!("returns \"{amount}\"")),
        _ => (Reply::json("0"), "returns \"0\"".into()),
    }
}

/// A random answer of the scripted token.
fn stub_reply(rng: &mut Rng, amount: u128, call: bool) -> (Reply, String) {
    if !call {
        let mode = match rng.below(100) {
            0..=54 => "void",
            55..=69 => "panic",
            _ => "value",
        };
        return stub_reply_mode(mode, amount, rng);
    }
    match rng.below(100) {
        0..=17 => stub_reply_mode("all", amount, rng),
        18..=25 => stub_reply_mode("zero", amount, rng),
        26..=33 => {
            let n = rng.upto(amount);
            (Reply::json(n.to_string()), format!("returns \"{n}\""))
        }
        34..=41 => stub_reply_mode("over", amount, rng),
        42..=65 => stub_reply_mode(*rng.pick(&["len43", "len44", "len45", "len46"]), amount, rng),
        66..=73 => stub_reply_mode(*rng.pick(&["bad44", "bad45", "full44"]), amount, rng),
        74..=77 => stub_reply_mode("plus", amount, rng),
        78..=85 => {
            let g = *rng.pick(&["{", "abc", "5", "null", "", "\"12a\"", "\"-1\"", "\" 5\"", "\"340282366920938463463374607431768211456\""]);
            (Reply::bytes(g.as_bytes().to_vec()), format!("returns the bytes {g:?}"))
        }
        86..=93 => stub_reply_mode("panic", amount, rng),
        _ => (Reply::json("0").at_limit(), "returns \"0\" padded to the return limit".into()),
    }
}

/// An amount argument: now and then 2^128, which is no `u128`.
fn amount_arg(rng: &mut Rng, a: u128) -> String {
    if rng.chance(1) { U128_OVER.to_string() } else { a.to_string() }
}

/// One of the four forced internal transfers (`mt_force_*`), by `by`.
fn mt_force_op(rng: &mut Rng, by: &str, owner: &str, tid: &str, to: &str, a: u128, variant: u64) -> Op {
    let (m, batch, call) = match variant % 4 {
        0 => ("mt_force_transfer", false, false),
        1 => ("mt_force_batch_transfer", true, false),
        2 => ("mt_force_transfer_call", false, true),
        _ => ("mt_force_batch_transfer_call", true, true),
    };
    let mut args = if batch {
        json!({"owner_id": owner, "receiver_id": to, "token_ids": [tid], "amounts": [a.to_string()]})
    } else {
        json!({"owner_id": owner, "receiver_id": to, "token_id": tid, "amount": a.to_string()})
    };
    if call {
        args["msg"] = json!("");
    }
    let mut op = Op::new("force_transfer", by, INTENTS, m, args).dep(1);
    let mut label = format!("{by} calls {m}: {a} of {tid} from {owner} to {to}");
    if call {
        if RECVS.contains(&to) {
            let (reply, l) = mt_reply(rng, &[a]);
            label += &format!("; receiver: {l}");
            op.replies.push((to.into(), "mt_on_transfer".into(), reply, l));
        }
        faults(
            rng,
            &mut op,
            &[
                (Receipts::call(to, "mt_on_transfer"), "mt_on_transfer", true),
                (Receipts::callback("mt_resolve_transfer"), "mt_resolve_transfer", false),
            ],
        );
    }
    op.label = label;
    op
}

/// Arguments (well-formed) for a guarded method outside the token paths.
fn outside_args(sim: &Sim, rng: &mut Rng, m: &str) -> Value {
    let pk = |u: &str| sim.secret_key(u).public_key().to_string();
    match m {
        "set_fee" => json!({"fee": *rng.pick(&[0u32, 1, 100, 2500])}),
        "set_fee_collector" => json!({"fee_collector": *rng.pick(&[ADMIN, USERS[1], DAO])}),
        "add_full_access_key" | "delete_key" => json!({"public_key": pk(*rng.pick(&[USERS[0], USERS[1]]))}),
        "add_relayer_key" | "delete_relayer_key" => json!({"public_key": pk(*rng.pick(&[USERS[2], USERS[3]]))}),
        "cleanup_nonces" => json!({"nonces": []}),
        "invalidate_salts" => json!({"salts": []}),
        "admin_call" => json!({"promises": []}),
        _ => json!({}),
    }
}

/// One call of a guarded method outside the token paths by `by`.
fn outside_op(sim: &Sim, rng: &mut Rng, m: &str, by: &str) -> Op {
    let mut op = Op::new("guarded", by, INTENTS, m, outside_args(sim, rng, m)).dep(1);
    if m == "upgrade" {
        // borsh: an empty `code: Vec<u8>` and `state_migration_gas: None`
        op.args = vec![0, 0, 0, 0, 0];
    }
    op.label = format!("{by} calls {m}");
    op
}

/// A call of a role-guarded method that is outside the token paths: by an account that holds none
/// of the required roles, or by a standing holder of one. No holder calls `upgrade` (it would
/// replace the code under test), and `TEMP`, whose roles change, makes none of these calls.
fn guarded_outside_op(sim: &Sim, rng: &mut Rng, st: &State) -> Op {
    let m = *rng.pick(&GUARDED[13..]);
    let need = guard_roles(m);
    let (right, wrong): (Vec<&'static str>, Vec<&'static str>) =
        ACTORS.iter().copied().chain([USERS[2], RECVS[0]]).filter(|a| *a != TEMP).partition(|a| has_any(st, a, need));
    let by = if m != "upgrade" && !right.is_empty() && rng.chance(45) { *rng.pick(&right) } else { *rng.pick(&wrong) };
    let mut op = outside_op(sim, rng, m, by);
    op.deposit = one(rng);
    op
}

fn gen_op(sim: &Sim, rng: &mut Rng, st: &State, c: &Cfg, pool: &mut Vec<Value>) -> Op {
    let fts = [TOKEN, TOKEN, WRAP];
    if !st.paused.is_empty() && rng.chance(30) {
        let keys: Vec<&String> = st.paused.iter().collect();
        let k = (*rng.pick(&keys)).clone();
        let by = if rng.chance(80) { PAUSER } else { pick_caller(rng, st, "pa_unpause_feature", 50) };
        return pause_op(by, &k, false);
    }
    if !st.auth_off.is_empty() && rng.chance(25) {
        let offs: Vec<&String> = st.auth_off.iter().collect();
        let who = (*rng.pick(&offs)).clone();
        let by = pick_caller(rng, st, "force_enable_auth_by_predecessor_ids", 85);
        return auth_force_op(by, &[who.as_str()], true);
    }
    match rng.below(136) {
        100..=112 => intent_op(sim, rng, st, pool),
        113..=118 => {
            // the scripted token notifies a deposit; amounts up to and beyond the u128 range
            let who = *rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0]]);
            let room = u128::MAX - st.supply.get(&ft_id(STUB)).copied().unwrap_or(0);
            let a: String = match rng.below(100) {
                0..=83 => (1 + rng.upto(near(1000))).to_string(),
                84..=85 => "0".into(),
                86..=87 => u128::MAX.to_string(),
                88..=89 => room.to_string(),
                90..=91 => room.saturating_add(1).to_string(),
                92..=93 => room.saturating_sub(1).to_string(),
                94..=95 => (1u128 << 127).to_string(),
                96..=97 => ((1u128 << 127) - 1).to_string(),
                _ => U128_OVER.to_string(),
            };
            let msg = deposit_msg(rng);
            stub_deposit_op(who, &a, &msg)
        }
        119..=121 => {
            // forced internal transfer
            let tid = rng.pick(&c.ids).clone();
            let owner = owner_of(rng, st, &tid);
            let a = amount_for(rng, ledger_of(st, &tid, owner));
            let to = *rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0], RECVS[1], GHOST, UNREG, FORCER]);
            let v = rng.below(4);
            let m = ["mt_force_transfer", "mt_force_batch_transfer", "mt_force_transfer_call", "mt_force_batch_transfer_call"][v as usize];
            let by = pick_caller(rng, st, m, 60);
            let mut op = mt_force_op(rng, by, owner, &tid, to, a, v);
            op.deposit = one(rng);
            op
        }
        122..=125 => {
            // the auth-by-predecessor switch
            match rng.below(10) {
                0..=3 => {
                    let who = *rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0], UNREG]);
                    let mut op = auth_self_op(who);
                    op.deposit = one(rng);
                    op
                }
                k => {
                    let enable = k >= 7;
                    let m = if enable { "force_enable_auth_by_predecessor_ids" } else { "force_disable_auth_by_predecessor_ids" };
                    let by = pick_caller(rng, st, m, 60);
                    let mut whom = vec![*rng.pick(&FLAG_WATCH)];
                    if rng.chance(30) {
                        whom.push(*rng.pick(&FLAG_WATCH));
                    }
                    if rng.chance(5) {
                        whom.clear();
                    }
                    let mut op = auth_force_op(by, &whom, enable);
                    op.deposit = one(rng);
                    op
                }
            }
        }
        126..=129 => {
            // role grants: only TEMP is ever granted or revoked anything, and ADMIN never gives
            // its own super-admin permission away, so the standing role holders stay as they are
            let m = *rng.pick(&[
                "acl_grant_role", "acl_grant_role", "acl_grant_role", "acl_revoke_role", "acl_revoke_role", "acl_renounce_role",
                "acl_add_admin", "acl_revoke_admin", "acl_renounce_admin", "acl_add_super_admin", "acl_revoke_super_admin",
                "acl_transfer_super_admin", "acl_init_super_admin",
            ]);
            let role = if rng.chance(95) { *rng.pick(&ROLE_NAMES) } else { "NoSuchRole" };
            let any = [ADMIN, ADMIN, ADMIN, ROLEADMIN, ROLEADMIN, TEMP, TEMP, DAO, FEES1, USERS[1], UNREG, PAUSER];
            let mut op = match m {
                "acl_renounce_role" | "acl_renounce_admin" => acl_op(*rng.pick(&[TEMP, TEMP, TEMP, USERS[1], UNREG]), m, Some(role), None),
                "acl_transfer_super_admin" => {
                    let by = *rng.pick(&[TEMP, TEMP, DAO, ROLEADMIN, USERS[1]]);
                    acl_op(by, m, None, Some(if by == TEMP { ADMIN } else { TEMP }))
                }
                "acl_add_super_admin" | "acl_revoke_super_admin" | "acl_init_super_admin" => acl_op(*rng.pick(&any), m, None, Some(TEMP)),
                _ => {
                    let role = if rng.chance(35) { *rng.pick(&ROLEADMIN_OF) } else { role };
                    acl_op(*rng.pick(&any), m, Some(role), Some(TEMP))
                }
            };
            if rng.chance(3) {
                op.deposit = 1;
            }
            op
        }
        130..=132 => {
            if rng.chance(25) {
                let victim = *rng.pick(&USERS);
                let by = pick_caller(rng, st, "nft_force_withdraw", 50);
                let args = json!({"owner_id": victim, "token": USERS[2], "receiver_id": USERS[1], "token_id": "1"});
                let mut op = Op::new("force_withdraw", by, INTENTS, "nft_force_withdraw", args).dep(one(rng));
                op.label = format!("{by} calls nft_force_withdraw for a token nobody holds");
                op
            } else {
                guarded_outside_op(sim, rng, st)
            }
        }
        133..=135 => {
            let who = *rng.pick(&[USERS[1], USERS[2], UNREG, RECVS[0], DAO, ADMIN]);
            let m = *rng.pick(&PRIVATE_MORE);
            let mut op = Op::new("private_direct", who, INTENTS, m, json!({"account_id": who})).dep(*rng.pick(&[0u128, 0, 1]));
            op.label = format!("{who} calls the private {m} directly");
            op
        }
        0..=21 => {
            // deposit: token.ft_transfer_call(intents, amount, msg)
            let t = *rng.pick(&fts);
            let who = *rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0]]);
            let a = amount_for(rng, token_balance(sim, t, who) / 50);
            let msg = deposit_msg(rng);
            let mut args = json!({"receiver_id": INTENTS, "amount": a.to_string(), "msg": msg});
            opt(&mut args, "memo", rng.chance(20).then(|| json!("dep")));
            let mut op = Op::new("deposit", who, t, "ft_transfer_call", args).dep(one(rng));
            faults(
                rng,
                &mut op,
                &[
                    (Receipts::call(INTENTS, "ft_on_transfer"), "ft_on_transfer", true),
                    (Receipts::callback("ft_resolve_transfer"), "the token's ft_resolve_transfer", false),
                ],
            );
            if rng.chance(4) {
                op.gas = Some(*rng.pick(&[20u64, 30, 40]));
            }
            op.label = format!("{who} deposits {a} of {t} with msg {msg:?}");
            op
        }
        22..=24 => {
            let t = *rng.pick(&fts);
            let who = *rng.pick(&USERS);
            let a = amount_for(rng, token_balance(sim, t, who) / 100);
            let mut op = Op::new("donate", who, t, "ft_transfer", json!({"receiver_id": INTENTS, "amount": a.to_string()})).dep(1);
            op.label = format!("{who} sends {a} of {t} to the contract with a plain ft_transfer");
            op
        }
        25..=47 => {
            // withdrawal: intents.ft_withdraw(token, receiver, amount, memo, msg)
            let fake = [USERS[1], USERS[2]];
            let t = match rng.below(100) {
                0..=73 => *rng.pick(&fts),
                74..=89 => STUB,
                90..=95 => *rng.pick(&fake),
                _ => *rng.pick(&["nope.near", UNREG, INTENTS]),
            };
            let tid = ft_id(t);
            let who = owner_of(rng, st, &tid);
            let a = amount_for(rng, ledger_of(st, &tid, who));
            let to = *rng.pick(&[
                USERS[1], USERS[2], USERS[3], USERS[0], RECVS[0], RECVS[1], RECVS[0], RECVS[1], UNREG, GHOST, INTENTS, MT,
            ]);
            let is_call = rng.chance(45);
            let to = if is_call && rng.chance(55) { *rng.pick(&RECVS) } else { to };
            let mut args = json!({"token": t, "receiver_id": to, "amount": amount_arg(rng, a)});
            opt(&mut args, "memo", rng.chance(25).then(|| if rng.chance(50) { json!("w") } else { Value::Null }));
            let mut label = format!("{who} withdraws {a} of {t} to {to}");
            let mut op;
            if is_call {
                let msg = *rng.pick(&["", "m", "take"]);
                args["msg"] = json!(msg);
                op = Op::new("withdraw", who, INTENTS, "ft_withdraw", args).dep(one(rng));
                label += &format!(" by ft_transfer_call (msg {msg:?})");
                if t == STUB {
                    let (reply, l) = stub_reply(rng, a, true);
                    label += &format!("; the scripted token: {l}");
                    op.replies.push((STUB.into(), "ft_transfer_call".into(), reply, l));
                } else if RECVS.contains(&to) {
                    let (reply, l) = ft_reply(rng, a, t, to);
                    label += &format!("; receiver: {l}");
                    op.replies.push((to.into(), "ft_on_transfer".into(), reply, l));
                }
                faults(
                    rng,
                    &mut op,
                    &[
                        (Receipts::call(t, "ft_transfer_call"), "the token's ft_transfer_call", true),
                        (Receipts::callback("ft_resolve_transfer"), "the token's ft_resolve_transfer", true),
                        (Receipts::callback("ft_resolve_withdraw"), "ft_resolve_withdraw", false),
                    ],
                );
            } else {
                if rng.chance(15) {
                    args["msg"] = Value::Null;
                }
                op = Op::new("withdraw", who, INTENTS, "ft_withdraw", args).dep(one(rng));
                if t == STUB {
                    let (reply, l) = stub_reply(rng, a, false);
                    label += &format!("; the scripted token: {l}");
                    op.replies.push((STUB.into(), "ft_transfer".into(), reply, l));
                }
                faults(
                    rng,
                    &mut op,
                    &[
                        (Receipts::call(t, "ft_transfer"), "the token's ft_transfer", true),
                        (Receipts::callback("ft_resolve_withdraw"), "ft_resolve_withdraw", false),
                    ],
                );
            }
            if rng.chance(8) {
                op.gas = Some(*rng.pick(&[10u64, 20, 25, 30, 40, 50, 70, 100]));
            }
            op.label = label;
            op
        }
        48..=50 => {
            if rng.chance(30) {
                let inner = ft_id(*rng.pick(&[TOKEN, WRAP]));
                let tid = mt_id(MT, &inner);
                let victim = owner_of(rng, st, &tid);
                let a = amount_for(rng, ledger_of(st, &tid, victim));
                let to = *rng.pick(&[USERS[1], USERS[2], FORCER, GHOST, INTENTS]);
                let by = pick_caller(rng, st, "mt_force_withdraw", 60);
                let mut args = json!({"owner_id": victim, "token": MT, "receiver_id": to, "token_ids": [inner], "amounts": [a.to_string()]});
                opt(&mut args, "msg", rng.chance(25).then(|| json!("")));
                let mut op = Op::new("force_withdraw", by, INTENTS, "mt_force_withdraw", args).dep(one(rng));
                op.label = format!("{by} force-withdraws {a} of {MT}:{inner} from {victim} to {to}");
                return op;
            }
            let t = if rng.chance(25) { STUB } else { *rng.pick(&fts) };
            let tid = ft_id(t);
            let victim = owner_of(rng, st, &tid);
            let a = amount_for(rng, ledger_of(st, &tid, victim));
            let to = *rng.pick(&[USERS[1], USERS[2], FORCER, UNREG, RECVS[0]]);
            let by = pick_caller(rng, st, "ft_force_withdraw", 60);
            let mut args = json!({"owner_id": victim, "token": t, "receiver_id": to, "amount": a.to_string()});
            let is_call = rng.chance(25);
            if is_call {
                args["msg"] = json!("");
            }
            let mut op = Op::new("force_withdraw", by, INTENTS, "ft_force_withdraw", args).dep(one(rng));
            op.label = format!("{by} force-withdraws {a} of {t} from {victim} to {to}");
            if t == STUB {
                let (reply, l) = stub_reply(rng, a, is_call);
                op.label += &format!("; the scripted token: {l}");
                op.replies.push((STUB.into(), (if is_call { "ft_transfer_call" } else { "ft_transfer" }).into(), reply, l));
            }
            op
        }
        51..=61 => {
            // inside the ledger: mt_transfer, mt_batch_transfer, mt_transfer_call
            let tid = rng.pick(&c.ids).clone();
            let who = owner_of(rng, st, &tid);
            let a = amount_for(rng, ledger_of(st, &tid, who));
            let to = *rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0], RECVS[1], GHOST, UNREG, INTENTS, MT]);
            let memo = rng.chance(20).then(|| json!("t"));
            match rng.below(10) {
                0..=4 => {
                    let mut args = json!({"receiver_id": to, "token_id": tid, "amount": amount_arg(rng, a)});
                    opt(&mut args, "memo", memo);
                    opt(&mut args, "approval", rng.chance(4).then(|| json!([USERS[0], 0])));
                    let mut op = Op::new("transfer", who, INTENTS, "mt_transfer", args).dep(one(rng));
                    op.label = format!("{who} moves {a} of {tid} to {to} inside the ledger");
                    op
                }
                5 | 6 => {
                    let tid2 = rng.pick(&c.ids).clone();
                    let a2 = amount_for(rng, ledger_of(st, &tid2, who));
                    let mut args = json!({"receiver_id": to, "token_ids": [tid, tid2], "amounts": [a.to_string(), a2.to_string()]});
                    opt(&mut args, "memo", memo);
                    let mut op = Op::new("transfer", who, INTENTS, "mt_batch_transfer", args).dep(one(rng));
                    op.label = format!("{who} moves {a} of {tid} and {a2} of {tid2} to {to} inside the ledger");
                    op
                }
                _ => {
                    let to = *rng.pick(&[RECVS[0], RECVS[1], RECVS[0], USERS[1], GHOST]);
                    let mut args = json!({"receiver_id": to, "token_id": tid, "amount": a.to_string(), "msg": *rng.pick(&["", "m"])});
                    opt(&mut args, "memo", memo);
                    let mut op = Op::new("transfer_call", who, INTENTS, "mt_transfer_call", args).dep(one(rng));
                    let mut label = format!("{who} moves {a} of {tid} to {to} inside the ledger with mt_transfer_call");
                    if RECVS.contains(&to) {
                        let (reply, l) = mt_reply(rng, &[a]);
                        label += &format!("; receiver: {l}");
                        op.replies.push((to.into(), "mt_on_transfer".into(), reply, l));
                    }
                    faults(
                        rng,
                        &mut op,
                        &[
                            (Receipts::call(to, "mt_on_transfer"), "mt_on_transfer", true),
                            (Receipts::callback("mt_resolve_transfer"), "mt_resolve_transfer", false),
                        ],
                    );
                    op.label = label;
                    op
                }
            }
        }
        62..=66 => {
            let k = if rng.chance(92) { *rng.pick(&PAUSE_KEYS) } else { *rng.pick(&["ALL", "no_such_feature"]) };
            let m = if rng.chance(70) { "pa_pause_feature" } else { "pa_unpause_feature" };
            let by = pick_caller(rng, st, m, 65);
            let mut op = Op::new("pause", by, INTENTS, m, json!({"key": k}));
            if rng.chance(3) {
                op.deposit = 1;
            }
            op.label = format!("{by} calls {m}({k})");
            op
        }
        67..=69 => {
            let (at, who) = if rng.chance(85) {
                (INTENTS, *rng.pick(&[USERS[1], USERS[2], USERS[3], RECVS[0], GHOST]))
            } else {
                (MT, INTENTS)
            };
            let m = if rng.chance(55) { "force_lock_account" } else { "force_unlock_account" };
            let by = if at == MT { *rng.pick(&[LOCKER, LOCKER, LOCKER, USERS[1], UNREG, PAUSER]) } else { pick_caller(rng, st, m, 65) };
            let mut op = Op::new("lock", by, at, m, json!({"account_id": who})).dep(one(rng));
            op.label = format!("{by} calls {at}::{m}({who})");
            op
        }
        70..=77 => {
            // a stranger calls a private callback, directly or as the callback of its own promise
            let who = *rng.pick(&[USERS[1], USERS[2], UNREG, RECVS[0]]);
            let victim = *rng.pick(&[USERS[1], USERS[2], USERS[3], who]);
            let t = *rng.pick(&fts);
            let big = *rng.pick(&[1u128, 1000, near(1), token_balance(sim, t, INTENTS)]);
            let m = *rng.pick(&PRIVATE);
            let args = match m {
                "ft_resolve_withdraw" => json!({"token": t, "sender_id": victim, "amount": big.to_string(), "is_call": rng.chance(50)}),
                "ft_resolve_deposit" => json!({"receiver_id": victim, "contract_id": t, "amount": big.to_string()}),
                "do_ft_withdraw" => json!({"withdraw": {"token": t, "receiver_id": who, "amount": big.to_string()}}),
                "mt_resolve_withdraw" => json!({"token": MT, "sender_id": victim, "token_ids": [ft_id(t)], "amounts": [big.to_string()], "is_call": rng.chance(50)}),
                "mt_resolve_deposit" => json!({"receiver_id": victim, "contract_id": MT, "tokens": [ft_id(t)], "amounts": [big.to_string()]}),
                "mt_resolve_transfer" => json!({"previous_owner_ids": [who], "receiver_id": victim, "token_ids": [ft_id(t)], "amounts": [big.to_string()]}),
                "do_mt_withdraw" => json!({"withdraw": {"token": MT, "receiver_id": who, "token_ids": [ft_id(t)], "amounts": [big.to_string()]}}),
                "do_native_withdraw" => json!({"withdraw": {"receiver_id": who, "amount": big.to_string()}}),
                _ => json!({"storage_deposit": {"contract_id": t, "deposit_for_account_id": who, "amount": big.to_string()}}),
            };
            let d = *rng.pick(&[0u128, 0, 1]);
            if rng.chance(55) {
                let mut op = Op::new("private_direct", who, INTENTS, m, args).dep(d);
                op.label = format!("{who} calls the private {m} directly");
                op
            } else {
                let pre = if rng.chance(50) { "f" } else { "s" };
                let mut op = Op::new("private_callback", who, EVIL, &format!("{pre}_{m}"), args);
                op.label = format!(
                    "{who} has {EVIL} run the private {m} as the callback of its own {} promise",
                    if pre == "f" { "failing" } else { "succeeding" }
                );
                op
            }
        }
        78..=81 => {
            // an account that is no token calls the deposit entry points itself
            let who = *rng.pick(&[USERS[1], USERS[2]]);
            let a = *rng.pick(&[1u128, 500, near(1), 0]);
            let msg = deposit_msg(rng);
            if who == USERS[1] && rng.chance(35) {
                let args = json!({"sender_id": who, "previous_owner_ids": [who], "token_ids": ["x"], "amounts": [a.to_string()], "msg": msg});
                let mut op = Op::new("self_token", who, INTENTS, "mt_on_transfer", args);
                op.label = format!("{who} calls mt_on_transfer itself: {a} of its own token x, msg {msg:?}");
                op
            } else {
                let args = json!({"sender_id": *rng.pick(&[who, USERS[3]]), "amount": a.to_string(), "msg": msg});
                let mut op = Op::new("self_token", who, INTENTS, "ft_on_transfer", args);
                op.label = format!("{who} calls ft_on_transfer itself: {a} of its own token, msg {msg:?}");
                op
            }
        }
        82..=89 => {
            // NEP-245 deposit: mt.near::mt_transfer_call(intents, token_id, amount, msg)
            let who = *rng.pick(&USERS);
            let inner = ft_id(*rng.pick(&[TOKEN, WRAP]));
            let bal = vj(sim, MT, "mt_balance_of", json!({"account_id": who, "token_id": inner})).map(|v| amt(&v)).unwrap_or(0);
            let a = amount_for(rng, bal / 20);
            let msg = deposit_msg(rng);
            let mut op;
            if rng.chance(70) {
                let args = json!({"receiver_id": INTENTS, "token_id": inner, "amount": a.to_string(), "msg": msg});
                op = Op::new("mt_deposit", who, MT, "mt_transfer_call", args).dep(one(rng));
                op.label = format!("{who} deposits {a} of {MT}:{inner} with msg {msg:?}");
            } else {
                let inner2 = ft_id(if inner == ft_id(TOKEN) { WRAP } else { TOKEN });
                let bal2 = vj(sim, MT, "mt_balance_of", json!({"account_id": who, "token_id": inner2})).map(|v| amt(&v)).unwrap_or(0);
                let a2 = amount_for(rng, bal2 / 20);
                let args = json!({"receiver_id": INTENTS, "token_ids": [inner, inner2], "amounts": [a.to_string(), a2.to_string()], "msg": msg});
                op = Op::new("mt_deposit", who, MT, "mt_batch_transfer_call", args).dep(one(rng));
                op.label = format!("{who} deposits {a} of {MT}:{inner} and {a2} of {MT}:{inner2} with msg {msg:?}");
            }
            faults(
                rng,
                &mut op,
                &[
                    (Receipts::call(INTENTS, "mt_on_transfer"), "mt_on_transfer", true),
                    (Receipts::callback("mt_resolve_transfer"), "the token's mt_resolve_transfer", false),
                ],
            );
            op
        }
        90..=96 => {
            // NEP-245 withdrawal: intents.mt_withdraw(mt.near, receiver, token_ids, amounts, memo, msg)
            let inner = ft_id(*rng.pick(&[TOKEN, WRAP]));
            let tid = mt_id(MT, &inner);
            let who = owner_of(rng, st, &tid);
            let a = amount_for(rng, ledger_of(st, &tid, who));
            let to = *rng.pick(&[USERS[1], USERS[2], USERS[3], RECVS[0], RECVS[1], RECVS[0], GHOST, INTENTS, MT]);
            let (mut ids, mut amounts) = (vec![inner.clone()], vec![a]);
            if rng.chance(25) {
                let inner2 = ft_id(if inner == ft_id(TOKEN) { WRAP } else { TOKEN });
                amounts.push(amount_for(rng, ledger_of(st, &mt_id(MT, &inner2), who)));
                ids.push(inner2);
            }
            let sa: Vec<String> = amounts.iter().map(|x| x.to_string()).collect();
            let mut args = json!({"token": MT, "receiver_id": to, "token_ids": ids, "amounts": sa});
            opt(&mut args, "memo", rng.chance(20).then(|| json!("w")));
            let mut label = format!("{who} withdraws {sa:?} of {MT}:{ids:?} to {to}");
            let mut op;
            if rng.chance(45) {
                let to = if rng.chance(50) { *rng.pick(&RECVS) } else { to };
                args["receiver_id"] = json!(to);
                label = format!("{who} withdraws {sa:?} of {MT}:{ids:?} to {to}");
                args["msg"] = json!(*rng.pick(&["", "m"]));
                op = Op::new("mt_withdraw", who, INTENTS, "mt_withdraw", args).dep(one(rng));
                label += " by mt_batch_transfer_call";
                if RECVS.contains(&to) {
                    let (reply, l) = mt_reply(rng, &amounts);
                    label += &format!("; receiver: {l}");
                    op.replies.push((to.into(), "mt_on_transfer".into(), reply, l));
                }
                faults(
                    rng,
                    &mut op,
                    &[
                        (Receipts::call(MT, "mt_batch_transfer_call"), "the token's mt_batch_transfer_call", true),
                        (Receipts::callback("mt_resolve_withdraw"), "mt_resolve_withdraw", false),
                    ],
                );
            } else {
                op = Op::new("mt_withdraw", who, INTENTS, "mt_withdraw", args).dep(one(rng));
                faults(
                    rng,
                    &mut op,
                    &[
                        (Receipts::call(MT, "mt_batch_transfer"), "the token's mt_batch_transfer", true),
                        (Receipts::callback("mt_resolve_withdraw"), "mt_resolve_withdraw", false),
                    ],
                );
            }
            if rng.chance(6) {
                op.gas = Some(*rng.pick(&[20u64, 30, 40, 60]));
            }
            op.label = label;
            op
        }
        97 => {
            let who = *rng.pick(&USERS);
            let inner = ft_id(*rng.pick(&[TOKEN, WRAP]));
            let a = *rng.pick(&[1u128, 1000, near(1)]);
            let mut op = Op::new("mt_donate", who, MT, "mt_transfer", json!({"receiver_id": INTENTS, "token_id": inner, "amount": a.to_string()})).dep(1);
            op.label = format!("{who} sends {a} of {MT}:{inner} to the contract with a plain mt_transfer");
            op
        }
        _ => {
            let who = *rng.pick(&[USERS[1], UNREG]);
            match rng.below(3) {
                0 => {
                    let mut op = Op::new("noise", who, INTENTS, "new", json!({"config": {"wnear_id": WRAP, "fees": {"fee": 0, "fee_collector": who}, "roles": {"super_admins": [who]}}}));
                    op.label = format!("{who} calls new() again");
                    op
                }
                1 => {
                    let mut op = Op::new("noise", who, INTENTS, "mt_balance_of", json!({"account_id": who, "token_id": ft_id(TOKEN)})).dep(*rng.pick(&[0u128, 1]));
                    op.label = format!("{who} calls a view as a transaction");
                    op
                }
                _ => {
                    let mut op = Op::new("noise", who, INTENTS, "ft_withdraw", json!({"token": TOKEN, "receiver_id": who})).dep(1);
                    op.label = format!("{who} calls ft_withdraw without an amount");
                    op
                }
            }
        }
    }
}

fn b64(b: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut s = String::new();
    for ch in b.chunks(3) {
        let n = (ch[0] as u32) << 16 | (*ch.get(1).unwrap_or(&0) as u32) << 8 | *ch.get(2).unwrap_or(&0) as u32;
        s.push(T[(n >> 18) as usize & 63] as char);
        s.push(T[(n >> 12) as usize & 63] as char);
        s.push(if ch.len() > 1 { T[(n >> 6) as usize & 63] as char } else { '=' });
        s.push(if ch.len() > 2 { T[n as usize & 63] as char } else { '=' });
    }
    s
}

fn fresh_nonce(rng: &mut Rng) -> String {
    let mut nonce = [0u8; 32];
    for b in nonce.iter_mut() {
        *b = rng.below(256) as u8;
    }
    b64(&nonce)
}

/// `execute_intents` with one payload that is right in every respect: signed by `signer` with
/// its registered key, for this contract, far deadline, fresh nonce.
fn intent_single(sim: &Sim, rng: &mut Rng, signer: &str, intents: Vec<Value>, what: &str) -> Op {
    let relayer = *rng.pick(&[USERS[0], UNREG, RECVS[0]]);
    let payload = json!({
        "signer_id": signer, "verifying_contract": INTENTS, "deadline": "2100-01-01T00:00:00Z",
        "nonce": fresh_nonce(rng), "intents": intents,
    });
    let text = payload.to_string();
    let sk = sim.secret_key(signer);
    let item = json!({
        "standard": "raw_ed25519", "payload": text,
        "public_key": sk.public_key().to_string(), "signature": sk.sign(text.as_bytes()).to_string(),
    });
    let mut op = Op::new("intent", relayer, INTENTS, "execute_intents", json!({"signed": [item]}));
    op.label = format!("{relayer} relays signed intents: {what}; [signed by {signer}]");
    op
}

/// `execute_intents` with payloads the users sign with their registered ed25519 keys
/// (standard `raw_ed25519`: the signature is over the payload text).
fn intent_op(sim: &Sim, rng: &mut Rng, st: &State, pool: &mut Vec<Value>) -> Op {
    let relayer = *rng.pick(&[USERS[0], USERS[1], UNREG, RECVS[0]]);
    if !pool.is_empty() && rng.chance(6) {
        let old = rng.pick(pool).clone();
        let mut op = Op::new("intent", relayer, INTENTS, "execute_intents", json!({"signed": [old]}));
        op.label = format!("{relayer} relays a signed payload that was already submitted before");
        return op;
    }
    let storage_min: u128 = 1_250_000_000_000_000_000_000;
    let mut signed = vec![];
    let mut labels = vec![];
    let mut op = Op::new("intent", relayer, INTENTS, "execute_intents", Value::Null);
    // mostly amounts the signer can pay: one failing intent fails the whole call
    let good = |rng: &mut Rng, bal: u128| -> u128 {
        if bal == 0 || rng.chance(8) { amount_for(rng, bal) } else if rng.chance(25) { bal } else { 1 + rng.upto(bal - 1) }
    };
    for _ in 0..(1 + rng.below(100) / 85) {
        let rich: Vec<&'static str> = USERS.iter().copied().filter(|u| st.ledger.values().any(|m| m.contains_key(*u))).collect();
        let signer = if !rich.is_empty() && rng.chance(90) { *rng.pick(&rich) } else { *rng.pick(&USERS) };
        let mut intents = vec![];
        for _ in 0..(1 + rng.below(100) / 80) {
            let wbal = ledger_of(st, &ft_id(WRAP), signer);
            let has = |t: &str| ledger_of(st, &ft_id(t), signer) > 0;
            let has_mt = [TOKEN, WRAP].iter().any(|t| ledger_of(st, &mt_id(MT, &ft_id(t)), signer) > 0);
            // mostly an intent the signer has the balance for
            let mut kinds: Vec<u64> = vec![90];
            if has(TOKEN) || has(WRAP) || has(STUB) {
                kinds.extend([10, 10, 10, 10]);
            }
            if st.auth_off.contains(signer) {
                kinds.extend([96, 96, 96]);
            }
            if has_mt {
                kinds.extend([50, 50]);
            }
            if wbal > 0 {
                kinds.extend([60, 75]);
            }
            let roll = if rng.chance(92) { *rng.pick(&kinds) } else { rng.below(100) };
            match roll {
                0..=44 => {
                    let t = if has(STUB) && (rng.chance(30) || !(has(TOKEN) || has(WRAP))) {
                        STUB
                    } else if has(TOKEN) && (!has(WRAP) || rng.chance(65)) {
                        TOKEN
                    } else if has(WRAP) {
                        WRAP
                    } else {
                        *rng.pick(&[TOKEN, WRAP])
                    };
                    let a = good(rng, ledger_of(st, &ft_id(t), signer));
                    let to = *rng.pick(&[USERS[1], USERS[2], USERS[3], RECVS[0], RECVS[1], UNREG, UNREG, GHOST, MT]);
                    let mut i = json!({"intent": "ft_withdraw", "token": t, "receiver_id": to, "amount": a.to_string()});
                    let mut l = format!("ft_withdraw {a} of {t} to {to}");
                    let is_call = rng.chance(35);
                    if t == STUB {
                        let m = if is_call { "ft_transfer_call" } else { "ft_transfer" };
                        if op.replies.iter().all(|r| !(r.0 == STUB && r.1 == m)) {
                            let (reply, rl) = stub_reply(rng, a, is_call);
                            l += &format!(" (the scripted token: {rl})");
                            op.replies.push((STUB.into(), m.into(), reply, rl));
                        }
                    }
                    if is_call {
                        i["msg"] = json!("");
                        l += " by ft_transfer_call";
                        if RECVS.contains(&to) && op.replies.iter().all(|r| r.0 != to) {
                            let (reply, rl) = ft_reply(rng, a, t, to);
                            l += &format!(" (receiver: {rl})");
                            op.replies.push((to.into(), "ft_on_transfer".into(), reply, rl));
                        }
                    }
                    let left = if t == WRAP { wbal.saturating_sub(a) } else { wbal };
                    if rng.chance(if left >= storage_min { 50 } else { 6 }) {
                        let sd = *rng.pick(&[storage_min, storage_min, storage_min, 2 * storage_min, 1, wbal.saturating_add(1)]);
                        i["storage_deposit"] = json!(sd.to_string());
                        l += &format!(" with storage_deposit {sd}");
                    }
                    if rng.chance(20) {
                        let g = *rng.pick(&["1", "15000000000000", "40000000000000", "120000000000000"]);
                        i["min_gas"] = json!(g);
                        l += &format!(" min_gas {g}");
                    }
                    intents.push(i);
                    labels.push(l);
                }
                45..=58 => {
                    let mut inner = ft_id(*rng.pick(&[TOKEN, WRAP]));
                    if ledger_of(st, &mt_id(MT, &inner), signer) == 0 {
                        inner = ft_id(if inner == ft_id(TOKEN) { WRAP } else { TOKEN });
                    }
                    let a = good(rng, ledger_of(st, &mt_id(MT, &inner), signer));
                    let to = *rng.pick(&[USERS[1], USERS[2], GHOST, RECVS[0], INTENTS]);
                    let mut i = json!({"intent": "mt_withdraw", "token": MT, "receiver_id": to, "token_ids": [inner], "amounts": [a.to_string()]});
                    let mut l = format!("mt_withdraw {a} of {MT}:{inner} to {to}");
                    if rng.chance(30) {
                        i["msg"] = json!("");
                        l += " by mt_batch_transfer_call";
                    }
                    if rng.chance(10) {
                        i["storage_deposit"] = json!(storage_min.to_string());
                        l += " with storage_deposit";
                    }
                    intents.push(i);
                    labels.push(l);
                }
                59..=70 => {
                    let a = good(rng, wbal / 4);
                    let to = *rng.pick(&[USERS[1], USERS[2], UNREG, GHOST, signer]);
                    intents.push(json!({"intent": "native_withdraw", "receiver_id": to, "amount": a.to_string()}));
                    labels.push(format!("native_withdraw {a} to {to}"));
                }
                71..=80 => {
                    let t = *rng.pick(&[TOKEN, TOKEN, WRAP, MT, UNREG, STUB]);
                    let who = *rng.pick(&[UNREG, GHOST, USERS[2], PAUSER]);
                    let a = *rng.pick(&[storage_min, storage_min, 2 * storage_min, 1]);
                    intents.push(json!({"intent": "storage_deposit", "contract_id": t, "deposit_for_account_id": who, "amount": a.to_string()}));
                    labels.push(format!("storage_deposit {a} on {t} for {who}"));
                }
                94.. => {
                    let on = if st.auth_off.contains(signer) { rng.chance(85) } else { rng.chance(15) };
                    intents.push(json!({"intent": "set_auth_by_predecessor_id", "enabled": on}));
                    labels.push(format!("set_auth_by_predecessor_id {on}"));
                }
                _ => {
                    let all = [ft_id(TOKEN), ft_id(WRAP), mt_id(MT, &ft_id(TOKEN)), mt_id(MT, &ft_id(WRAP)), ft_id(STUB)];
                    let mine: Vec<&String> = all.iter().filter(|t| ledger_of(st, t, signer) > 0).collect();
                    let tid = if mine.is_empty() { rng.pick(&all).clone() } else { (*rng.pick(&mine)).clone() };
                    let a = good(rng, ledger_of(st, &tid, signer));
                    let others: Vec<&str> = [USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0], GHOST].into_iter().filter(|x| *x != signer || rng.chance(5)).collect();
                    let to = *rng.pick(&others);
                    let mut tokens = Map::new();
                    tokens.insert(tid.clone(), json!(a.to_string()));
                    intents.push(json!({"intent": "transfer", "receiver_id": to, "tokens": tokens}));
                    labels.push(format!("transfer {a} of {tid} to {to}"));
                }
            }
        }
        let mut payload = json!({
            "signer_id": signer, "verifying_contract": INTENTS, "deadline": "2100-01-01T00:00:00Z",
            "nonce": fresh_nonce(rng), "intents": intents,
        });
        let mut key_of = signer;
        let mut other_text = false;
        match rng.below(100) {
            0..=2 => {
                key_of = *rng.pick(&USERS);
                labels.push(format!("(signed with the key of {key_of})"));
            }
            3 | 4 => {
                payload["verifying_contract"] = json!(MT);
                labels.push("(for another verifying contract)".into());
            }
            5 | 6 => {
                payload["deadline"] = json!("2001-01-01T00:00:00Z");
                labels.push("(deadline in the past)".into());
            }
            7 | 8 => {
                payload["signer_id"] = json!(*rng.pick(&[USERS[3], UNREG, RECVS[0]]));
                labels.push(format!("(signer_id replaced by {})", payload["signer_id"]));
            }
            9 => {
                other_text = true;
                labels.push("(the signature is over another text)".into());
            }
            _ => {}
        }
        let text = payload.to_string();
        let sk = sim.secret_key(key_of);
        let signed_text = if other_text { format!("{text} ") } else { text.clone() };
        let item = json!({
            "standard": "raw_ed25519", "payload": text,
            "public_key": sk.public_key().to_string(), "signature": sk.sign(signed_text.as_bytes()).to_string(),
        });
        labels.push(format!("[signed by {signer}]"));
        pool.push(item.clone());
        signed.push(item);
    }
    if pool.len() > 8 {
        pool.remove(0);
    }
    op.args = serde_json::to_vec(&json!({"signed": signed})).unwrap();
    faults(
        rng,
        &mut op,
        &[
            (Receipts::call(WRAP, "near_withdraw"), "wNEAR's near_withdraw", true),
            (Receipts::callback("do_ft_withdraw"), "do_ft_withdraw", false),
            (Receipts::callback("ft_resolve_withdraw"), "ft_resolve_withdraw", false),
            (Receipts::callback("mt_resolve_withdraw"), "mt_resolve_withdraw", false),
        ],
    );
    op.label = format!("{relayer} relays signed intents: {}", labels.join("; "));
    op
}

/// A plain successful deposit, so that the random part of a trace starts with ledger balances.
fn fund_op(sim: &Sim, rng: &mut Rng) -> Op {
    let who = *rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], RECVS[0], RECVS[1]]);
    let to = if rng.chance(70) { who } else { *rng.pick(&[USERS[1], USERS[2], USERS[3], RECVS[0], RECVS[1], UNREG]) };
    let msg = if to == who { String::new() } else { to.to_string() };
    if USERS.contains(&who) && rng.chance(30) {
        let inner = ft_id(*rng.pick(&[TOKEN, WRAP]));
        let bal = vj(sim, MT, "mt_balance_of", json!({"account_id": who, "token_id": inner})).map(|v| amt(&v)).unwrap_or(0);
        let a = 1 + rng.upto(bal / 20);
        let args = json!({"receiver_id": INTENTS, "token_id": inner, "amount": a.to_string(), "msg": msg});
        let mut op = Op::new("mt_deposit", who, MT, "mt_transfer_call", args).dep(1);
        op.label = format!("{who} deposits {a} of {MT}:{inner} for {to} (funding)");
        op
    } else {
        let t = *rng.pick(&[TOKEN, TOKEN, WRAP]);
        let a = 1 + rng.upto(token_balance(sim, t, who) / 50);
        let args = json!({"receiver_id": INTENTS, "amount": a.to_string(), "msg": msg});
        let mut op = Op::new("deposit", who, t, "ft_transfer_call", args).dep(1);
        op.label = format!("{who} deposits {a} of {t} for {to} (funding)");
        op
    }
}

fn submit(sim: &mut Sim, op: &Op) -> CryptoHash {
    let mut tx = sim
        .call(op.signer.as_str(), op.recv.as_str(), &op.method)
        .args(op.args.clone())
        .deposit(Balance::from_yoctonear(op.deposit));
    if let Some(g) = op.gas {
        tx = tx.gas(Gas::from_teragas(g));
    }
    for (stub, method, reply, _) in &op.replies {
        tx = tx.stub_reply(stub.as_str(), method, reply.clone());
    }
    for (at, fault, _) in &op.faults {
        tx = tx.inject(at.clone(), fault.clone());
    }
    tx.submit()
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
        ExecutionStatus::SuccessReceiptId(id) => json!({"kind": "promise", "rid": id.to_string()}),
        _ => Value::Null,
    }
}

fn args_of(a: Option<&Vec<u8>>) -> Value {
    match a {
        None => Value::Null,
        Some(b) => match serde_json::from_slice::<Value>(b) {
            Ok(j) => j,
            Err(_) => json!({"$raw": String::from_utf8_lossy(b)}),
        },
    }
}

/// The ids of the data a receipt's result goes to: borsh `Vec<DataReceiver>` in hex.
fn output_data_ids(hexs: &str) -> Vec<String> {
    let b: Vec<u8> = (0..hexs.len() / 2).filter_map(|i| u8::from_str_radix(&hexs[2 * i..2 * i + 2], 16).ok()).collect();
    let mut out = vec![];
    if b.len() < 4 {
        return out;
    }
    let n = u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as usize;
    let mut p = 4;
    for _ in 0..n {
        if p + 36 > b.len() {
            break;
        }
        let mut id = [0u8; 32];
        id.copy_from_slice(&b[p..p + 32]);
        let l = u32::from_le_bytes([b[p + 32], b[p + 33], b[p + 34], b[p + 35]]) as usize;
        p += 36 + l;
        out.push(CryptoHash(id).to_string());
    }
    out
}

/// One trace being generated.
struct Run<'a> {
    sim: Sim,
    rng: Rng,
    c: &'a Cfg,
    /// The views after the last block.
    st: State,
    ops: Vec<Value>,
    tx_op: HashMap<CryptoHash, usize>,
    /// Per block: height, views, enumerated token ids, view errors, pending operations, timestamp.
    blocks: Vec<(u64, State, Vec<String>, Vec<String>, Vec<usize>, u64)>,
    pool: Vec<Value>,
    /// The probe the operations being submitted belong to.
    probe: Option<&'static str>,
}

impl Run<'_> {
    fn submit(&mut self, op: Op) -> CryptoHash {
        let h = self.sim.height();
        let tx = submit(&mut self.sim, &op);
        self.tx_op.insert(tx, self.ops.len());
        self.ops.push(json!({
            "i": self.ops.len(), "h": h, "tx": tx.to_string(), "kind": op.kind, "signer": op.signer, "recv": op.recv,
            "method": op.method, "args": args_of(Some(&op.args)), "deposit": op.deposit.to_string(),
            "gas_tgas": op.gas, "label": op.label, "probe": self.probe,
            "replies": op.replies.iter().map(|(s, m, _, l)| json!({"stub": s, "method": m, "does": l})).collect::<Vec<_>>(),
            "faults": op.faults.iter().map(|(_, _, l)| l.clone()).collect::<Vec<_>>(),
        }));
        tx
    }

    /// One block, then the views.
    fn step(&mut self) {
        self.sim.step();
        let (s, tokens, errs) = observe(&self.sim, self.c);
        let mut pend: Vec<usize> = self
            .sim
            .pending_receipts()
            .iter()
            .filter(|p| !p.predecessor_id.is_system())
            .filter_map(|p| self.tx_op.get(&p.tx).copied())
            .collect();
        pend.sort();
        pend.dedup();
        self.blocks.push((self.sim.height(), s.clone(), tokens, errs, pend, self.sim.timestamp_ns()));
        self.st = s;
    }

    /// A probe step: the operation and everything it spawns run before the next one is chosen.
    fn go(&mut self, op: Op) {
        let tx = self.submit(op);
        for k in 0..16 {
            self.step();
            if k >= 1 && !self.sim.pending_receipts().iter().any(|p| p.tx == tx && !p.predecessor_id.is_system()) {
                break;
            }
        }
    }

    fn bal(&self, t: &str, who: &str) -> u128 {
        ledger_of(&self.st, &ft_id(t), who)
    }

    /// An amount `who` can spend of `t` (at most half of the balance, so that probes can spend twice).
    fn some_of(&mut self, t: &str, who: &str) -> u128 {
        let b = self.bal(t, who);
        if b < 2 { 1 } else { 1 + self.rng.upto(b / 2 - 1) }
    }

    /// The standard token or the scripted one, whichever `who` has a ledger balance of; the scripted
    /// token notifies a deposit first when it has neither.
    fn funded(&mut self, who: &'static str) -> &'static str {
        for t in [TOKEN, STUB] {
            let b = self.bal(t, who);
            if b > 1000 && b < u128::MAX / 4 {
                return t;
            }
        }
        let a = 1_000_000 + self.rng.upto(near(1));
        self.go(stub_deposit_op(who, &a.to_string(), ""));
        STUB
    }

    /// A withdrawal by `who` that passes every check except the one a probe is about.
    fn plain_withdraw(&mut self, who: &'static str, t: &'static str) -> Op {
        let a = self.some_of(t, who);
        let to = *self.rng.pick(&USERS);
        let mut op = Op::new("withdraw", who, INTENTS, "ft_withdraw", json!({"token": t, "receiver_id": to, "amount": a.to_string()})).dep(1);
        op.label = format!("{who} withdraws {a} of {t} to {to}");
        op
    }

    fn plain_move(&mut self, who: &'static str, t: &'static str) -> Op {
        let a = self.some_of(t, who);
        let to = *self.rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], GHOST].iter().copied().filter(|x| *x != who).collect::<Vec<_>>());
        let tid = ft_id(t);
        let mut op = Op::new("transfer", who, INTENTS, "mt_transfer", json!({"receiver_id": to, "token_id": tid, "amount": a.to_string()})).dep(1);
        op.label = format!("{who} moves {a} of {tid} to {to} inside the ledger");
        op
    }

    fn signed_withdraw(&mut self, who: &'static str, t: &'static str) -> Op {
        let a = self.some_of(t, who);
        let to = *self.rng.pick(&USERS);
        let i = json!({"intent": "ft_withdraw", "token": t, "receiver_id": to, "amount": a.to_string()});
        intent_single(&self.sim, &mut self.rng, who, vec![i], &format!("ft_withdraw {a} of {t} to {to}"))
    }

    fn signed_move(&mut self, who: &'static str, t: &'static str) -> Op {
        let a = self.some_of(t, who);
        let to = *self.rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], GHOST].iter().copied().filter(|x| *x != who).collect::<Vec<_>>());
        let mut tokens = Map::new();
        tokens.insert(ft_id(t), json!(a.to_string()));
        let i = json!({"intent": "transfer", "receiver_id": to, "tokens": tokens});
        intent_single(&self.sim, &mut self.rng, who, vec![i], &format!("transfer {a} of {} to {to}", ft_id(t)))
    }

    fn signed_auth(&mut self, who: &'static str, enable: bool) -> Op {
        let i = json!({"intent": "set_auth_by_predecessor_id", "enabled": enable});
        intent_single(&self.sim, &mut self.rng, who, vec![i], &format!("set_auth_by_predecessor_id {enable}"))
    }

    fn forced_withdraw(&mut self, by: &str, victim: &'static str, t: &'static str) -> Op {
        let a = self.some_of(t, victim);
        let to = *self.rng.pick(&[USERS[1], USERS[2], FORCER]);
        let args = json!({"owner_id": victim, "token": t, "receiver_id": to, "amount": a.to_string()});
        let mut op = Op::new("force_withdraw", by, INTENTS, "ft_force_withdraw", args).dep(1);
        op.label = format!("{by} force-withdraws {a} of {t} from {victim} to {to}");
        op
    }

    /// A caller that holds one of the roles `method` requires (`right`), or one that holds none.
    fn caller(&mut self, method: &str, right: bool) -> &'static str {
        pick_caller(&mut self.rng, &self.st, method, if right { 100 } else { 0 })
    }
}

/// The probes: short scripted sequences, each built so that one guard is the only reason a call
/// fails. The operations of a probe run one after another, each to its end.
const PROBES: [&str; 11] = [
    "auth_flag", "intents_pause", "pause_roles", "lock_roles", "forced", "grants", "bounds", "replies", "role_sweep", "keys",
    "edges",
];

fn run_probe(r: &mut Run, which: u64) {
    let name = PROBES[which as usize % PROBES.len()];
    r.probe = Some(name);
    match name {
        "auth_flag" => probe_auth_flag(r),
        "intents_pause" => probe_intents_pause(r),
        "pause_roles" => probe_pause_roles(r),
        "lock_roles" => probe_lock_roles(r),
        "forced" => probe_forced(r),
        "grants" => probe_grants(r),
        "bounds" => probe_bounds(r),
        "role_sweep" => probe_role_sweep(r),
        "keys" => probe_keys(r),
        "edges" => probe_edges(r),
        _ => probe_replies(r),
    }
    r.probe = None;
}

/// Withdrawals and transfers by an account whose auth-by-predecessor flag is off.
fn probe_auth_flag(r: &mut Run) {
    let u = *r.rng.pick(&USERS);
    let t = r.funded(u);
    let op = match r.rng.below(3) {
        0 => auth_self_op(u),
        1 => {
            let by = r.caller("force_disable_auth_by_predecessor_ids", true);
            auth_force_op(by, &[u], false)
        }
        _ => r.signed_auth(u, false),
    };
    r.go(op);
    let op = r.plain_withdraw(u, t);
    r.go(op);
    let op = r.plain_move(u, t);
    r.go(op);
    r.go(auth_self_op(u));
    let op = r.signed_move(u, t);
    r.go(op);
    let wrong = r.caller("force_enable_auth_by_predecessor_ids", false);
    r.go(auth_force_op(wrong, &[u], true));
    let op = if r.rng.chance(50) {
        r.signed_auth(u, true)
    } else {
        let by = r.caller("force_enable_auth_by_predecessor_ids", true);
        auth_force_op(by, &[u], true)
    };
    r.go(op);
    let op = r.plain_withdraw(u, t);
    r.go(op);
}

/// Signed intents while the feature `intents` is paused.
fn probe_intents_pause(r: &mut Run) {
    let u = *r.rng.pick(&USERS);
    let t = r.funded(u);
    let by = r.caller("pa_pause_feature", true);
    r.go(pause_op(by, "intents", true));
    let op = r.signed_withdraw(u, t);
    r.go(op);
    let op = r.signed_move(u, t);
    r.go(op);
    if r.bal(WRAP, u) > 4 {
        let a = 1 + r.rng.upto(r.bal(WRAP, u) / 4);
        let i = json!({"intent": "native_withdraw", "receiver_id": USERS[1], "amount": a.to_string()});
        let op = intent_single(&r.sim, &mut r.rng, u, vec![i], &format!("native_withdraw {a} to {}", USERS[1]));
        r.go(op);
    }
    let op = r.plain_withdraw(u, t);
    r.go(op);
    let by = r.caller("pa_unpause_feature", true);
    r.go(pause_op(by, "intents", false));
    let op = r.signed_withdraw(u, t);
    r.go(op);
}

/// Who may pause and unpause; what a pause key stops (the method) and what it does not (the same
/// action through a signed intent).
fn probe_pause_roles(r: &mut Run) {
    let key = *r.rng.pick(&["ft_withdraw", "mt_transfer", "ft_on_transfer", "intents", "mt_withdraw", "ALL"]);
    let u = *r.rng.pick(&USERS);
    let t = r.funded(u);
    r.go(pause_op(UNPAUSE1, key, true));
    let wrong = r.caller("pa_pause_feature", false);
    r.go(pause_op(wrong, key, true));
    let right = *r.rng.pick(&[PAUSE1, PAUSE1, DAO]);
    r.go(pause_op(right, key, true));
    r.go(pause_op(PAUSE1, key, false));
    let wrong = r.caller("pa_unpause_feature", false);
    r.go(pause_op(wrong, key, false));
    match key {
        "ft_withdraw" => {
            let op = r.plain_withdraw(u, t);
            r.go(op);
            let op = r.signed_withdraw(u, t);
            r.go(op);
        }
        "mt_transfer" => {
            let op = r.plain_move(u, t);
            r.go(op);
            let op = r.signed_move(u, t);
            r.go(op);
        }
        "ft_on_transfer" => {
            let a = 1 + r.rng.upto(near(1));
            r.go(stub_deposit_op(u, &a.to_string(), ""));
        }
        "intents" => {
            let op = r.signed_move(u, t);
            r.go(op);
            let op = r.plain_withdraw(u, t);
            r.go(op);
        }
        _ => {
            let op = r.plain_withdraw(u, t);
            r.go(op);
        }
    }
    let right = *r.rng.pick(&[UNPAUSE1, UNPAUSE1, DAO]);
    r.go(pause_op(right, key, false));
}

/// Who may lock and unlock an account; what a locked account cannot do and what a forced
/// withdrawal still can.
fn probe_lock_roles(r: &mut Run) {
    let a = *r.rng.pick(&[USERS[1], USERS[2], USERS[3]]);
    let t = r.funded(a);
    if r.bal(WRAP, a) < 1000 {
        // some wNEAR in the ledger, for an unwrap signed by the locked account
        let x = near(1) / 1000 + r.rng.upto(near(1) / 1000);
        let mut op = Op::new("deposit", a, WRAP, "ft_transfer_call", json!({"receiver_id": INTENTS, "amount": x.to_string(), "msg": ""})).dep(1);
        op.label = format!("{a} deposits {x} of {WRAP} with msg \"\"");
        r.go(op);
    }
    r.go(lock_op(UNLOCK1, INTENTS, a, true));
    let wrong = r.caller("force_lock_account", false);
    r.go(lock_op(wrong, INTENTS, a, true));
    let right = *r.rng.pick(&[LOCK1, LOCK1, ACCTMGR, DAO]);
    r.go(lock_op(right, INTENTS, a, true));
    let op = r.plain_withdraw(a, t);
    r.go(op);
    let op = r.signed_move(a, t);
    r.go(op);
    if r.bal(WRAP, a) > 4 {
        let x = 1 + r.rng.upto(r.bal(WRAP, a) / 4);
        let i = json!({"intent": "native_withdraw", "receiver_id": USERS[0], "amount": x.to_string()});
        let op = intent_single(&r.sim, &mut r.rng, a, vec![i], &format!("native_withdraw {x} to {}", USERS[0]));
        r.go(op);
    }
    r.go(auth_self_op(a));
    let op = r.signed_auth(a, false);
    r.go(op);
    let by = *r.rng.pick(&[FORCER, DAO]);
    let op = r.forced_withdraw(by, a, t);
    r.go(op);
    r.go(lock_op(LOCK1, INTENTS, a, false));
    let wrong = r.caller("force_unlock_account", false);
    r.go(lock_op(wrong, INTENTS, a, false));
    let right = *r.rng.pick(&[UNLOCK1, UNLOCK1, ACCTMGR, DAO]);
    r.go(lock_op(right, INTENTS, a, false));
    let op = r.plain_withdraw(a, t);
    r.go(op);
}

/// Forced withdrawal and forced internal transfer by callers of every class.
fn probe_forced(r: &mut Run) {
    let v = *r.rng.pick(&USERS);
    let t = r.funded(v);
    for _ in 0..2 {
        let wrong = r.caller("ft_force_withdraw", false);
        let op = r.forced_withdraw(wrong, v, t);
        r.go(op);
    }
    let op = r.forced_withdraw(DAO, v, t);
    r.go(op);
    let op = r.forced_withdraw(FORCER, v, t);
    r.go(op);
    let to = *r.rng.pick(&[USERS[0], USERS[1], USERS[2], USERS[3], GHOST].iter().copied().filter(|x| *x != v).collect::<Vec<_>>());
    let variant = r.rng.below(4);
    let wrong = r.caller("mt_force_transfer", false);
    let a = r.some_of(t, v);
    let op = mt_force_op(&mut r.rng, wrong, v, &ft_id(t), to, a, variant);
    r.go(op);
    let right = *r.rng.pick(&[DAO, FORCER]);
    let a = r.some_of(t, v);
    let op = mt_force_op(&mut r.rng, right, v, &ft_id(t), to, a, variant);
    r.go(op);
    let a = r.some_of(t, v);
    let op = mt_force_op(&mut r.rng, right, v, &ft_id(t), to, a, variant + 1);
    r.go(op);
}

/// A role is granted to an account and revoked again; before, between and after, the account
/// calls a method the role guards.
fn probe_grants(r: &mut Run) {
    let role = *r.rng.pick(&[
        "PauseManager", "UnpauseManager", "UnrestrictedWithdrawer", "UnrestrictedAccountLocker", "UnrestrictedAccountUnlocker",
        "UnrestrictedAccountManager", "DAO",
    ]);
    let u = *r.rng.pick(&[USERS[1], USERS[2], USERS[3]]);
    let t = r.funded(u);
    let key = *r.rng.pick(&["ft_withdraw", "mt_transfer", "mt_withdraw"]);
    // what TEMP tries with the role, and what has to be in place for the attempt to change something
    let use_role = |r: &mut Run| -> Op {
        match role {
            "PauseManager" | "DAO" => pause_op(TEMP, key, true),
            "UnpauseManager" => pause_op(TEMP, key, false),
            "UnrestrictedWithdrawer" => r.forced_withdraw(TEMP, u, t),
            "UnrestrictedAccountUnlocker" => lock_op(TEMP, INTENTS, u, false),
            _ => lock_op(TEMP, INTENTS, u, true),
        }
    };
    let prepare = |r: &mut Run| match role {
        "UnpauseManager" => r.go(pause_op(PAUSER, key, true)),
        "UnrestrictedAccountUnlocker" => r.go(lock_op(LOCKER, INTENTS, u, true)),
        _ => {}
    };
    let tidy = |r: &mut Run| match role {
        "PauseManager" | "DAO" | "UnpauseManager" => r.go(pause_op(PAUSER, key, false)),
        "UnrestrictedWithdrawer" => {}
        _ => r.go(lock_op(LOCKER, INTENTS, u, false)),
    };
    prepare(r);
    let op = use_role(r);
    r.go(op);
    let wrong = *r.rng.pick(&[DAO, FEES1, UPGR1, USERS[1], UNREG, PAUSER, FORCER]);
    r.go(acl_op(wrong, "acl_grant_role", Some(role), Some(TEMP)));
    // three ways to the role: granted by the super-admin, granted by an admin of the role,
    // or granted by TEMP to itself after it was made an admin of the role or a super-admin
    let via = r.rng.below(4);
    match via {
        0 if ROLEADMIN_OF.contains(&role) => r.go(acl_op(ROLEADMIN, "acl_grant_role", Some(role), Some(TEMP))),
        1 => {
            r.go(acl_op(ADMIN, "acl_add_admin", Some(role), Some(TEMP)));
            r.go(acl_op(TEMP, "acl_grant_role", Some(role), Some(TEMP)));
        }
        2 => {
            r.go(acl_op(ADMIN, "acl_add_super_admin", None, Some(TEMP)));
            r.go(acl_op(TEMP, "acl_grant_role", Some(role), Some(TEMP)));
        }
        _ => r.go(acl_op(ADMIN, "acl_grant_role", Some(role), Some(TEMP))),
    }
    tidy(r);
    prepare(r);
    let op = use_role(r);
    r.go(op);
    let wrong = *r.rng.pick(&[DAO, FEES1, UPGR1, USERS[1], UNREG, PAUSER, FORCER]);
    r.go(acl_op(wrong, "acl_revoke_role", Some(role), Some(TEMP)));
    if r.rng.chance(50) {
        r.go(acl_op(TEMP, "acl_renounce_role", Some(role), None));
    } else {
        r.go(acl_op(ADMIN, "acl_revoke_role", Some(role), Some(TEMP)));
    }
    match via {
        1 => r.go(acl_op(ADMIN, "acl_revoke_admin", Some(role), Some(TEMP))),
        2 => r.go(acl_op(ADMIN, "acl_revoke_super_admin", None, Some(TEMP))),
        _ => {}
    }
    tidy(r);
    prepare(r);
    let op = use_role(r);
    r.go(op);
    tidy(r);
}

/// A payload of `signer` with the given intents, signed with the key of `key_of`.
fn intent_signed_with(sim: &Sim, rng: &mut Rng, signer: &str, key_of: &str, intents: Vec<Value>, what: &str) -> Op {
    let relayer = *rng.pick(&[USERS[0], UNREG, RECVS[0]]);
    let payload = json!({
        "signer_id": signer, "verifying_contract": INTENTS, "deadline": "2100-01-01T00:00:00Z",
        "nonce": fresh_nonce(rng), "intents": intents,
    });
    let text = payload.to_string();
    let sk = sim.secret_key(key_of);
    let item = json!({
        "standard": "raw_ed25519", "payload": text,
        "public_key": sk.public_key().to_string(), "signature": sk.sign(text.as_bytes()).to_string(),
    });
    let mut op = Op::new("intent", relayer, INTENTS, "execute_intents", json!({"signed": [item]}));
    op.label = format!("{relayer} relays signed intents: {what}; [signed by {signer} with the key of {key_of}]");
    op
}

/// `add_public_key` / `remove_public_key` called by `who` with the public key of `key_of`.
fn key_op(sim: &Sim, who: &str, key_of: &str, add: bool) -> Op {
    let m = if add { "add_public_key" } else { "remove_public_key" };
    let pk = sim.secret_key(key_of).public_key().to_string();
    let mut op = Op::new("key", who, INTENTS, m, json!({"public_key": pk})).dep(1);
    op.label = format!("{who} calls {m} with the key of {key_of}");
    op
}

/// Public keys. An account adds and removes keys, and a payload signed with a key is accepted exactly
/// while that key is registered for the signer: a key that is there cannot be added, a key that is not
/// there cannot be removed; neither call runs for an account whose auth-by-predecessor flag is off or
/// that is locked; a locked account's payload is refused even when it has no intents.
fn probe_keys(r: &mut Run) {
    let u = *r.rng.pick(&[USERS[1], USERS[2], USERS[3]]);
    let v = *r.rng.pick(&USERS.iter().copied().filter(|x| *x != u).collect::<Vec<_>>());
    let nothing = |r: &mut Run, key_of: &'static str| -> Op {
        intent_signed_with(&r.sim, &mut r.rng, u, key_of, vec![], "no intents")
    };
    let key = |r: &mut Run, key_of: &'static str, add: bool| -> Op { key_op(&r.sim, u, key_of, add) };
    let op = key(r, u, true);
    r.go(op);
    let op = key(r, v, false);
    r.go(op);
    // the key of another account: refused, added, accepted, removed, refused
    let op = nothing(r, v);
    r.go(op);
    let op = key(r, v, true);
    r.go(op);
    let op = nothing(r, v);
    r.go(op);
    let op = key(r, v, false);
    r.go(op);
    let op = nothing(r, v);
    r.go(op);
    // the account's own key: removed, refused, added back, accepted
    let op = key(r, u, false);
    r.go(op);
    let op = nothing(r, u);
    r.go(op);
    let op = key(r, u, true);
    r.go(op);
    let op = nothing(r, u);
    r.go(op);
    if r.rng.chance(50) {
        // with the auth-by-predecessor flag off
        r.go(auth_self_op(u));
        let op = key(r, v, true);
        r.go(op);
        let op = key(r, u, false);
        r.go(op);
        r.go(auth_force_op(LOCKER, &[u], true));
    } else {
        // locked
        r.go(lock_op(LOCKER, INTENTS, u, true));
        let op = key(r, v, true);
        r.go(op);
        let op = key(r, u, false);
        r.go(op);
        let op = nothing(r, u);
        r.go(op);
        r.go(lock_op(LOCKER, INTENTS, u, false));
    }
}

/// Transfer calls and the role table at their edges. A receiver that already holds the token is sent an
/// amount and asks for more than that amount back. An `mt_resolve_transfer` runs out of gas. An admin entry
/// that an account without the permission tries to revoke, and that its holder renounces. The super-admin
/// role handed over and back.
fn probe_edges(r: &mut Run) {
    let u = *r.rng.pick(&[USERS[1], USERS[2], USERS[3]]);
    let t = r.funded(u);
    let tid = ft_id(t);
    let to = RECVS[0];
    let a = r.some_of(t, u);
    let mut op = Op::new("transfer", u, INTENTS, "mt_transfer", json!({"receiver_id": to, "token_id": tid, "amount": a.to_string()})).dep(1);
    op.label = format!("{u} moves {a} of {tid} to {to} inside the ledger");
    r.go(op);
    let b = r.some_of(t, u);
    let ask = b.saturating_add(1 + r.rng.upto(a));
    let mut op = Op::new("transfer_call", u, INTENTS, "mt_transfer_call", json!({"receiver_id": to, "token_id": tid, "amount": b.to_string(), "msg": ""})).dep(1);
    let l = format!("returns [\"{ask}\"], more than it was sent");
    op.label = format!("{u} moves {b} of {tid} to {to} inside the ledger with mt_transfer_call; receiver: {l}");
    op.replies.push((to.into(), "mt_on_transfer".into(), Reply::json(vec![ask.to_string()]), l));
    r.go(op);
    let d = r.some_of(t, u);
    let mut op = Op::new("transfer_call", u, INTENTS, "mt_transfer_call", json!({"receiver_id": to, "token_id": tid, "amount": d.to_string(), "msg": ""})).dep(1);
    let l = format!("returns [\"{d}\"]");
    op.label = format!("{u} moves {d} of {tid} to {to} inside the ledger with mt_transfer_call; receiver: {l}");
    op.replies.push((to.into(), "mt_on_transfer".into(), Reply::json(vec![d.to_string()]), l));
    op.faults.push((Receipts::callback("mt_resolve_transfer"), Fault::OutOfGas, "mt_resolve_transfer runs out of gas".into()));
    r.go(op);
    let role = *r.rng.pick(&["PauseManager", "UnpauseManager", "UnrestrictedWithdrawer", "UnrestrictedAccountLocker"]);
    r.go(acl_op(ADMIN, "acl_add_admin", Some(role), Some(TEMP)));
    let wrong = *r.rng.pick(&[DAO, FEES1, UPGR1, USERS[1], UNREG, PAUSER, FORCER]);
    r.go(acl_op(wrong, "acl_revoke_admin", Some(role), Some(TEMP)));
    r.go(acl_op(TEMP, "acl_renounce_admin", Some(role), None));
    r.go(acl_op(ADMIN, "acl_transfer_super_admin", None, Some(TEMP)));
    r.go(acl_op(ADMIN, "acl_add_super_admin", None, Some(UNREG)));
    r.go(acl_op(TEMP, "acl_transfer_super_admin", None, Some(ADMIN)));
}

/// Amounts at and next to the `u128` bounds, on the ledger id of the scripted token.
fn probe_bounds(r: &mut Run) {
    let (u, v) = (*r.rng.pick(&[USERS[0], USERS[1]]), *r.rng.pick(&[USERS[2], USERS[3]]));
    let tid = ft_id(STUB);
    let room = u128::MAX - r.st.supply.get(&tid).copied().unwrap_or(0);
    let d = *r.rng.pick(&[0u128, 1, 2, 7]);
    if room > d {
        r.go(stub_deposit_op(u, &(room - d).to_string(), ""));
    }
    if d > 0 {
        r.go(stub_deposit_op(v, &(d + 1).to_string(), ""));
        r.go(stub_deposit_op(v, &d.to_string(), ""));
    }
    r.go(stub_deposit_op(v, "1", ""));
    r.go(stub_deposit_op(u, U128_OVER, ""));
    let b = r.bal(STUB, u);
    let over = b.saturating_add(1);
    let mut op = Op::new("transfer", u, INTENTS, "mt_transfer", json!({"receiver_id": v, "token_id": tid, "amount": over.to_string()})).dep(1);
    op.label = format!("{u} moves {over} of {tid} to {v} inside the ledger");
    r.go(op);
    let mut op = Op::new("transfer", u, INTENTS, "mt_transfer", json!({"receiver_id": v, "token_id": tid, "amount": b.to_string()})).dep(1);
    op.label = format!("{u} moves {b} of {tid} to {v} inside the ledger");
    r.go(op);
    // a withdrawal whose refund would lift the supply over the bound: the callback is held back
    // while the scripted token notifies a deposit that fills the supply up
    let b = r.bal(STUB, v);
    if b > 2 && r.rng.chance(60) {
        let x = 1 + r.rng.upto(b / 2);
        let args = json!({"token": STUB, "receiver_id": u, "amount": x.to_string(), "msg": ""});
        let mut op = Op::new("withdraw", v, INTENTS, "ft_withdraw", args).dep(1);
        op.replies.push((STUB.into(), "ft_transfer_call".into(), Reply::json("0"), "returns \"0\"".into()));
        op.faults.push((Receipts::callback("ft_resolve_withdraw"), Fault::Hold(4), "ft_resolve_withdraw held 4 blocks".into()));
        op.label = format!("{v} withdraws {x} of {STUB} to {u} by ft_transfer_call; the scripted token: returns \"0\"");
        r.submit(op);
        r.step();
        r.step();
        r.go(stub_deposit_op(u, &x.to_string(), ""));
    }
    // back to modest numbers: the holders withdraw what they have, the scripted token accepts
    for who in [u, v] {
        let b = r.bal(STUB, who);
        if b > 0 {
            let keep = if b > near(1) { near(1) } else { 0 };
            let mut op = Op::new("withdraw", who, INTENTS, "ft_withdraw", json!({"token": STUB, "receiver_id": who, "amount": (b - keep).to_string()})).dep(1);
            op.label = format!("{who} withdraws {} of {STUB} to itself", b - keep);
            r.go(op);
        }
    }
}

/// One guarded method is called, with well-formed arguments, by the holder of each of the twelve
/// roles in turn and by an account with no role. For `upgrade` the two holders that could run it
/// are left out.
fn probe_role_sweep(r: &mut Run) {
    let m = *r.rng.pick(&GUARDED);
    let u = *r.rng.pick(&[USERS[1], USERS[2], USERS[3]]);
    let t = r.funded(u);
    let key = *r.rng.pick(&["mt_withdraw", "mt_on_transfer"]);
    let variant = r.rng.below(4);
    match m {
        "pa_unpause_feature" => r.go(pause_op(PAUSER, key, true)),
        "force_unlock_account" => r.go(lock_op(LOCKER, INTENTS, u, true)),
        "force_enable_auth_by_predecessor_ids" => r.go(auth_force_op(LOCKER, &[u], false)),
        _ => {}
    }
    let callers: Vec<&'static str> = SINGLE.iter().map(|x| x.1).chain([UNREG]).collect();
    for by in callers {
        if m == "upgrade" && has_any(&r.st, by, guard_roles(m)) {
            continue;
        }
        let op = match m {
            "pa_pause_feature" => pause_op(by, key, true),
            "pa_unpause_feature" => pause_op(by, key, false),
            "force_lock_account" => lock_op(by, INTENTS, u, true),
            "force_unlock_account" => lock_op(by, INTENTS, u, false),
            "force_disable_auth_by_predecessor_ids" => auth_force_op(by, &[u], false),
            "force_enable_auth_by_predecessor_ids" => auth_force_op(by, &[u], true),
            "ft_force_withdraw" => r.forced_withdraw(by, u, t),
            "mt_force_withdraw" => {
                let inner = ft_id(TOKEN);
                let a = ledger_of(&r.st, &mt_id(MT, &inner), u).max(2) / 2;
                let args = json!({"owner_id": u, "token": MT, "receiver_id": USERS[0], "token_ids": [inner], "amounts": [a.to_string()]});
                let mut op = Op::new("force_withdraw", by, INTENTS, "mt_force_withdraw", args).dep(1);
                op.label = format!("{by} force-withdraws {a} of {MT}:{inner} from {u} to {}", USERS[0]);
                op
            }
            "nft_force_withdraw" => {
                let args = json!({"owner_id": u, "token": USERS[2], "receiver_id": USERS[1], "token_id": "1"});
                let mut op = Op::new("force_withdraw", by, INTENTS, "nft_force_withdraw", args).dep(1);
                op.label = format!("{by} calls nft_force_withdraw for a token nobody holds");
                op
            }
            "mt_force_transfer" | "mt_force_batch_transfer" | "mt_force_transfer_call" | "mt_force_batch_transfer_call" => {
                let v = ["mt_force_transfer", "mt_force_batch_transfer", "mt_force_transfer_call", "mt_force_batch_transfer_call"]
                    .iter()
                    .position(|x| *x == m)
                    .unwrap_or(variant as usize) as u64;
                let a = r.some_of(t, u);
                mt_force_op(&mut r.rng, by, u, &ft_id(t), GHOST, a, v)
            }
            _ => outside_op(&r.sim, &mut r.rng, m, by),
        };
        r.go(op);
    }
    // back to where it was
    match m {
        "pa_pause_feature" | "pa_unpause_feature" => r.go(pause_op(PAUSER, key, false)),
        "force_lock_account" | "force_unlock_account" => r.go(lock_op(LOCKER, INTENTS, u, false)),
        "force_disable_auth_by_predecessor_ids" | "force_enable_auth_by_predecessor_ids" => r.go(auth_force_op(LOCKER, &[u], true)),
        _ => {}
    }
}

/// The token's answers at the edges of what `ft_resolve_withdraw` accepts.
fn probe_replies(r: &mut Run) {
    let u = *r.rng.pick(&USERS);
    if r.bal(STUB, u) < 1_000_000 || r.bal(STUB, u) > u128::MAX / 4 {
        let a = 1_000_000 + r.rng.upto(near(1));
        r.go(stub_deposit_op(u, &a.to_string(), ""));
    }
    let calls = ["len43", "len44", "len45", "len46", "bad44", "bad45", "full44", "over", "plus"];
    for k in 0..5 {
        let (mode, call) = if k == 4 { ("value", false) } else { (*r.rng.pick(&calls), true) };
        let a = 2 + r.some_of(STUB, u);
        let mut args = json!({"token": STUB, "receiver_id": USERS[0], "amount": a.to_string()});
        if call {
            args["msg"] = json!("");
        }
        let mut op = Op::new("withdraw", u, INTENTS, "ft_withdraw", args).dep(1);
        let (reply, l) = stub_reply_mode(mode, a, &mut r.rng);
        op.label = format!(
            "{u} withdraws {a} of {STUB} by {}; the scripted token: {l}",
            if call { "ft_transfer_call" } else { "ft_transfer" }
        );
        op.replies.push((STUB.into(), (if call { "ft_transfer_call" } else { "ft_transfer" }).into(), reply, l));
        r.go(op);
    }
}

fn run_trace(base: &World, seed: u64, id: u64) -> Value {
    let c = &base.cfg;
    let sim = base.sim.clone();
    let h0 = sim.height();
    let (init, tokens0, errs0) = observe(&sim, c);
    let mut r = Run {
        sim,
        rng: Rng(seed ^ (id.wrapping_mul(0x9E3779B97F4A7C15)) | 1),
        c,
        st: init.clone(),
        ops: vec![],
        tx_op: HashMap::new(),
        blocks: vec![],
        pool: vec![],
        probe: None,
    };
    let n_fund = 3 + r.rng.below(6);
    let n_ops = n_fund + 12 + r.rng.below(40);
    let n_probes = match r.rng.below(100) {
        0..=24 => 0,
        25..=69 => 1,
        _ => 2,
    };
    let probes: Vec<(u64, u64)> = (0..n_probes).map(|_| (n_fund + r.rng.below(n_ops - n_fund), r.rng.below(PROBES.len() as u64))).collect();
    for k in 0..n_ops {
        for (at, which) in &probes {
            if *at == k {
                run_probe(&mut r, *which);
            }
        }
        let burst = if r.rng.chance(15) { 2 + r.rng.below(3) } else { 1 };
        for _ in 0..burst {
            let op = if k < n_fund { fund_op(&r.sim, &mut r.rng) } else { gen_op(&r.sim, &mut r.rng, &r.st, r.c, &mut r.pool) };
            r.submit(op);
        }
        let gap = *r.rng.pick(&[0u64, 1, 1, 1, 2, 2, 3, 5]);
        for _ in 0..gap {
            r.step();
        }
    }
    let mut guard = 0;
    while !r.sim.is_idle() && guard < 300 {
        r.step();
        guard += 1;
    }
    let Run { sim, ops, tx_op, blocks, .. } = r;
    let settled = sim.is_idle();

    let all = sim.receipts_in(h0 + 1..);
    // who produces which data
    let ser: Vec<Value> = all.iter().map(|r| serde_json::to_value(r).unwrap_or(Value::Null)).collect();
    let mut producers: HashMap<String, Vec<usize>> = HashMap::new();
    for (i, s) in ser.iter().enumerate() {
        for d in output_data_ids(s["output_data_receivers"].as_str().unwrap_or("")) {
            producers.entry(d).or_default().push(i);
        }
    }
    let by_id: HashMap<CryptoHash, usize> = all.iter().enumerate().map(|(i, r)| (r.receipt_id, i)).collect();
    let views: HashMap<u64, usize> = blocks.iter().enumerate().map(|(i, b)| (b.0, i)).collect();
    let mut steps = vec![];
    let mut refunds = 0u64;
    let mut cur = init.clone();
    let mut mism: BTreeMap<u64, Value> = BTreeMap::new();
    let mut derive_errs: Vec<String> = vec![];
    for (i, r) in all.iter().enumerate() {
        derive_errs.extend(apply(&mut cur, r, c));
        let last_in_block = all.get(i + 1).is_none_or(|n| n.block_height != r.block_height);
        let mut src = "derived";
        if last_in_block {
            if let Some(b) = views.get(&r.block_height) {
                let seen = &blocks[*b].1;
                if *seen != cur {
                    mism.insert(r.block_height, json!({"derived": cur.json(), "views": seen.json()}));
                }
                cur = seen.clone();
                src = "views";
            }
        }
        if r.is_refund() {
            refunds += 1;
            continue;
        }
        let results: Vec<Value> = ser[i]["input_data_ids"]
            .as_array()
            .map(|ids| {
                ids.iter()
                    .map(|d| {
                        let ps = producers.get(d.as_str().unwrap_or("")).cloned().unwrap_or_default();
                        let fin = ps.iter().map(|p| &all[*p]).find(|p| !matches!(p.status, ExecutionStatus::SuccessReceiptId(_)));
                        match fin.map(|p| (&p.status, p)) {
                            Some((ExecutionStatus::SuccessValue(v), p)) => match serde_json::from_slice::<Value>(v) {
                                Ok(j) => json!({"ok": true, "json": j, "hex": hex(v), "from": p.receipt_id.to_string()}),
                                Err(_) => json!({"ok": true, "hex": hex(v), "from": p.receipt_id.to_string()}),
                            },
                            Some((ExecutionStatus::Failure(_), p)) => json!({"ok": false, "from": p.receipt_id.to_string()}),
                            _ => json!({"unknown": true}),
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();
        let calls: Vec<Value> = r
            .receipt_ids
            .iter()
            .filter_map(|x| by_id.get(x).map(|j| &all[*j]))
            .filter(|x| !x.is_refund())
            .map(|x| {
                json!({
                    "rid": x.receipt_id.to_string(), "recv": x.receiver_id.as_str(), "actions": x.actions,
                    "method": x.method_names.first(), "methods": x.method_names, "args": args_of(x.args.first()),
                    "deposit": x.deposit.as_yoctonear().to_string(), "gas": x.attached_gas.as_gas(),
                })
            })
            .collect();
        let moves: Vec<Value> = r
            .token_moves
            .iter()
            .map(|m| json!([m.token.as_str(), m.token_id, m.holder.as_ref().map(|h| h.to_string()), m.delta.to_string()]))
            .collect();
        steps.push(json!({
            "i": steps.len(), "h": r.block_height, "ts": views.get(&r.block_height).map(|b| blocks[*b].5.to_string()),
            "rid": r.receipt_id.to_string(), "tx": r.tx.to_string(),
            "op": tx_op.get(&r.tx), "pred": r.predecessor_id.as_str(), "recv": r.receiver_id.as_str(),
            "actions": r.actions, "method": r.method_names.first(), "methods": r.method_names, "args": args_of(r.args.first()),
            "deposit": r.deposit.as_yoctonear().to_string(), "gas": r.attached_gas.as_gas(),
            "gas_burnt": r.gas_burnt.as_gas(), "ok": r.is_success(), "status": status_text(r), "ret": ret_of(r),
            "callback": r.is_callback(), "results": results, "logs": r.logs, "events": events(r),
            "calls": calls, "fault": r.fault.as_ref().map(|f| f.to_string()), "held_blocks": r.held,
            "moves": moves, "state": cur.json(), "state_src": src,
        }));
    }
    let obs: Vec<Value> = blocks
        .iter()
        .map(|(h, s, tokens, errs, pend, ts)| {
            let mut o = json!({"h": h, "ts": ts.to_string(), "state": s.json(), "tokens": tokens, "pending_ops": pend});
            if !errs.is_empty() {
                o["view_errors"] = json!(errs);
            }
            if let Some(m) = mism.get(h) {
                o["derive_mismatch"] = m.clone();
            }
            o
        })
        .collect();
    let mut world = Map::new();
    world.insert("contract".into(), json!(INTENTS));
    world.insert("assets".into(), json!(c.assets.iter().map(|a| json!({"ledger": a.ledger, "contract": a.contract, "inner": a.inner})).collect::<Vec<_>>()));
    world.insert("ids".into(), json!(c.ids));
    world.insert("holders".into(), json!(c.holders));
    world.insert("private".into(), json!(PRIVATE.iter().chain(PRIVATE_MORE.iter()).collect::<Vec<_>>()));
    world.insert("scripted_token".into(), json!(STUB));
    world.insert("flag_watch".into(), json!(FLAG_WATCH));
    world.insert(
        "roles".into(),
        json!({
            "pause": PAUSER, "force_withdraw": FORCER, "lock": LOCKER, "super_admin": ADMIN, "dao": DAO,
            "pause_only": PAUSE1, "unpause_only": UNPAUSE1, "lock_only": LOCK1, "unlock_only": UNLOCK1,
            "account_manager": ACCTMGR, "fees": FEES1, "relayer_keys": RELAY1, "upgrader": UPGR1, "salts": SALT1,
            "garbage_collector": GC1, "role_admin": ROLEADMIN, "no_role_at_start": TEMP,
        }),
    );
    world.insert("keys".into(), base.keys.clone());
    world.insert("fees".into(), json!({"fee": 0, "fee_collector": ADMIN}));
    json!({
        "id": id, "seed": seed, "mock": c.mock, "h0": h0, "world": world,
        "init": {"state": init.json(), "tokens": tokens0, "view_errors": errs0, "tokens_state": base.tokens_state},
        "ops": ops, "steps": steps, "obs": obs, "settled": settled, "refund_receipts": refunds,
        "derive_errors": derive_errs,
    })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: intents-gen probe <intents.wasm> <ft.wasm> <wnear.wasm> | traces <intents.wasm> <ft.wasm> <wnear.wasm> <seed> <start> <count> [mock]";
    if args.len() < 5 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let rd = |p: &str| std::fs::read(p).unwrap_or_else(|e| panic!("{p}: {e}"));
    let (intents, ft, wnear) = (rd(&args[2]), rd(&args[3]), rd(&args[4]));
    match args[1].as_str() {
        "probe" => {
            let w = build_world(&intents, &ft, &wnear, false);
            let (st, tokens, errs) = observe(&w.sim, &w.cfg);
            let out = json!({
                "code_hash": w.sim.account(INTENTS).unwrap().code_hash.to_string(),
                "wasm_code_hash": CryptoHash::hash_bytes(&intents).to_string(),
                "height": w.sim.height(), "init_state": st.json(), "tokens": tokens, "view_errors": errs,
                "metadata": vj(&w.sim, INTENTS, "contract_source_metadata", json!({})).ok(),
            });
            println!("{}", serde_json::to_string_pretty(&out).unwrap());
        }
        "traces" => {
            let seed: u64 = args[5].parse().unwrap();
            let start: u64 = args[6].parse().unwrap();
            let count: u64 = args[7].parse().unwrap();
            let mock = args.get(8).map(String::as_str) == Some("mock");
            let w = build_world(&intents, &ft, &wnear, mock);
            std::panic::set_hook(Box::new(|_| {}));
            for id in start..start + count {
                let t = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_trace(&w, seed, id)));
                let line = match t {
                    Ok(v) => v,
                    Err(e) => {
                        let msg = e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default();
                        json!({"id": id, "seed": seed, "mock": mock, "sim_panic": msg})
                    }
                };
                println!("{}", serde_json::to_string(&line).unwrap());
            }
        }
        _ => eprintln!("{usage}"),
    }
}
