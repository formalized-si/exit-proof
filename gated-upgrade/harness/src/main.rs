//! Tests of the gated vault on the nearcore runtime (near-contract-sim).
//!
//! The world: the certificate registry (the unchanged registry wasm) on `registry.near`, the gated
//! vault (v1 build) on `vault.near`, initialised with staging duration `D`, the registry, the kind
//! `upgrade-window`, one accepted attestor and one code stager.
//!
//!   gu-test scenarios <v1.wasm> <v2.wasm> <v3.wasm> <registry.wasm>
//!       the named scenarios, each a list of steps and checks; JSON on stdout, exit 0 iff all hold
//!   gu-test traces <v1.wasm> <v2.wasm> <v3.wasm> <registry.wasm> <seed> <start> <count>
//!       random traces with a monitor that checks, from what the chain shows, the statement of
//!       the theorem on every change of the vault's code; a JSON summary on stdout
//!   gu-test info <v1.wasm> <v2.wasm> <v3.wasm> <registry.wasm>

use near_contract_sim::prelude::*;
use near_contract_sim::{CryptoHash, ExecutionStatus, ReceiptOutcome, TxOutcome};
use serde_json::{Value, json};
use std::collections::BTreeMap;

const VAULT: &str = "vault.near";
const REGISTRY: &str = "registry.near";
const REG_OWNER: &str = "regowner.near";
/// Allow-listed in the registry and accepted by the vault.
const ATTESTOR: &str = "attestor.near";
/// Allow-listed in the registry, not accepted by the vault.
const OTHER_ATTESTOR: &str = "other-attestor.near";
/// The code stager.
const GOV: &str = "gov.near";
const ALICE: &str = "alice.near";
const MALLORY: &str = "mallory.near";
const KIND: &str = "upgrade-window";
const SEC: u64 = 1_000_000_000;
/// The staging duration of the test vault: one hour.
const D: u64 = 3600 * SEC;
/// A realistic starting block timestamp (2026-11-12T00:00:00Z in nanoseconds).
const T_START: u64 = 1_794_441_600_000_000_000;

fn everyone() -> Vec<&'static str> {
    vec![REG_OWNER, ATTESTOR, OTHER_ATTESTOR, GOV, ALICE, MALLORY]
}

struct Codes {
    list: Vec<(String, Vec<u8>)>,
    registry: Vec<u8>,
}

impl Codes {
    fn new(v1: Vec<u8>, v2: Vec<u8>, v3: Vec<u8>, registry: Vec<u8>) -> Self {
        let stub = wat::parse_str(r#"(module (func (export "up_verify_state")))"#).expect("stub wat");
        let list = vec![
            ("v1".to_string(), v1),
            ("v2".to_string(), v2),
            ("v3".to_string(), v3),
            ("junk".to_string(), b"not a wasm module".to_vec()),
            ("stub".to_string(), stub),
        ];
        // v2 with a custom section appended, 1 MB in all: a valid contract that is dear to hash
        let mut list = list;
        let mut big = list[1].1.clone();
        let pad = 1_000_000usize.saturating_sub(big.len() + 10);
        big.push(0); // custom section
        let mut n = pad + 4; // payload: name length byte + "pad" + bytes
        loop {
            let b = (n & 0x7f) as u8;
            n >>= 7;
            if n == 0 { big.push(b); break; } else { big.push(b | 0x80); }
        }
        big.extend_from_slice(&[3, b'p', b'a', b'd']);
        big.extend(std::iter::repeat_n(0u8, pad));
        list.push(("big".to_string(), big));
        Codes { list, registry }
    }
    fn bytes(&self, label: &str) -> Vec<u8> {
        self.list.iter().find(|(l, _)| l == label).expect("label").1.clone()
    }
    fn hash(&self, label: &str) -> String {
        CryptoHash::hash_bytes(&self.bytes(label)).to_string()
    }
    fn label_of_hash(&self, h: &str) -> String {
        self.list.iter().find(|(l, _)| self.hash(l) == h).map(|(l, _)| l.clone()).unwrap_or_else(|| "?".into())
    }
    fn table(&self) -> Value {
        let m: BTreeMap<String, String> = self.list.iter().map(|(l, _)| (l.clone(), self.hash(l))).collect();
        json!(m)
    }
}

fn g300() -> Gas {
    Gas::from_teragas(300)
}

fn init_args(registry: &str) -> Value {
    json!({"staging_duration": D, "registry": registry, "certificate_kind": KIND,
           "attestors": [ATTESTOR], "stagers": [GOV]})
}

/// Accounts, the registry (initialised, two attestors allow-listed) and the vault's code, not
/// yet initialised.
fn bare_world(codes: &Codes) -> Sim {
    let mut sim = Sim::new();
    sim.set_timestamp_ns(T_START);
    for a in everyone() {
        sim.create_account(a, Balance::from_near(1_000));
    }
    sim.create_account(REGISTRY, Balance::from_near(100));
    sim.deploy(REGISTRY, codes.registry.clone());
    sim.call(REGISTRY, REGISTRY, "new").args_json(json!({"owner": REG_OWNER})).transact().assert_success();
    for a in [ATTESTOR, OTHER_ATTESTOR] {
        sim.call(REG_OWNER, REGISTRY, "add_attestor").args_json(json!({"account_id": a})).transact().assert_success();
    }
    sim.create_account(VAULT, Balance::from_near(100));
    sim.deploy(VAULT, codes.bytes("v1"));
    sim
}

/// The world with the vault initialised and a deposit of alice.
fn world(codes: &Codes) -> Sim {
    let mut sim = bare_world(codes);
    sim.call(VAULT, VAULT, "new").args_json(init_args(REGISTRY)).gas(g300()).transact().assert_success();
    sim.call(ALICE, VAULT, "deposit").args_json(json!({})).deposit(Balance::from_near(5)).transact().assert_success();
    let t = sim.timestamp_ns() + 10 * SEC;
    sim.pause_clock_at(t);
    sim
}

fn view(sim: &Sim, contract: &str, method: &str, args: Value) -> Option<Value> {
    let v = sim.view(contract, method, args);
    v.value().and_then(|b| serde_json::from_slice::<Value>(b).ok())
}

fn code_hash(sim: &Sim) -> String {
    sim.account(VAULT).expect("vault account").code_hash.to_string()
}

fn code_of(sim: &Sim, codes: &Codes) -> String {
    codes.label_of_hash(&code_hash(sim))
}

fn staged_hash(sim: &Sim) -> Value {
    view(sim, VAULT, "up_staged_code_hash", json!({})).unwrap_or(Value::Null)
}

fn status(sim: &Sim) -> Value {
    view(sim, VAULT, "up_get_delay_status", json!({})).unwrap_or(Value::Null)
}

/// The access-control state, sorted: super-admins, and per role the admins and the grantees.
fn acl(sim: &Sim) -> Value {
    let p = view(sim, VAULT, "acl_get_permissioned_accounts", json!({})).unwrap_or(Value::Null);
    let sorted = |v: &Value| -> Value {
        let mut xs: Vec<String> = v.as_array().into_iter().flatten().filter_map(|x| x.as_str().map(String::from)).collect();
        xs.sort();
        json!(xs)
    };
    let mut roles = BTreeMap::new();
    if let Some(m) = p["roles"].as_object() {
        for (role, v) in m {
            roles.insert(role.clone(), json!({"admins": sorted(&v["admins"]), "grantees": sorted(&v["grantees"])}));
        }
    }
    json!({"super_admins": sorted(&p["super_admins"]), "roles": roles})
}

/// What the theorem's hypotheses say about the access-control state.
fn acl_expected() -> Value {
    json!({"super_admins": [VAULT], "roles": {
        "CodeDeployer": {"admins": [], "grantees": [VAULT]},
        "CodeStager": {"admins": [], "grantees": [GOV]},
        "DurationManager": {"admins": [], "grantees": []},
    }})
}

fn gate_expected() -> Value {
    json!({"registry": REGISTRY, "kind": KIND, "attestors": [ATTESTOR]})
}

fn snap(sim: &Sim, codes: &Codes) -> Value {
    json!({
        "block_timestamp": sim.timestamp_ns().to_string(),
        "code": code_of(sim, codes), "code_hash": code_hash(sim),
        "version": view(sim, VAULT, "version", json!({})),
        "up_staged_code_hash": staged_hash(sim),
        "up_get_delay_status": status(sim),
    })
}

fn status_text(r: &ReceiptOutcome) -> String {
    match r.failure() {
        Some(f) => format!("{f:?}"),
        None => "ok".into(),
    }
}

fn ret_json(r: &ReceiptOutcome) -> Value {
    match &r.status {
        ExecutionStatus::SuccessValue(v) if !v.is_empty() => serde_json::from_slice::<Value>(v).unwrap_or(Value::Null),
        _ => Value::Null,
    }
}

/// The receipts of a transaction that carry actions (refunds left out), in execution order.
fn receipts(o: &TxOutcome) -> Vec<Value> {
    o.receipts
        .iter()
        .filter(|r| r.refund.is_none() && !r.actions.is_empty())
        .map(|r| {
            json!({
                "block": r.block_height, "block_timestamp": r.block_timestamp_ns.to_string(),
                "receiver": r.receiver_id.as_str(), "predecessor": r.predecessor_id.as_str(),
                "actions": r.actions, "methods": r.method_names,
                "ok": r.is_success(), "status": status_text(r), "logs": r.logs,
                "gas_burnt": r.gas_burnt.as_gas().to_string(),
            })
        })
        .collect()
}

fn total_gas(o: &TxOutcome) -> u64 {
    o.receipts.iter().map(|r| r.gas_burnt.as_gas()).sum::<u64>() + o.transaction.as_ref().map(|t| t.gas_burnt.as_gas()).unwrap_or(0)
}

/// The first receipt on `receiver` that calls `method`.
fn rc<'a>(rs: &'a [Value], receiver: &str, method: &str) -> Option<&'a Value> {
    rs.iter().find(|r| r["receiver"] == receiver && r["methods"].as_array().is_some_and(|m| m.iter().any(|x| x == method)))
}

fn batch(rs: &[Value]) -> Option<&Value> {
    rs.iter().find(|r| r["actions"][0] == "DeployContract")
}

fn ok(r: Option<&Value>) -> bool {
    r.is_some_and(|r| r["ok"] == json!(true))
}

fn failed_with(r: Option<&Value>, text: &str) -> bool {
    r.is_some_and(|r| r["ok"] == json!(false) && r["status"].as_str().unwrap_or("").contains(text))
}

fn block(r: Option<&Value>) -> u64 {
    r.and_then(|r| r["block"].as_u64()).unwrap_or(0)
}

/// A certificate the registry accepts. The texts say what it is: a test certificate.
fn cert(kind: &str) -> Value {
    json!({
        "kind": kind, "family": "gated vault, test build",
        "statement": "test certificate used by the harness; it certifies nothing",
        "theorems": ["GatedUpgrade.gated_code_change"], "axioms": ["propext"], "assumptions": ["test"],
        "binding": "test", "conformance": {"traces": 0, "calls": 0, "mismatches": 0, "runtime": "near-contract-sim"},
        "artifact_sha256": "0".repeat(64), "artifact_location": "test", "check_command": "./check.sh",
    })
}

/// Attests `hash` as `who`; returns the certificate's index if the registry accepted it.
fn attest(sim: &mut Sim, who: &str, hash: &str, kind: &str) -> Option<u64> {
    let before = view(sim, REGISTRY, "count", json!({})).and_then(|v| v.as_u64()).unwrap_or(0);
    let o = sim
        .call(who, REGISTRY, "attest")
        .args_json(json!({"code_hash": hash, "certificate": cert(kind)}))
        .deposit(Balance::from_near(1))
        .gas(Gas::from_teragas(100))
        .transact();
    sim.settle();
    let after = view(sim, REGISTRY, "count", json!({})).and_then(|v| v.as_u64()).unwrap_or(0);
    if o.is_success() && after == before + 1 { Some(before) } else { None }
}

fn revoke(sim: &mut Sim, who: &str, index: u64) -> bool {
    let o = sim.call(who, REGISTRY, "revoke").args_json(json!({"index": index, "reason": "test"})).transact();
    sim.settle();
    o.is_success()
}

fn stage(sim: &mut Sim, who: &str, code: Vec<u8>) -> TxOutcome {
    let o = sim.call(who, VAULT, "up_stage_code").args(code).gas(g300()).transact();
    sim.settle();
    o
}

fn deploy_certified(sim: &mut Sim, who: &str) -> TxOutcome {
    let o = sim.call(who, VAULT, "deploy_certified").args_json(json!({})).gas(g300()).transact();
    sim.settle();
    o
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
    /// Records a transaction: what the accounts executed, and the vault afterwards.
    fn tx(&mut self, sim: &Sim, codes: &Codes, what: &str, o: &TxOutcome) -> Vec<Value> {
        let rs = receipts(o);
        self.steps.push(json!({"step": what, "receipts": rs, "after": snap(sim, codes)}));
        rs
    }
    fn note(&mut self, what: &str, v: Value) {
        self.steps.push(json!({"step": what, "value": v}));
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

/// Stages `label` as gov at the paused clock; returns the block timestamp of the staging.
fn stage_now(sc: &mut Scenario, sim: &mut Sim, codes: &Codes, label: &str) -> u64 {
    let o = stage(sim, GOV, codes.bytes(label));
    let rs = sc.tx(sim, codes, &format!("gov.near: up_stage_code({label})"), &o);
    rs.first().and_then(|r| r["block_timestamp"].as_str()).and_then(|s| s.parse().ok()).unwrap_or(0)
}

fn scenarios(codes: &Codes) -> Value {
    let base = world(codes);
    let (h2, h3) = (codes.hash("v2"), codes.hash("v3"));
    let mut out = vec![];

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("certified_upgrade", "Code staged by the stager and certified by the accepted attestor is deployed by anyone's deploy_certified once the staging duration has passed, and not one nanosecond earlier. The gate, the roles and the deposits are unchanged by the upgrade.");
        let mut sim = base.clone();
        let ts = stage_now(&mut sc, &mut sim, codes, "v2");
        sc.check("the staged hash is the hash of v2 and the staging timestamp is staging time + D",
            staged_hash(&sim) == json!(h2) && status(&sim)["staging_timestamp"] == json!(ts + D));
        let idx = attest(&mut sim, ATTESTOR, &h2, KIND);
        sc.note("attestor.near: attest(hash of v2, kind upgrade-window)", json!({"index": idx}));
        sc.check("the registry stores the certificate", idx.is_some());
        sim.pause_clock_at(ts + D - 1);
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "mallory.near: deploy_certified(), 1 ns before staging + D", &o);
        sc.check("refused at once: deploy too early; the registry is not even asked",
            failed_with(rc(&rs, VAULT, "deploy_certified"), "Gate: deploy too early") && rc(&rs, REGISTRY, "get_valid_kind").is_none());
        sc.check("the code is still v1", code_of(&sim, codes) == "v1");
        sim.pause_clock_at(ts + D);
        let before = code_hash(&sim);
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "mallory.near (no role): deploy_certified() at staging + D", &o);
        sc.note("gas burnt by the whole transaction", json!(total_gas(&o).to_string()));
        sc.check("the vault asks the registry, the registry answers, the callback accepts",
            ok(rc(&rs, VAULT, "deploy_certified")) && ok(rc(&rs, REGISTRY, "get_valid_kind")) && ok(rc(&rs, VAULT, "on_certificates")));
        sc.check("the deploy batch [DeployContract, up_verify_state] succeeds, created by the vault itself",
            ok(batch(&rs)) && batch(&rs).is_some_and(|b| b["predecessor"] == VAULT && b["methods"] == json!(["up_verify_state"])));
        sc.check("the transaction as a whole succeeds", o.is_success());
        sc.check("the account's code hash changed to the hash of v2; version() = 2",
            code_hash(&sim) != before && code_hash(&sim) == h2 && view(&sim, VAULT, "version", json!({})) == Some(json!(2)));
        sc.check("after the upgrade: same gate, same roles", view(&sim, VAULT, "gate", json!({})) == Some(gate_expected()) && acl(&sim) == acl_expected());
        let five = Balance::from_near(5).as_yoctonear().to_string();
        sc.check("after the upgrade: alice's balance is intact", view(&sim, VAULT, "balance_of", json!({"account_id": ALICE})) == Some(json!(five)));
        let o = sim.call(ALICE, VAULT, "withdraw").args_json(json!({"amount": five})).transact();
        sim.settle();
        let rs = sc.tx(&sim, codes, "alice.near: withdraw(5 NEAR)", &o);
        sc.check("alice withdraws everything from the new code", ok(rc(&rs, VAULT, "withdraw")) && rs.iter().any(|r| r["receiver"] == ALICE && r["actions"] == json!(["Transfer"]) && r["ok"] == json!(true)));
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("uncertified_refused", "Staged code without a matching certificate is never deployed: no certificate at all, a certificate by an attestor the vault does not accept, a certificate of another kind, a certificate for another hash. With the matching certificate the same call deploys it.");
        let mut sim = base.clone();
        let ts = stage_now(&mut sc, &mut sim, codes, "v3");
        sim.pause_clock_at(ts + D);
        let before = code_hash(&sim);
        let refused = |sc: &mut Scenario, sim: &mut Sim, what: &str| {
            let o = deploy_certified(sim, MALLORY);
            let rs = sc.tx(sim, codes, &format!("mallory.near: deploy_certified() — {what}"), &o);
            let good = ok(rc(&rs, REGISTRY, "get_valid_kind"))
                && failed_with(rc(&rs, VAULT, "on_certificates"), "Gate: no valid upgrade-window certificate from an accepted attestor")
                && batch(&rs).is_none() && !o.is_success() && code_hash(sim) == before;
            sc.check(&format!("{what}: the callback refuses, no deploy batch, the code hash does not change"), good);
        };
        refused(&mut sc, &mut sim, "no certificate");
        let i = attest(&mut sim, OTHER_ATTESTOR, &h3, KIND);
        sc.note("other-attestor.near (allow-listed in the registry, not accepted by the vault): attest(hash of v3, upgrade-window)", json!({"index": i}));
        refused(&mut sc, &mut sim, "certificate by an attestor the vault does not accept");
        let i = attest(&mut sim, ATTESTOR, &h3, "exit");
        sc.note("attestor.near: attest(hash of v3, kind exit)", json!({"index": i}));
        refused(&mut sc, &mut sim, "certificate of another kind");
        let i = attest(&mut sim, ATTESTOR, &h2, KIND);
        sc.note("attestor.near: attest(hash of v2, upgrade-window)", json!({"index": i}));
        refused(&mut sc, &mut sim, "certificate for another hash");
        let o = attest(&mut sim, MALLORY, &h3, KIND);
        sc.check("mallory.near cannot attest: not an attestor of the registry", o.is_none());
        let i = attest(&mut sim, ATTESTOR, &h3, KIND);
        sc.note("attestor.near: attest(hash of v3, upgrade-window)", json!({"index": i}));
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "mallory.near: deploy_certified() — with the matching certificate", &o);
        sc.check("control: with the matching certificate the same call deploys v3", ok(batch(&rs)) && code_of(&sim, codes) == "v3");
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("restaged_between_check_and_deploy", "The staged code is replaced, re-staged or removed after deploy_certified asked the registry and before the callback: the callback deploys nothing. Replaced after the callback: the batch installs the code that was checked.");
        // v2 staged, certified, delay passed; one in-flight deploy_certified per case
        let mut sim0 = base.clone();
        let ts = stage_now(&mut sc, &mut sim0, codes, "v2");
        attest(&mut sim0, ATTESTOR, &h2, KIND);
        sim0.pause_clock_at(ts + D);
        for (case, input, late, panic_text) in [
            ("another code (v3), whose own delay starts", codes.bytes("v3"), false, "Upgradable: Deploy code too early"),
            ("another code (v3), and the callback runs only after that code's delay", codes.bytes("v3"), true, "Upgradable: Cannot deploy due to wrong hash"),
            ("the same code (v2), which restarts its delay", codes.bytes("v2"), false, "Upgradable: Deploy code too early"),
            ("empty input (the staged code is removed)", vec![], false, "Upgradable: staging timestamp isn't set"),
        ] {
            let mut sim = sim0.clone();
            let hx = sim.call(MALLORY, VAULT, "deploy_certified").args_json(json!({})).gas(g300()).submit();
            sim.step(); // the transaction becomes a receipt
            let hs = sim.call(GOV, VAULT, "up_stage_code").args(input).gas(g300()).submit();
            sim.step(); // deploy_certified runs
            sim.step(); // the registry answers; the staging runs
            if late {
                // not something a chain does within two blocks: the clock is moved by D to reach
                // the plugin's second check
                sim.pause_clock_at(ts + 2 * D);
            }
            sim.settle();
            let (o, os) = (sim.outcome(hx), sim.outcome(hs));
            let rs = sc.tx(&sim, codes, &format!("mallory.near: deploy_certified(); gov.near stages {case} while the registry call is in flight"), &o);
            let rss = sc.tx(&sim, codes, "   the staging transaction", &os);
            let st = rc(&rss, VAULT, "up_stage_code");
            sc.check(&format!("{case}: the staging ran after deploy_certified and before the callback"),
                ok(st) && block(rc(&rs, VAULT, "deploy_certified")) < block(st) && block(st) < block(rc(&rs, VAULT, "on_certificates")));
            sc.check(&format!("{case}: the registry answered with the certificate of v2, and the plugin refuses in the callback: {panic_text}"),
                ok(rc(&rs, REGISTRY, "get_valid_kind")) && failed_with(rc(&rs, VAULT, "on_certificates"), panic_text));
            sc.check(&format!("{case}: no deploy batch, the code is still v1"), batch(&rs).is_none() && code_of(&sim, codes) == "v1");
        }
        // replaced after the callback
        let mut sim = sim0.clone();
        let hx = sim.call(MALLORY, VAULT, "deploy_certified").args_json(json!({})).gas(g300()).submit();
        sim.step(); // conversion
        sim.step(); // deploy_certified runs
        sim.step(); // the registry answers
        let hs = sim.call(GOV, VAULT, "up_stage_code").args(codes.bytes("v3")).gas(g300()).submit();
        sim.settle();
        let (o, os) = (sim.outcome(hx), sim.outcome(hs));
        let rs = sc.tx(&sim, codes, "mallory.near: deploy_certified(); gov.near stages v3 after the registry answered", &o);
        let rss = sc.tx(&sim, codes, "   the staging transaction", &os);
        sc.check("the staging of v3 ran after the callback", ok(rc(&rss, VAULT, "up_stage_code")) && block(rc(&rss, VAULT, "up_stage_code")) > block(rc(&rs, VAULT, "on_certificates")));
        sc.check("the batch installs v2, the code the registry was asked about; v3 is merely staged",
            ok(batch(&rs)) && code_of(&sim, codes) == "v2" && staged_hash(&sim) == json!(h3));
        sim.pause_clock_at(ts + 3 * D);
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "mallory.near: deploy_certified() for the uncertified v3, after its delay", &o);
        sc.check("v3 has no certificate: refused, the code stays v2", failed_with(rc(&rs, VAULT, "on_certificates"), "Gate: no valid") && code_of(&sim, codes) == "v2");
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("revoked_certificate", "A certificate revoked before the registry is asked does not count. A revocation that lands after the registry answered does not stop that deployment: the guarantee is about the moment of the registry call.");
        let mut sim0 = base.clone();
        let ts = stage_now(&mut sc, &mut sim0, codes, "v2");
        let idx = attest(&mut sim0, ATTESTOR, &h2, KIND).unwrap_or(u64::MAX);
        sim0.pause_clock_at(ts + D);
        let mut sim = sim0.clone();
        sc.check("other-attestor.near cannot revoke somebody else's certificate", !revoke(&mut sim, OTHER_ATTESTOR, idx));
        sc.check("attestor.near revokes its certificate", revoke(&mut sim, ATTESTOR, idx));
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "mallory.near: deploy_certified() after the revocation", &o);
        sc.check("refused: the registry's answer holds no valid certificate; the code is still v1",
            failed_with(rc(&rs, VAULT, "on_certificates"), "Gate: no valid") && batch(&rs).is_none() && code_of(&sim, codes) == "v1");
        let i2 = attest(&mut sim, ATTESTOR, &h2, KIND);
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "attestor.near attests again; mallory.near: deploy_certified()", &o);
        sc.check("a new certificate next to the revoked one counts: v2 is deployed", i2.is_some() && ok(batch(&rs)) && code_of(&sim, codes) == "v2");
        // the limit: revocation after the registry call
        let mut sim = sim0.clone();
        let hx = sim.call(MALLORY, VAULT, "deploy_certified").args_json(json!({})).gas(g300()).submit();
        sim.step(); // conversion
        sim.step(); // deploy_certified runs
        let hr = sim.call(ATTESTOR, REGISTRY, "revoke").args_json(json!({"index": idx, "reason": "test"})).submit();
        sim.settle();
        let (o, or) = (sim.outcome(hx), sim.outcome(hr));
        let rs = sc.tx(&sim, codes, "LIMIT — mallory.near: deploy_certified(); attestor.near revokes while the answer is on its way", &o);
        let rsr = sc.tx(&sim, codes, "   the revocation", &or);
        sc.check("LIMIT: the revocation ran after the registry call and not after the deploy batch",
            ok(rc(&rsr, REGISTRY, "revoke")) && block(rc(&rsr, REGISTRY, "revoke")) > block(rc(&rs, REGISTRY, "get_valid_kind")) && block(rc(&rsr, REGISTRY, "revoke")) <= block(batch(&rs)));
        sc.check("LIMIT: the deployment goes through; the certificate was valid when the registry was asked",
            ok(batch(&rs)) && code_of(&sim, codes) == "v2" && view(&sim, REGISTRY, "get_valid_kind", json!({"code_hash": h2, "kind": KIND})) == Some(json!([])));
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("callback_checks_every_field", "The callback's own test of the registry's answer, on answers the registry would never give (the simulator delivers the callback with a chosen promise result; no node does that): a revoked certificate, another hash, another kind, another attestor, an empty list, bytes that are no certificate list, a failed call — each refused. The registry holds no certificate at all in this scenario.");
        let mut sim0 = base.clone();
        let ts = stage_now(&mut sc, &mut sim0, codes, "v2");
        sim0.pause_clock_at(ts + D);
        let forged = |hash: &str, kind: &str, attestor: &str, revoked: bool| -> Value {
            json!({"code_hash": hash, "body": cert(kind), "attestor": attestor, "attested_at_ns": 1, "revoked": revoked, "revoke_reason": null})
        };
        for (what, result, text) in [
            ("a revoked certificate", PromiseResult::json(json!([forged(&h2, KIND, ATTESTOR, true)])), "Gate: no valid"),
            ("a certificate for another hash", PromiseResult::json(json!([forged(&h3, KIND, ATTESTOR, false)])), "Gate: no valid"),
            ("a certificate of another kind", PromiseResult::json(json!([forged(&h2, "exit", ATTESTOR, false)])), "Gate: no valid"),
            ("a certificate by another attestor", PromiseResult::json(json!([forged(&h2, KIND, OTHER_ATTESTOR, false)])), "Gate: no valid"),
            ("all four of these at once", PromiseResult::json(json!([forged(&h2, KIND, ATTESTOR, true), forged(&h3, KIND, ATTESTOR, false), forged(&h2, "exit", ATTESTOR, false), forged(&h2, KIND, MALLORY, false)])), "Gate: no valid"),
            ("an empty list", PromiseResult::json(json!([])), "Gate: no valid"),
            ("bytes that are no certificate list", PromiseResult::json(json!({"ok": true})), "Failed to deserialize"),
            ("a failed registry call", PromiseResult::Failed, "Gate: the registry call failed"),
        ] {
            let mut sim = sim0.clone();
            let o = sim.call(MALLORY, VAULT, "on_certificates").args_json(json!({"hash": h2})).promise_results([result]).gas(g300()).transact();
            sim.settle();
            let rs = receipts(&o);
            sc.check(&format!("answer = {what}: refused ({text}), no deploy batch, the code is still v1"),
                failed_with(rc(&rs, VAULT, "on_certificates"), text) && batch(&rs).is_none() && code_of(&sim, codes) == "v1");
        }
        let mut sim = sim0.clone();
        let o = sim.call(MALLORY, VAULT, "on_certificates").args_json(json!({"hash": h2}))
            .promise_results([PromiseResult::json(json!([forged(&h2, KIND, OTHER_ATTESTOR, false), forged(&h2, KIND, ATTESTOR, false)]))]).gas(g300()).transact();
        sim.settle();
        let rs = sc.tx(&sim, codes, "control: the callback delivered with a matching certificate in the answer", &o);
        sc.check("control: with a matching certificate in the answer the callback deploys — the gate relies on the answer being the registry's (hypothesis)", ok(batch(&rs)) && code_of(&sim, codes) == "v2");
        let mut sim = sim0.clone();
        let o = sim.call(MALLORY, VAULT, "on_certificates").args_json(json!({"hash": h3}))
            .promise_results([PromiseResult::json(json!([forged(&h3, KIND, ATTESTOR, false)]))]).gas(g300()).transact();
        sim.settle();
        let rs = receipts(&o);
        sc.check("an accepted answer for a hash that is not the staged one: the plugin refuses (wrong hash), the code is still v1",
            failed_with(rc(&rs, VAULT, "on_certificates"), "Upgradable: Cannot deploy due to wrong hash") && code_of(&sim, codes) == "v1");
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("no_way_around_the_gate", "With certified code staged and its delay passed: the callback cannot be called from outside; up_deploy_code is refused for every account; no account can obtain the deployer role, become an admin or a super-admin; nobody can change the staging duration; new cannot be called again.");
        let mut sim = base.clone();
        let ts = stage_now(&mut sc, &mut sim, codes, "v3");
        sim.pause_clock_at(ts + D);
        let (acl0, status0, gate0, code0) = (acl(&sim), status(&sim), view(&sim, VAULT, "gate", json!({})), code_hash(&sim));
        sc.check("the access-control state is the one the theorem assumes", acl0 == acl_expected());
        let outsiders = [MALLORY, GOV, ATTESTOR, OTHER_ATTESTOR, REG_OWNER, REGISTRY, ALICE];
        let mut all_private = true;
        for who in outsiders {
            let o = sim.call(who, VAULT, "on_certificates").args_json(json!({"hash": h3})).gas(g300()).transact();
            sim.settle();
            let rs = receipts(&o);
            all_private &= failed_with(rc(&rs, VAULT, "on_certificates"), "Method on_certificates is private") && batch(&rs).is_none();
        }
        sc.check("on_certificates(hash of the staged code) called directly by 7 accounts (the stager, both attestors, the registry and its owner, a depositor, a stranger): Method on_certificates is private", all_private);
        let mut all_refused = true;
        for who in outsiders {
            for args in [json!({"hash": h3}), json!({"hash": h3, "function_call_args": {"function_name": "version", "arguments": [], "amount": "0", "gas": "5000000000000"}})] {
                let o = sim.call(who, VAULT, "up_deploy_code").args_json(args).gas(g300()).transact();
                sim.settle();
                let rs = receipts(&o);
                all_refused &= failed_with(rc(&rs, VAULT, "up_deploy_code"), "Insufficient permissions for method up_deploy_code") && batch(&rs).is_none();
            }
        }
        sc.check("up_deploy_code(hash of the staged code), with and without an attached call, by the same 7 accounts: Insufficient permissions", all_refused);
        // access control: every state-changing acl method, by every outsider, aimed at getting the deployer role
        let mut acl_calls = 0;
        let mut acl_none = true;
        for who in outsiders {
            for (method, args) in [
                ("acl_grant_role", json!({"role": "CodeDeployer", "account_id": who})),
                ("acl_grant_role", json!({"role": "DurationManager", "account_id": who})),
                ("acl_add_admin", json!({"role": "CodeDeployer", "account_id": who})),
                ("acl_add_admin", json!({"role": "DurationManager", "account_id": who})),
                ("acl_add_super_admin", json!({"account_id": who})),
                ("acl_transfer_super_admin", json!({"account_id": who})),
                ("acl_revoke_super_admin", json!({"account_id": VAULT})),
                ("acl_revoke_role", json!({"role": "CodeDeployer", "account_id": VAULT})),
                ("acl_revoke_admin", json!({"role": "CodeDeployer", "account_id": VAULT})),
                ("acl_init_super_admin", json!({"account_id": who})),
                ("acl_renounce_admin", json!({"role": "CodeDeployer"})),
            ] {
                let o = sim.call(who, VAULT, method).args_json(args).transact();
                sim.settle();
                acl_calls += 1;
                // refused = the method returned null (no permission) or false, or panicked (private)
                let r = o.receipts.iter().find(|r| r.receiver_id.as_str() == VAULT && r.method_names.first().map(String::as_str) == Some(method));
                let refused = r.is_some_and(|r| !r.is_success() || matches!(ret_json(r), Value::Null | Value::Bool(false)));
                acl_none &= refused && acl(&sim) == acl0;
            }
        }
        sc.note("acl calls made", json!(acl_calls));
        sc.check("77 acl calls by the 7 accounts (grant role, add admin, add / transfer / revoke super-admin, revoke role / admin, init super-admin, renounce admin): each returns null or false or panics, and the permissions are unchanged after each", acl_none && acl_calls == 77);
        let mut dur_refused = true;
        for who in outsiders {
            for (method, args) in [
                ("up_init_staging_duration", json!({"staging_duration": 0})),
                ("up_stage_update_staging_duration", json!({"staging_duration": 0})),
                ("up_apply_update_staging_duration", json!({})),
            ] {
                let o = sim.call(who, VAULT, method).args_json(args).transact();
                sim.settle();
                dur_refused &= failed_with(rc(&receipts(&o), VAULT, method), "Insufficient permissions");
            }
        }
        sc.check("the three duration methods by the same 7 accounts: Insufficient permissions; the delay status is unchanged", dur_refused && status(&sim) == status0);
        let mut stage_refused = true;
        for who in [MALLORY, ATTESTOR, OTHER_ATTESTOR, REG_OWNER, REGISTRY, ALICE] {
            let o = stage(&mut sim, who, codes.bytes("v2"));
            stage_refused &= failed_with(rc(&receipts(&o), VAULT, "up_stage_code"), "Insufficient permissions");
        }
        sc.check("up_stage_code by the 6 accounts that are not the stager: Insufficient permissions; the staged hash is unchanged", stage_refused && staged_hash(&sim) == json!(h3));
        let mut init_refused = true;
        for who in [MALLORY, GOV, VAULT] {
            let o = sim.call(who, VAULT, "new").args_json(json!({"staging_duration": 1, "registry": MALLORY, "certificate_kind": KIND, "attestors": [MALLORY], "stagers": [MALLORY]})).gas(g300()).transact();
            sim.settle();
            init_refused &= !ok(rc(&receipts(&o), VAULT, "new"));
        }
        sc.check("new called again (by a stranger, by the stager, by the contract account): refused; the gate is unchanged", init_refused && view(&sim, VAULT, "gate", json!({})) == gate0 && gate0 == Some(gate_expected()));
        sc.check("after all of the above: same code hash, same permissions, same delay status", code_hash(&sim) == code0 && acl(&sim) == acl0 && status(&sim) == status0);
        // what the stager can do with its own role: give it up
        let o = sim.call(GOV, VAULT, "acl_renounce_role").args_json(json!({"role": "CodeStager"})).transact();
        sim.settle();
        let mut exp = acl_expected();
        exp["roles"]["CodeStager"]["grantees"] = json!([]);
        sc.check("the stager can renounce its own role, and that is all: afterwards nobody can stage", o.is_success() && acl(&sim) == exp);
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("init", "new is callable only by the contract account, only once, and refuses a zero duration, itself as the registry, an empty kind and an empty attestor list.");
        let bare = bare_world(codes);
        let mut sim = bare.clone();
        let o = sim.call(MALLORY, VAULT, "new").args_json(init_args(REGISTRY)).gas(g300()).transact();
        sim.settle();
        sc.check("a stranger calling new on the uninitialised contract: Method new is private", failed_with(rc(&receipts(&o), VAULT, "new"), "Method new is private"));
        for (what, args, text) in [
            ("staging_duration = 0", json!({"staging_duration": 0, "registry": REGISTRY, "certificate_kind": KIND, "attestors": [ATTESTOR], "stagers": [GOV]}), "the staging duration must be positive"),
            ("registry = the contract account", json!({"staging_duration": D, "registry": VAULT, "certificate_kind": KIND, "attestors": [ATTESTOR], "stagers": [GOV]}), "the registry must be another account"),
            ("empty kind", json!({"staging_duration": D, "registry": REGISTRY, "certificate_kind": "", "attestors": [ATTESTOR], "stagers": [GOV]}), "the certificate kind must not be empty"),
            ("no attestors", json!({"staging_duration": D, "registry": REGISTRY, "certificate_kind": KIND, "attestors": [], "stagers": [GOV]}), "at least one accepted attestor"),
        ] {
            let mut sim = bare.clone();
            let o = sim.call(VAULT, VAULT, "new").args_json(args).gas(g300()).transact();
            sim.settle();
            sc.check(&format!("new with {what}: refused"), failed_with(rc(&receipts(&o), VAULT, "new"), text));
        }
        let mut sim = bare.clone();
        let o = sim.call(VAULT, VAULT, "new").args_json(init_args(REGISTRY)).gas(g300()).transact();
        sim.settle();
        sc.tx(&sim, codes, "vault.near: new(D = 1 h, registry.near, upgrade-window, [attestor.near], [gov.near])", &o);
        sc.check("after new: the gate as given, the contract account the only super-admin and code deployer, gov the code stager, nobody a duration manager, no admins",
            o.is_success() && view(&sim, VAULT, "gate", json!({})) == Some(gate_expected()) && acl(&sim) == acl_expected());
        sc.check("after new: staging duration D, nothing staged, no duration update staged",
            status(&sim) == json!({"staging_duration": D, "staging_timestamp": null, "new_staging_duration": null, "new_staging_duration_timestamp": null}));
        let o = deploy_certified(&mut sim, MALLORY);
        sc.check("deploy_certified with nothing staged: Gate: no staged code", failed_with(rc(&receipts(&o), VAULT, "deploy_certified"), "Gate: no staged code"));
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("failed_steps", "A step that fails leaves nothing behind: too little gas, a registry that does not exist or has no code, a certified code that is not a contract. The same call with enough gas and a working registry deploys.");
        let mut sim0 = base.clone();
        let ts = stage_now(&mut sc, &mut sim0, codes, "v2");
        attest(&mut sim0, ATTESTOR, &h2, KIND);
        sim0.pause_clock_at(ts + D);
        let mut sim = sim0.clone();
        let (code0, staged0, status0) = (code_hash(&sim), staged_hash(&sim), status(&sim));
        let mut lowest_ok = 0u64;
        for tgas in [5u64, 20, 40, 60, 80, 100, 120, 150, 200, 300] {
            let mut s = sim.clone();
            let o = s.call(MALLORY, VAULT, "deploy_certified").args_json(json!({})).gas(Gas::from_teragas(tgas)).transact();
            s.settle();
            let rs = receipts(&o);
            let deployed = ok(batch(&rs)) && code_of(&s, codes) == "v2";
            sc.note(&format!("deploy_certified with {tgas} Tgas"), json!({"deployed": deployed, "burnt": total_gas(&o).to_string(),
                "receipts": rs.iter().map(|r| json!({"receiver": r["receiver"], "methods": r["methods"], "ok": r["ok"], "status": r["status"]})).collect::<Vec<_>>()}));
            if deployed {
                if lowest_ok == 0 { lowest_ok = tgas; }
            } else {
                sc.check(&format!("{tgas} Tgas is not enough: nothing is deployed and the vault is as before (code, staged code, delay status)"),
                    code_hash(&s) == code0 && staged_hash(&s) == staged0 && status(&s) == status0);
            }
        }
        sc.note("lowest tested gas with which the deployment went through (Tgas)", json!(lowest_ok));
        sc.check("with 300 Tgas the deployment goes through", lowest_ok > 0 && lowest_ok <= 300);
        // a failed attempt, then a good one on the same state
        let o = sim.call(MALLORY, VAULT, "deploy_certified").args_json(json!({})).gas(Gas::from_teragas(20)).transact();
        sim.settle();
        let o2 = deploy_certified(&mut sim, ALICE);
        sc.check("after a failed attempt the next deploy_certified deploys: the gate keeps no state", !o.is_success() && ok(batch(&receipts(&o2))) && code_of(&sim, codes) == "v2");
        // a callback that runs out of gas: 1 MB of staged code makes reading and hashing it dear
        {
            let mut sim = base.clone();
            let big = codes.bytes("big");
            let hb = codes.hash("big");
            let o = stage(&mut sim, GOV, big);
            let rs = sc.tx(&sim, codes, "gov.near: up_stage_code(v2 padded to 1 MB)", &o);
            let tsb: u64 = rs.first().and_then(|r| r["block_timestamp"].as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
            attest(&mut sim, ATTESTOR, &hb, KIND);
            sim.pause_clock_at(tsb + D);
            let (code0, staged0, status0) = (code_hash(&sim), staged_hash(&sim), status(&sim));
            let (mut first_step, mut in_callback, mut deployed_at) = (0, 0, 0u64);
            let mut unchanged = true;
            for tgas in (100u64..=300).step_by(10) {
                let mut s = sim.clone();
                let o = s.call(MALLORY, VAULT, "deploy_certified").args_json(json!({})).gas(Gas::from_teragas(tgas)).transact();
                s.settle();
                let rs = receipts(&o);
                let deployed = ok(batch(&rs)) && code_hash(&s) == hb;
                let cb = rc(&rs, VAULT, "on_certificates");
                let what = if deployed { "deployed" } else if cb.is_some() { "the callback failed" } else { "deploy_certified failed" };
                sc.note(&format!("1 MB staged, deploy_certified with {tgas} Tgas"), json!({"result": what, "burnt": total_gas(&o).to_string(),
                    "callback": cb.map(|r| r["status"].clone())}));
                if deployed {
                    if deployed_at == 0 { deployed_at = tgas; }
                } else {
                    unchanged &= code_hash(&s) == code0 && staged_hash(&s) == staged0 && status(&s) == status0 && batch(&rs).is_none();
                    if cb.is_some() { if failed_with(cb, "GasExceeded") || failed_with(cb, "OutOfGas") || failed_with(cb, "gas") { in_callback += 1; } } else { first_step += 1; }
                }
            }
            sc.note("1 MB staged: attempts that failed in deploy_certified / in the callback, lowest gas that deployed (Tgas)", json!([first_step, in_callback, deployed_at]));
            sc.check("1 MB of staged code: some gas amounts fail in the callback for lack of gas; every failed attempt leaves the vault as before and creates no deploy batch", in_callback > 0 && unchanged);
            sc.check("1 MB of staged code: with 300 Tgas the deployment goes through", deployed_at > 0 && deployed_at <= 300);
        }
        // registries that cannot answer
        for (what, registry, deploy_nothing) in [("an account that does not exist", "nobody.near", false), ("an account without code", "empty.near", true)] {
            let mut sim = bare_world(codes);
            if deploy_nothing { sim.create_account(registry, Balance::from_near(10)); }
            sim.call(VAULT, VAULT, "new").args_json(init_args(registry)).gas(g300()).transact().assert_success();
            let t = sim.timestamp_ns() + 10 * SEC;
            sim.pause_clock_at(t);
            stage(&mut sim, GOV, codes.bytes("v2")).assert_success();
            sim.pause_clock_at(t + D);
            let o = deploy_certified(&mut sim, MALLORY);
            let rs = sc.tx(&sim, codes, &format!("a vault whose registry is {what}: deploy_certified()"), &o);
            sc.check(&format!("registry = {what}: the callback sees a failed call and refuses; the code is still v1"),
                failed_with(rc(&rs, VAULT, "on_certificates"), "Gate: the registry call failed") && batch(&rs).is_none() && code_of(&sim, codes) == "v1");
        }
        // certified bytes that are not a contract: the plugin's batch rolls back
        let mut sim = base.clone();
        let ts = stage_now(&mut sc, &mut sim, codes, "junk");
        attest(&mut sim, ATTESTOR, &codes.hash("junk"), KIND);
        sim.pause_clock_at(ts + D);
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "certified bytes that are not wasm: deploy_certified()", &o);
        sc.check("the callback accepts, the deploy batch fails in up_verify_state and is rolled back: the code is still v1",
            ok(rc(&rs, VAULT, "on_certificates")) && batch(&rs).is_some_and(|b| b["ok"] == json!(false)) && code_of(&sim, codes) == "v1");
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("gate_survives_upgrade", "After a certified upgrade to v2 the new code enforces the same gate: uncertified v3 is refused, a direct up_deploy_code is refused, certified v3 is deployed after its own delay.");
        let mut sim = base.clone();
        let ts = stage_now(&mut sc, &mut sim, codes, "v2");
        attest(&mut sim, ATTESTOR, &h2, KIND);
        sim.pause_clock_at(ts + D);
        deploy_certified(&mut sim, MALLORY).assert_success();
        sc.check("v2 is running", code_of(&sim, codes) == "v2");
        let ts3 = stage_now(&mut sc, &mut sim, codes, "v3");
        sim.pause_clock_at(ts3 + D);
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "on v2 — mallory.near: deploy_certified() for the uncertified v3", &o);
        sc.check("on v2: uncertified v3 is refused, the code hash does not change", failed_with(rc(&rs, VAULT, "on_certificates"), "Gate: no valid") && code_of(&sim, codes) == "v2");
        let o = sim.call(GOV, VAULT, "up_deploy_code").args_json(json!({"hash": h3})).gas(g300()).transact();
        sim.settle();
        sc.check("on v2: up_deploy_code by the stager is refused", failed_with(rc(&receipts(&o), VAULT, "up_deploy_code"), "Insufficient permissions") && code_of(&sim, codes) == "v2");
        attest(&mut sim, ATTESTOR, &h3, KIND);
        let o = deploy_certified(&mut sim, MALLORY);
        let rs = sc.tx(&sim, codes, "on v2 — attestor.near attests v3; mallory.near: deploy_certified()", &o);
        sc.check("on v2: certified v3 is deployed", ok(batch(&rs)) && code_of(&sim, codes) == "v3" && view(&sim, VAULT, "version", json!({})) == Some(json!(3)));
        out.push(sc.done());
    }

    // ---------------------------------------------------------------------------------------
    {
        let mut sc = Scenario::new("control_contract_key", "LIMIT, not a guarantee: a transaction signed by the contract account itself passes the plugin's role check and deploys uncertified code. This is why the contract account must have no access keys.");
        let mut sim = base.clone();
        let ts = stage_now(&mut sc, &mut sim, codes, "v3");
        sim.pause_clock_at(ts + D);
        let o = sim.call(VAULT, VAULT, "up_deploy_code").args_json(json!({"hash": h3})).gas(g300()).transact();
        sim.settle();
        let rs = sc.tx(&sim, codes, "vault.near (possible only with an access key of the contract account): up_deploy_code(hash of the uncertified v3)", &o);
        sc.check("LIMIT: with the contract account as the signer the uncertified code is deployed", ok(batch(&rs)) && code_of(&sim, codes) == "v3");
        out.push(sc.done());
    }

    let ok = out.iter().all(|s| s["ok"] == json!(true));
    let checks: usize = out.iter().map(|s| s["checks"].as_array().map_or(0, Vec::len)).sum();
    json!({"ok": ok, "scenarios_total": out.len(), "checks_total": checks, "codes": codes.table(),
           "registry_wasm_hash": CryptoHash::hash_bytes(&codes.registry).to_string(), "scenarios": out})
}

// ---------------------------------------------------------------------------------------------
// Random traces with a monitor.
//
// Every trace: a vault with a random staging duration, then random operations by random accounts
// sharing blocks: staging (v1, v2, v3, a stub, bytes that are no contract, empty input),
// attestations (both attestors and a stranger; three kinds; five hashes), revocations,
// deploy_certified with different gas, direct calls of up_deploy_code and of the callback, the
// three duration methods, acl calls aimed at the deployer role, deposits and withdrawals, and
// jumps of the clock to one nanosecond before, exactly at and after the staging timestamp.
//
// The monitor reads only what the chain shows — the receipts in execution order and the vault's
// state after every block — and keeps its own record of the registry's certificates. It checks
//   * the statement of the theorem: the account's code hash changes only in a block where a deploy
//     batch succeeded; that batch was created by a successful callback; the registry call behind
//     that callback returned, for the hash that is now installed, a certificate that is not
//     revoked, of the accepted kind, by the accepted attestor; that hash was the last staged one
//     and was staged at least D earlier;
//   * the registry's answers against the monitor's own record of attestations and revocations;
//   * the rule of the model for every step: deploy_certified and the callback succeed or fail,
//     with the panic the model predicts, exactly when the model says (a failure for lack of gas
//     is allowed anywhere);
//   * the hypotheses that are supposed to be invariant: permissions, gate, staging duration.

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

#[derive(Default)]
struct Stats {
    traces: u64,
    blocks: u64,
    receipts: u64,
    counts: BTreeMap<String, u64>,
    violations: Vec<String>,
}

impl Stats {
    fn count(&mut self, key: &str) {
        *self.counts.entry(key.to_string()).or_insert(0) += 1;
    }
    fn violation(&mut self, trace: u64, what: String) {
        if self.violations.len() < 50 {
            self.violations.push(format!("trace {trace}: {what}"));
        }
        self.count("VIOLATIONS");
    }
}

fn arg_json(r: &ReceiptOutcome) -> Value {
    r.args.first().and_then(|a| serde_json::from_slice::<Value>(a).ok()).unwrap_or(Value::Null)
}

fn is_gas_failure(text: &str) -> bool {
    text.contains("GasExceeded") || text.contains("GasLimitExceeded") || text.contains("OutOfGas") || text.contains("Exceeded the prepaid gas") || text.contains("Exceeded the maximum amount of gas")
}

fn sat_add(a: u64, b: u64) -> u64 {
    a.saturating_add(b)
}

fn random_op(sim: &mut Sim, rng: &mut Rng, codes: &Codes, n_certs: u64) -> &'static str {
    let labels = ["v1", "v2", "v3", "stub", "junk"];
    let anyone = [GOV, ATTESTOR, OTHER_ATTESTOR, MALLORY, ALICE, REG_OWNER];
    match rng.below(100) {
        0..=17 => {
            let who = if rng.chance(80) { GOV } else { *rng.pick(&anyone) };
            let code = match rng.below(100) {
                0..=39 => codes.bytes("v2"),
                40..=64 => codes.bytes("v3"),
                65..=74 => codes.bytes("v1"),
                75..=82 => codes.bytes("stub"),
                83..=89 => codes.bytes("junk"),
                _ => vec![],
            };
            sim.call(who, VAULT, "up_stage_code").args(code).gas(g300()).submit();
            "stage"
        }
        18..=35 => {
            let who = match rng.below(100) { 0..=59 => ATTESTOR, 60..=84 => OTHER_ATTESTOR, _ => MALLORY };
            let label: &str = *rng.pick(&labels[..]);
            let hash = codes.hash(label);
            let kind = match rng.below(100) { 0..=74 => KIND, 75..=87 => "exit", _ => "token-standard" };
            sim.call(who, REGISTRY, "attest").args_json(json!({"code_hash": hash, "certificate": cert(kind)}))
                .deposit(Balance::from_near(1)).gas(Gas::from_teragas(100)).submit();
            "attest"
        }
        36..=43 => {
            let who = match rng.below(100) { 0..=64 => ATTESTOR, 65..=89 => OTHER_ATTESTOR, _ => MALLORY };
            let index = if n_certs == 0 || rng.chance(10) { rng.below(5) } else { rng.below(n_certs) };
            sim.call(who, REGISTRY, "revoke").args_json(json!({"index": index, "reason": "test"})).submit();
            "revoke"
        }
        44..=71 => {
            let who = *rng.pick(&anyone);
            let tgas = *rng.pick(&[300u64, 300, 300, 200, 150, 100, 90, 60, 30]);
            sim.call(who, VAULT, "deploy_certified").args_json(json!({})).gas(Gas::from_teragas(tgas)).submit();
            "deploy_certified"
        }
        72..=77 => {
            let who = *rng.pick(&anyone);
            let hash = match view(sim, VAULT, "up_staged_code_hash", json!({})) {
                Some(Value::String(h)) if rng.chance(80) => h,
                _ => { let label: &str = *rng.pick(&labels[..]); codes.hash(label) }
            };
            let args = if rng.chance(70) { json!({"hash": hash}) } else {
                json!({"hash": hash, "function_call_args": {"function_name": "version", "arguments": [], "amount": "0", "gas": "5000000000000"}})
            };
            sim.call(who, VAULT, "up_deploy_code").args_json(args).gas(g300()).submit();
            "direct up_deploy_code"
        }
        78..=81 => {
            let who = *rng.pick(&anyone);
            let hash = match view(sim, VAULT, "up_staged_code_hash", json!({})) {
                Some(Value::String(h)) => h,
                _ => codes.hash("v2"),
            };
            sim.call(who, VAULT, "on_certificates").args_json(json!({"hash": hash})).gas(g300()).submit();
            "direct on_certificates"
        }
        82..=86 => {
            let who = *rng.pick(&anyone);
            let (method, args) = match rng.below(3) {
                0 => ("up_init_staging_duration", json!({"staging_duration": rng.below(3)})),
                1 => ("up_stage_update_staging_duration", json!({"staging_duration": rng.below(3)})),
                _ => ("up_apply_update_staging_duration", json!({})),
            };
            sim.call(who, VAULT, method).args_json(args).submit();
            "duration method"
        }
        87..=93 => {
            let who = *rng.pick(&anyone);
            let role = *rng.pick(&["CodeDeployer", "DurationManager", "CodeStager"]);
            let (method, args) = match rng.below(9) {
                0 | 1 => ("acl_grant_role", json!({"role": role, "account_id": who})),
                2 => ("acl_add_admin", json!({"role": role, "account_id": who})),
                3 => ("acl_add_super_admin", json!({"account_id": who})),
                4 => ("acl_transfer_super_admin", json!({"account_id": who})),
                5 => ("acl_revoke_role", json!({"role": role, "account_id": VAULT})),
                6 => ("acl_revoke_super_admin", json!({"account_id": VAULT})),
                7 => ("acl_init_super_admin", json!({"account_id": who})),
                _ => if who == GOV && !rng.chance(15) { ("acl_renounce_admin", json!({"role": role})) } else { ("acl_renounce_role", json!({"role": role})) },
            };
            sim.call(who, VAULT, method).args_json(args).submit();
            "acl method"
        }
        94..=96 => {
            sim.call(REG_OWNER, REGISTRY, if rng.chance(70) { "add_attestor" } else { "remove_attestor" })
                .args_json(json!({"account_id": rng.pick(&[MALLORY, OTHER_ATTESTOR, ATTESTOR])})).submit();
            "registry attestor list"
        }
        _ => {
            if rng.chance(50) {
                sim.call(ALICE, VAULT, "deposit").args_json(json!({})).deposit(Balance::from_near(1)).submit();
            } else {
                sim.call(ALICE, VAULT, "withdraw").args_json(json!({"amount": Balance::from_near(1).as_yoctonear().to_string()})).submit();
            }
            "vault deposit / withdraw"
        }
    }
}

fn run_trace(bare: &Sim, codes: &Codes, seed: u64, id: u64, st: &mut Stats) {
    let mut sim = bare.clone();
    let mut rng = Rng(seed ^ (id.wrapping_mul(0x9E3779B97F4A7C15)) | 1);
    let dur = *rng.pick(&[2 * SEC, 5 * SEC, 20 * SEC, 3600 * SEC]);
    let mut args = init_args(REGISTRY);
    args["staging_duration"] = json!(dur);
    sim.call(VAULT, VAULT, "new").args_json(args).gas(g300()).transact().assert_success();
    sim.call(ALICE, VAULT, "deposit").args_json(json!({})).deposit(Balance::from_near(5)).transact().assert_success();
    sim.settle();
    let h0 = sim.height();
    let mut code_at: Vec<(u64, String)> = vec![(h0, code_hash(&sim))];
    let acl0 = acl_expected();
    let mut acl_gov_gone = acl_expected();
    acl_gov_gone["roles"]["CodeStager"]["grantees"] = json!([]);
    let observe = |sim: &Sim, st: &mut Stats, code_at: &mut Vec<(u64, String)>| {
        code_at.push((sim.height(), code_hash(sim)));
        st.blocks += 1;
        // the code that runs may be a stub without views: then there is nothing to read
        if let Some(g) = view(sim, VAULT, "gate", json!({})) {
            let a = acl(sim);
            if g != gate_expected() { st.violation(id, format!("the gate changed: {g}")); }
            if a != acl0 && a != acl_gov_gone { st.violation(id, format!("the permissions changed: {a}")); }
            let s = status(sim);
            if s["staging_duration"] != json!(dur) || !s["new_staging_duration"].is_null() || !s["new_staging_duration_timestamp"].is_null() {
                st.violation(id, format!("the delay status changed: {s}"));
            }
        }
    };
    let n_ops = 25 + rng.below(50);
    for _ in 0..n_ops {
        if rng.chance(40) {
            let now = sim.timestamp_ns();
            let target = match (status(&sim)["staging_timestamp"].as_u64(), rng.below(100)) {
                (Some(ts), 0..=69) => match rng.below(5) { 0 => ts - 1, 1 | 2 => ts, 3 => ts + 1, _ => ts + rng.below(3 * SEC) },
                _ => now + rng.below(2 * dur.min(40 * SEC) + SEC),
            };
            if target >= now + 3 * SEC {
                sim.set_timestamp_ns(target);
                st.count("clock jumps");
            }
        }
        let n_certs = view(&sim, REGISTRY, "count", json!({})).and_then(|v| v.as_u64()).unwrap_or(0);
        let op = random_op(&mut sim, &mut rng, codes, n_certs);
        st.count(&format!("submitted: {op}"));
        for _ in 0..*rng.pick(&[0u64, 0, 1, 1, 1, 2, 3]) {
            sim.step();
            observe(&sim, st, &mut code_at);
        }
    }
    let mut guard = 0;
    while !sim.is_idle() && guard < 200 {
        sim.step();
        observe(&sim, st, &mut code_at);
        guard += 1;
    }
    if !sim.is_idle() { st.violation(id, "the trace did not settle".into()); }

    // ---- the monitor: receipts in execution order
    let all = sim.receipts_in(h0 + 1..);
    let by_id: std::collections::HashMap<CryptoHash, &ReceiptOutcome> = all.iter().map(|r| (r.receipt_id, r)).collect();
    // the monitor's own record of the registry: (hash, kind, attestor, revoked)
    let mut certs: Vec<(String, String, String, bool)> = vec![];
    let mut reg_attestors: Vec<String> = vec![REG_OWNER.into(), ATTESTOR.into(), OTHER_ATTESTOR.into()];
    // the last successful staging: (hash, block timestamp)
    let mut staged: Option<(String, u64)> = None;
    let mut gov_can_stage = true;
    // registry call receipt -> (hash asked, Some(accepted) once it ran; None = it failed)
    let mut answers: std::collections::HashMap<CryptoHash, (String, Option<bool>)> = Default::default();
    // callback receipt -> the registry call behind it
    let mut callback_of: std::collections::HashMap<CryptoHash, CryptoHash> = Default::default();
    // deploy batch receipt -> the hash its callback was called with
    let mut batch_hash: std::collections::HashMap<CryptoHash, String> = Default::default();
    // block height -> hashes installed by successful batches in that block, in order
    let mut installed: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    // Blocks in which the account runs, at the start or at the end, a code that is not a build of
    // the vault (the certified stub, once installed, has no methods at all): there the model of
    // the vault says nothing about a call, and the call fails with MethodNotFound. The check of
    // the code hash, block by block, goes on.
    let vault_builds = [codes.hash("v1"), codes.hash("v2"), codes.hash("v3")];
    let foreign_code: std::collections::HashSet<u64> = code_at.windows(2)
        .filter(|w| !vault_builds.contains(&w[0].1) || !vault_builds.contains(&w[1].1)).map(|w| w[1].0).collect();
    for r in &all {
        st.receipts += 1;
        let (recv, pred, now) = (r.receiver_id.as_str(), r.predecessor_id.as_str(), r.block_timestamp_ns);
        let method = r.method_names.first().map(String::as_str).unwrap_or("");
        let fail = status_text(r);
        if recv == REGISTRY {
            match method {
                "attest" if r.is_success() => {
                    let a = arg_json(r);
                    if !reg_attestors.iter().any(|x| x == pred) { st.violation(id, format!("the registry accepted an attestation by {pred}")); }
                    certs.push((a["code_hash"].as_str().unwrap_or("").into(), a["certificate"]["kind"].as_str().unwrap_or("").into(), pred.into(), false));
                    st.count("registry: attestations stored");
                }
                "revoke" if r.is_success() => {
                    let i = arg_json(r)["index"].as_u64().unwrap_or(u64::MAX) as usize;
                    match certs.get_mut(i) {
                        Some(c) if c.2 == pred => { c.3 = true; st.count("registry: revocations"); }
                        _ => st.violation(id, format!("the registry let {pred} revoke certificate {i}")),
                    }
                }
                "add_attestor" if r.is_success() => {
                    let a = arg_json(r)["account_id"].as_str().unwrap_or("").to_string();
                    if !reg_attestors.contains(&a) { reg_attestors.push(a); }
                }
                "remove_attestor" if r.is_success() => {
                    let a = arg_json(r)["account_id"].as_str().unwrap_or("").to_string();
                    reg_attestors.retain(|x| *x != a);
                }
                "get_valid_kind" if pred == VAULT => {
                    let a = arg_json(r);
                    let (h, k) = (a["code_hash"].as_str().unwrap_or("").to_string(), a["kind"].as_str().unwrap_or("").to_string());
                    if !r.is_success() {
                        answers.insert(r.receipt_id, (h, None));
                        st.count("registry call failed");
                        continue;
                    }
                    let got = ret_json(r);
                    let got_list: Vec<(String, String, String, bool)> = got.as_array().into_iter().flatten().map(|c| {
                        (c["code_hash"].as_str().unwrap_or("").to_string(), c["body"]["kind"].as_str().unwrap_or("").to_string(),
                         c["attestor"].as_str().unwrap_or("").to_string(), c["revoked"].as_bool().unwrap_or(true))
                    }).collect();
                    let want: Vec<(String, String, String, bool)> = certs.iter().filter(|c| c.0 == h && c.1 == k && !c.3).cloned().collect();
                    if got_list != want { st.violation(id, format!("the registry's answer for {h} differs from the monitor's record: {got_list:?} vs {want:?}")); }
                    let accepted = want.iter().any(|c| c.2 == ATTESTOR && c.1 == KIND);
                    if k != KIND { st.violation(id, format!("the vault asked for kind {k}")); }
                    answers.insert(r.receipt_id, (h, Some(accepted)));
                    st.count(if accepted { "registry answered: accepted certificate present" } else { "registry answered: no accepted certificate" });
                }
                _ => {}
            }
            continue;
        }
        if recv != VAULT { continue; }
        if r.actions.first().map(String::as_str) == Some("DeployContract") {
            match batch_hash.get(&r.receipt_id) {
                None => st.violation(id, format!("a deploy batch that no callback created (predecessor {pred})")),
                Some(h) => {
                    if r.is_success() {
                        installed.entry(r.block_height).or_default().push(h.clone());
                        st.count("deploy batches succeeded");
                    } else {
                        st.count("deploy batches rolled back");
                    }
                }
            }
            continue;
        }
        if fail.contains("MethodNotFound") && foreign_code.contains(&r.block_height) {
            st.count("calls on an installed code that is not the vault (the certified stub): MethodNotFound");
            continue;
        }
        let staged_ok = |staged: &Option<(String, u64)>| staged.as_ref().is_some_and(|(_, ts)| sat_add(*ts, dur) <= now);
        match method {
            "up_stage_code" => {
                let should = pred == GOV && gov_can_stage;
                if r.is_success() != should && !(should && is_gas_failure(&fail)) {
                    st.violation(id, format!("up_stage_code by {pred}: {fail}"));
                }
                if r.is_success() {
                    let code = r.args.first().cloned().unwrap_or_default();
                    staged = if code.is_empty() { None } else { Some((CryptoHash::hash_bytes(&code).to_string(), now)) };
                    st.count("stagings");
                }
            }
            "acl_renounce_role" if r.is_success() && pred == GOV && arg_json(r)["role"] == "CodeStager" && ret_json(r) == json!(true) => {
                gov_can_stage = false;
                st.count("the stager renounced its role");
            }
            "up_deploy_code" => {
                st.count(if r.is_success() { "direct up_deploy_code ACCEPTED" } else { "direct up_deploy_code refused" });
                if r.is_success() || !fail.contains("Insufficient permissions") { st.violation(id, format!("direct up_deploy_code by {pred}: {fail}")); }
            }
            "up_init_staging_duration" | "up_stage_update_staging_duration" | "up_apply_update_staging_duration" => {
                st.count("duration methods refused");
                if r.is_success() || !fail.contains("Insufficient permissions") { st.violation(id, format!("{method} by {pred}: {fail}")); }
            }
            "deploy_certified" => {
                if r.is_success() {
                    st.count("deploy_certified: registry asked");
                    let kids: Vec<&&ReceiptOutcome> = r.receipt_ids.iter().filter_map(|c| by_id.get(c)).collect();
                    let q = kids.iter().find(|c| c.receiver_id.as_str() == REGISTRY && c.method_names.first().map(String::as_str) == Some("get_valid_kind"));
                    let cb = kids.iter().find(|c| c.receiver_id.as_str() == VAULT && c.method_names.first().map(String::as_str) == Some("on_certificates"));
                    match (q, cb) {
                        (Some(q), Some(cb)) => {
                            callback_of.insert(cb.receipt_id, q.receipt_id);
                            let asked = arg_json(q)["code_hash"].as_str().unwrap_or("").to_string();
                            let told = arg_json(cb)["hash"].as_str().unwrap_or("").to_string();
                            if !staged_ok(&staged) || staged.as_ref().map(|s| &s.0) != Some(&asked) || asked != told {
                                st.violation(id, format!("deploy_certified went ahead: staged {staged:?}, asked {asked}, callback {told}, now {now}"));
                            }
                        }
                        _ => st.violation(id, "deploy_certified succeeded without a registry call and a callback".into()),
                    }
                } else if fail.contains("Gate: no staged code") {
                    st.count("deploy_certified refused: nothing staged");
                    if staged.is_some() { st.violation(id, "deploy_certified said nothing was staged".into()); }
                } else if fail.contains("Gate: deploy too early") {
                    st.count("deploy_certified refused: too early");
                    if staged.is_none() || staged_ok(&staged) { st.violation(id, format!("deploy_certified said too early: staged {staged:?}, now {now}")); }
                } else if is_gas_failure(&fail) {
                    st.count("deploy_certified failed: gas");
                } else {
                    st.violation(id, format!("deploy_certified: {fail}"));
                }
            }
            "on_certificates" if pred != VAULT => {
                st.count("direct on_certificates refused");
                if r.is_success() || !fail.contains("is private") { st.violation(id, format!("direct on_certificates by {pred}: {fail}")); }
            }
            "on_certificates" => {
                let told = arg_json(r)["hash"].as_str().unwrap_or("").to_string();
                let answer = callback_of.get(&r.receipt_id).and_then(|q| answers.get(q)).cloned();
                let Some((asked, result)) = answer else {
                    st.violation(id, "a callback without an executed registry call".into());
                    continue;
                };
                let same_hash = staged.as_ref().is_some_and(|s| s.0 == told);
                // what the model says this callback does
                let model = if asked != told { "?" }
                    else if result.is_none() { "Gate: the registry call failed" }
                    else if result == Some(false) { "Gate: no valid" }
                    else if staged.is_none() { "Upgradable: staging timestamp isn't set" }
                    else if !staged_ok(&staged) { "Upgradable: Deploy code too early" }
                    else if !same_hash { "Upgradable: Cannot deploy due to wrong hash" }
                    else { "deploy" };
                if r.is_success() {
                    st.count("callback: deployment started");
                    if model != "deploy" { st.violation(id, format!("the callback deployed {told} although the model says: {model}")); }
                    // the statement of the theorem, read off the chain
                    if result != Some(true) { st.violation(id, format!("deployment of {told} without an accepted certificate in the registry's answer")); }
                    if !same_hash || !staged_ok(&staged) { st.violation(id, format!("deployment of {told}: staged {staged:?}, D {dur}, now {now}")); }
                    let kids: Vec<&&ReceiptOutcome> = r.receipt_ids.iter().filter_map(|c| by_id.get(c)).collect();
                    match kids.iter().find(|c| c.actions.first().map(String::as_str) == Some("DeployContract")) {
                        Some(b) => {
                            if b.actions != vec!["DeployContract".to_string(), "FunctionCall".to_string()] || b.method_names != vec!["up_verify_state".to_string()] || b.receiver_id.as_str() != VAULT {
                                st.violation(id, format!("unexpected deploy batch: {:?} {:?}", b.actions, b.method_names));
                            }
                            batch_hash.insert(b.receipt_id, told);
                        }
                        None => st.violation(id, "a successful callback without a deploy batch".into()),
                    }
                } else if is_gas_failure(&fail) {
                    st.count("callback failed: gas");
                } else {
                    let key = ["Gate: the registry call failed", "Gate: no valid", "Upgradable: staging timestamp isn't set", "Upgradable: Deploy code too early", "Upgradable: Cannot deploy due to wrong hash"]
                        .into_iter().find(|k| fail.contains(k)).unwrap_or("?");
                    st.count(&format!("callback refused: {key}"));
                    if key != model { st.violation(id, format!("the callback failed with [{fail}] although the model says: {model}")); }
                }
            }
            _ => {}
        }
    }
    // ---- the code on the account, block by block
    for w in code_at.windows(2) {
        let ((_, before), (h, after)) = (&w[0], &w[1]);
        let batches = installed.get(h).cloned().unwrap_or_default();
        if before != after {
            st.count("code hash changes");
            if batches.last() != Some(after) { st.violation(id, format!("block {h}: the code hash became {after} without a certified batch for it ({batches:?})")); }
        } else if batches.last().is_some_and(|b| b != after) {
            st.violation(id, format!("block {h}: a batch for {batches:?} succeeded but the code hash is {after}"));
        }
        if !batches.is_empty() && before == after { st.count("re-deployments of the running code"); }
    }
    st.traces += 1;
}

fn traces(codes: &Codes, seed: u64, start: u64, count: u64) -> Value {
    let bare = bare_world(codes);
    let mut st = Stats::default();
    for id in start..start + count {
        run_trace(&bare, codes, seed, id, &mut st);
    }
    json!({"seed": seed, "start": start, "traces": st.traces, "blocks": st.blocks, "receipts": st.receipts,
           "violations": st.counts.get("VIOLATIONS").copied().unwrap_or(0), "violation_samples": st.violations, "counts": st.counts})
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: gu-test scenarios|info <v1.wasm> <v2.wasm> <v3.wasm> <registry.wasm> | traces <v1.wasm> <v2.wasm> <v3.wasm> <registry.wasm> <seed> <start> <count>";
    if args.len() < 6 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let read = |p: &str| std::fs::read(p).unwrap_or_else(|e| panic!("{p}: {e}"));
    let codes = Codes::new(read(&args[2]), read(&args[3]), read(&args[4]), read(&args[5]));
    match args[1].as_str() {
        "info" => {
            println!("{}", serde_json::to_string_pretty(&json!({"codes": codes.table(), "registry": CryptoHash::hash_bytes(&codes.registry).to_string()})).unwrap());
        }
        "scenarios" => {
            let w = scenarios(&codes);
            println!("{}", serde_json::to_string_pretty(&w).unwrap());
            if w["ok"] != json!(true) {
                std::process::exit(1);
            }
        }
        "traces" if args.len() >= 9 => {
            let (seed, start, count): (u64, u64, u64) = (args[6].parse().unwrap(), args[7].parse().unwrap(), args[8].parse().unwrap());
            let w = traces(&codes, seed, start, count);
            println!("{}", serde_json::to_string(&w).unwrap());
            if w["violations"] != json!(0) {
                std::process::exit(1);
            }
        }
        _ => {
            eprintln!("{usage}");
            std::process::exit(2);
        }
    }
}
