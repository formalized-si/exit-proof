//! Exit Proof registry.
//!
//! Stores exit certificates keyed by the base58 code hash of deployed NEAR contract code. A certificate says which
//! machine-checked theorems hold for that exact code, under which assumptions, how the model was tied to the bytes,
//! and how anyone can re-check it (artifact hash + command). Wallets and agents read it before a deposit.
//!
//! Certificates have a `kind`; only kind "exit" states that depositors can always withdraw.
//!
//! Trust model: the registry does not verify proofs on chain. It records who attested what (`attestor` is the
//! predecessor of `attest`), and pins the artifact by sha256 so any reader can re-run the check on the same files.
//! Attestors are added by the owner. Certificates are append-only; an attestor can mark its own certificate revoked
//! but cannot edit or delete it, so the history of claims stays public.

use near_sdk::store::{IterableSet, LookupMap, Vector};
use near_sdk::{env, near, require, AccountId, NearToken, PanicOnDefault, Promise};

const MAX_TEXT: usize = 2048;
const MAX_LIST: usize = 32;
const KINDS: [&str; 3] = ["exit", "token-standard", "upgrade-window"];

#[near(serializers = [borsh, json])]
#[derive(Clone, Debug, PartialEq)]
pub struct Conformance {
    /// Random traces executed on the nearcore runtime against the model, all steps compared.
    pub traces: u64,
    /// Contract calls in those traces.
    pub calls: u64,
    /// Traces with any difference between model and deployed bytes.
    pub mismatches: u64,
    /// Runtime used, e.g. "nearcore 2.14.0 via near-contract-sim".
    pub runtime: String,
}

#[near(serializers = [borsh, json])]
#[derive(Clone, Debug, PartialEq)]
pub struct CertificateInput {
    /// What the certificate establishes: "exit" (a depositor can always withdraw), "token-standard" (the token
    /// behaves as the proved NEP-141 library) or "upgrade-window" (code changes only after a visible delay).
    /// Agents must filter on this: only "exit" is an exit guarantee.
    pub kind: String,
    /// Contract family, e.g. "core staking pool v0.4.0".
    pub family: String,
    /// The guarantee in plain words.
    pub statement: String,
    /// Lean theorem names that state it.
    pub theorems: Vec<String>,
    /// Axioms reported by `#print axioms`.
    pub axioms: Vec<String>,
    /// Assumptions the theorem depends on, in plain words.
    pub assumptions: Vec<String>,
    /// How the model is tied to these bytes (source commit, hash of the committed artifact, ...).
    pub binding: String,
    pub conformance: Conformance,
    /// sha256 (hex) of the proof bundle: Lean sources, harness, evidence.
    pub artifact_sha256: String,
    /// Where the bundle lives (repository + commit or URL).
    pub artifact_location: String,
    /// One command that re-runs the check on the bundle.
    pub check_command: String,
}

#[near(serializers = [borsh, json])]
#[derive(Clone, Debug, PartialEq)]
pub struct Certificate {
    pub code_hash: String,
    pub body: CertificateInput,
    pub attestor: AccountId,
    pub attested_at_ns: u64,
    pub revoked: bool,
    pub revoke_reason: Option<String>,
}

#[near(contract_state)]
#[derive(PanicOnDefault)]
pub struct Registry {
    owner: AccountId,
    attestors: IterableSet<AccountId>,
    certs: Vector<Certificate>,
    by_code: LookupMap<String, Vec<u32>>,
}

fn check_text(name: &str, s: &str) {
    require!(!s.is_empty() && s.len() <= MAX_TEXT, format!("{name}: empty or longer than {MAX_TEXT} bytes"));
}

fn check_list(name: &str, v: &[String]) {
    require!(v.len() <= MAX_LIST, format!("{name}: more than {MAX_LIST} entries"));
    for s in v {
        check_text(name, s);
    }
}

fn is_base58_hash(s: &str) -> bool {
    const A: &str = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    (32..=44).contains(&s.len()) && s.chars().all(|c| A.contains(c))
}

#[near]
impl Registry {
    #[init]
    pub fn new(owner: AccountId) -> Self {
        let mut attestors = IterableSet::new(b"a");
        attestors.insert(owner.clone());
        Self { owner, attestors, certs: Vector::new(b"c"), by_code: LookupMap::new(b"h") }
    }

    pub fn add_attestor(&mut self, account_id: AccountId) {
        require!(env::predecessor_account_id() == self.owner, "only the owner adds attestors");
        self.attestors.insert(account_id);
    }

    pub fn remove_attestor(&mut self, account_id: AccountId) {
        require!(env::predecessor_account_id() == self.owner, "only the owner removes attestors");
        self.attestors.remove(&account_id);
    }

    /// Append a certificate for `code_hash`. The caller pays for the storage it adds; any excess deposit is refunded.
    #[payable]
    pub fn attest(&mut self, code_hash: String, certificate: CertificateInput) -> u32 {
        let attestor = env::predecessor_account_id();
        require!(self.attestors.contains(&attestor), "caller is not an attestor");
        require!(is_base58_hash(&code_hash), "code_hash must be a base58 sha256");
        let c = &certificate;
        require!(KINDS.contains(&c.kind.as_str()), "kind must be one of: exit, token-standard, upgrade-window");
        for (n, s) in [("family", &c.family), ("statement", &c.statement), ("binding", &c.binding),
                       ("artifact_location", &c.artifact_location), ("check_command", &c.check_command),
                       ("conformance.runtime", &c.conformance.runtime)] {
            check_text(n, s);
        }
        check_list("theorems", &c.theorems);
        check_list("axioms", &c.axioms);
        check_list("assumptions", &c.assumptions);
        require!(c.artifact_sha256.len() == 64 && c.artifact_sha256.chars().all(|x| x.is_ascii_hexdigit()),
                 "artifact_sha256 must be 64 hex characters");
        require!(!c.theorems.is_empty(), "at least one theorem");

        let before = env::storage_usage();
        let idx = self.certs.len();
        self.certs.push(Certificate {
            code_hash: code_hash.clone(),
            body: certificate,
            attestor,
            attested_at_ns: env::block_timestamp(),
            revoked: false,
            revoke_reason: None,
        });
        let mut ids = self.by_code.get(&code_hash).cloned().unwrap_or_default();
        ids.push(idx);
        self.by_code.insert(code_hash, ids);
        self.certs.flush();
        self.by_code.flush();
        let used = env::storage_usage().saturating_sub(before);
        let cost = env::storage_byte_cost().saturating_mul(used as u128);
        let paid = env::attached_deposit();
        require!(paid >= cost, format!("attach at least {} yoctoNEAR for storage", cost.as_yoctonear()));
        let refund = paid.saturating_sub(cost);
        if refund > NearToken::from_yoctonear(0) {
            Promise::new(env::predecessor_account_id()).transfer(refund);
        }
        idx
    }

    /// Mark one of your own certificates revoked. The record stays readable.
    pub fn revoke(&mut self, index: u32, reason: String) {
        check_text("reason", &reason);
        let caller = env::predecessor_account_id();
        let c = self.certs.get_mut(index).unwrap_or_else(|| env::panic_str("no such certificate"));
        require!(c.attestor == caller, "only the attestor can revoke its certificate");
        c.revoked = true;
        c.revoke_reason = Some(reason);
    }

    /// All certificates for a code hash, revoked ones included (check `revoked`).
    pub fn get(&self, code_hash: String) -> Vec<Certificate> {
        self.by_code
            .get(&code_hash)
            .map(|ids| ids.iter().filter_map(|i| self.certs.get(*i).cloned()).collect())
            .unwrap_or_default()
    }

    /// Certificates that are not revoked, for a code hash.
    pub fn get_valid(&self, code_hash: String) -> Vec<Certificate> {
        self.get(code_hash).into_iter().filter(|c| !c.revoked).collect()
    }

    /// Not revoked certificates of one kind for a code hash, e.g. kind = "exit".
    pub fn get_valid_kind(&self, code_hash: String, kind: String) -> Vec<Certificate> {
        self.get_valid(code_hash).into_iter().filter(|c| c.body.kind == kind).collect()
    }

    pub fn list(&self, from_index: u32, limit: u32) -> Vec<Certificate> {
        let end = (from_index.saturating_add(limit.min(50))).min(self.certs.len());
        (from_index..end).filter_map(|i| self.certs.get(i).cloned()).collect()
    }

    pub fn count(&self) -> u32 {
        self.certs.len()
    }

    pub fn attestors(&self) -> Vec<AccountId> {
        self.attestors.iter().cloned().collect()
    }

    pub fn owner(&self) -> AccountId {
        self.owner.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use near_sdk::test_utils::{accounts, VMContextBuilder};
    use near_sdk::testing_env;

    const H: &str = "J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY";

    fn ctx(pred: usize, deposit: u128) {
        let mut b = VMContextBuilder::new();
        b.predecessor_account_id(accounts(pred)).attached_deposit(NearToken::from_yoctonear(deposit));
        testing_env!(b.build());
    }

    fn cert() -> CertificateInput {
        CertificateInput {
            kind: "exit".into(),
            family: "core staking pool v0.4.0".into(),
            statement: "a delegator can always get its balance back by its own calls".into(),
            theorems: vec!["StakingPool.exit_guarantee".into()],
            axioms: vec!["propext".into(), "Classical.choice".into(), "Quot.sound".into()],
            assumptions: vec!["the protocol returns unstaked stake in time".into()],
            binding: "hash equals staking_pool.wasm at near/core-contracts@1cacc9d".into(),
            conformance: Conformance { traces: 1149, calls: 55955, mismatches: 0, runtime: "nearcore 2.14.0".into() },
            artifact_sha256: "0".repeat(64),
            artifact_location: "repo@commit".into(),
            check_command: "./check.sh".into(),
        }
    }

    #[test]
    fn owner_attests_and_reads_back() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        ctx(0, 10u128.pow(24));
        let i = r.attest(H.into(), cert());
        assert_eq!(i, 0);
        let got = r.get(H.into());
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].attestor, accounts(0));
        assert_eq!(got[0].body, cert());
        assert_eq!(r.get_valid(H.into()).len(), 1);
        assert_eq!(r.count(), 1);
    }

    #[test]
    #[should_panic(expected = "caller is not an attestor")]
    fn stranger_cannot_attest() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        ctx(1, 10u128.pow(24));
        r.attest(H.into(), cert());
    }

    #[test]
    #[should_panic(expected = "attach at least")]
    fn storage_must_be_paid() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        ctx(0, 0);
        r.attest(H.into(), cert());
    }

    #[test]
    #[should_panic(expected = "code_hash must be a base58 sha256")]
    fn rejects_bad_hash() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        ctx(0, 10u128.pow(24));
        r.attest("not-a-hash".into(), cert());
    }

    #[test]
    fn revoke_keeps_record_and_only_by_attestor() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        r.add_attestor(accounts(1));
        ctx(1, 10u128.pow(24));
        let i = r.attest(H.into(), cert());
        ctx(1, 0);
        r.revoke(i, "model updated".into());
        assert_eq!(r.get(H.into()).len(), 1);
        assert!(r.get(H.into())[0].revoked);
        assert_eq!(r.get_valid(H.into()).len(), 0);
    }

    #[test]
    #[should_panic(expected = "only the attestor can revoke")]
    fn other_attestor_cannot_revoke() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        r.add_attestor(accounts(1));
        ctx(1, 10u128.pow(24));
        let i = r.attest(H.into(), cert());
        ctx(0, 0);
        r.revoke(i, "not mine".into());
    }

    #[test]
    #[should_panic(expected = "kind must be one of")]
    fn rejects_unknown_kind() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        ctx(0, 10u128.pow(24));
        let mut c = cert();
        c.kind = "audit".into();
        r.attest(H.into(), c);
    }

    #[test]
    fn filters_by_kind() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        ctx(0, 10u128.pow(24));
        r.attest(H.into(), cert());
        let mut c = cert();
        c.kind = "token-standard".into();
        ctx(0, 10u128.pow(24));
        r.attest(H.into(), c);
        assert_eq!(r.get_valid(H.into()).len(), 2);
        assert_eq!(r.get_valid_kind(H.into(), "exit".into()).len(), 1);
        assert_eq!(r.get_valid_kind(H.into(), "upgrade-window".into()).len(), 0);
    }

    #[test]
    #[should_panic(expected = "only the owner adds attestors")]
    fn only_owner_adds_attestors() {
        ctx(0, 0);
        let mut r = Registry::new(accounts(0));
        ctx(2, 0);
        r.add_attestor(accounts(3));
    }
}
