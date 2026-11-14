//! Gated vault: a NEAR vault whose code can be replaced only by code that
//!   (a) was staged on chain at least `staging_duration` earlier, and
//!   (b) has a valid certificate from an accepted attestor in a certificate registry.
//!
//! The upgrade path is the `Upgradable` plugin of near-plugins v0.5.1 (staging, delay, "only the
//! staged hash"). What this contract adds is the gate in front of the plugin's `up_deploy_code`:
//!
//! * `up_deploy_code` requires the role `CodeDeployer`, and that role is held by the contract's
//!   own account only. The contract account is the only ACL super-admin and is meant to have no
//!   access keys, so the role cannot be granted to anybody else.
//! * `deploy_certified()` — callable by anyone — reads the hash of the staged code, asks the
//!   registry `get_valid_kind(code_hash, kind)`, and in the callback calls the plugin's
//!   `up_deploy_code(hash, None)` only if the answer contains a certificate that is not revoked,
//!   is for exactly that hash and the accepted kind, and was attested by an accepted attestor.
//!   The plugin then checks again that the staged code still has that hash and that its delay has
//!   passed. No function call is attached to the deployment.
//! * The registry account, the accepted kind and the accepted attestors are written once, in
//!   `new`, and no method changes them. The staging duration is set in `new` and nobody holds the
//!   role that could change it.
//!
//! The gate keeps no state between the call and the callback: a failed step leaves nothing
//! behind, and `deploy_certified` can be called again.
//!
//! The vault itself is the one of the exit-window kit: `deposit` credits the attached NEAR to the
//! caller, `withdraw` pays it back. No owner, no pause, no fee.

use near_plugins::{AccessControlRole, AccessControllable, Upgradable, access_control};
// `try_from_slice` in the code the `Upgradable` derive generates needs the trait in scope.
use near_sdk::borsh::BorshDeserialize;
use near_sdk::json_types::U128;
use near_sdk::serde::{Deserialize, Serialize};
use near_sdk::store::LookupMap;
use near_sdk::{
    AccountId, Duration, Gas, GasWeight, NearToken, PanicOnDefault, Promise, PromiseError, env, near, require,
};

#[cfg(not(any(feature = "v2", feature = "v3")))]
const VERSION: u32 = 1;
#[cfg(all(feature = "v2", not(feature = "v3")))]
const VERSION: u32 = 2;
#[cfg(feature = "v3")]
const VERSION: u32 = 3;

/// Gas reserved for the registry's `get_valid_kind`, and its share of the gas left over.
const GAS_REGISTRY: Gas = Gas::from_tgas(10);
const WEIGHT_REGISTRY: u64 = 1;
/// Gas reserved for the callback (it reads and hashes the staged code and creates the deploy
/// batch), and its share of the gas left over.
const GAS_CALLBACK: Gas = Gas::from_tgas(60);
const WEIGHT_CALLBACK: u64 = 3;

/// Roles for the protected `Upgradable` methods. One role per kind of method, no role that may
/// call everything.
#[derive(AccessControlRole, Deserialize, Serialize, Copy, Clone)]
#[serde(crate = "near_sdk::serde")]
pub enum Role {
    /// May call `up_stage_code`. Granted in `new` to the accounts listed there.
    CodeStager,
    /// May call `up_deploy_code`. Granted in `new` to the contract's own account only.
    CodeDeployer,
    /// May call the three methods that change the staging duration. Held by nobody.
    DurationManager,
}

/// What the gate accepts. Written once, in `new`.
#[near(serializers = [borsh, json])]
#[derive(Clone)]
pub struct Gate {
    /// The certificate registry that is asked.
    pub registry: AccountId,
    /// The certificate kind that counts.
    pub kind: String,
    /// The attestors whose certificates count.
    pub attestors: Vec<AccountId>,
}

/// The fields of a registry certificate the gate reads; the rest of the answer is ignored.
#[derive(Deserialize)]
#[serde(crate = "near_sdk::serde")]
pub struct CertificateBody {
    pub kind: String,
}

#[derive(Deserialize)]
#[serde(crate = "near_sdk::serde")]
pub struct Certificate {
    pub code_hash: String,
    pub body: CertificateBody,
    pub attestor: AccountId,
    pub revoked: bool,
}

#[access_control(role_type(Role))]
#[near(contract_state)]
#[derive(Upgradable, PanicOnDefault)]
#[upgradable(access_control_roles(
    code_stagers(Role::CodeStager),
    code_deployers(Role::CodeDeployer),
    duration_initializers(Role::DurationManager),
    duration_update_stagers(Role::DurationManager),
    duration_update_appliers(Role::DurationManager),
))]
pub struct Vault {
    balances: LookupMap<AccountId, u128>,
    gate: Gate,
}

#[near]
impl Vault {
    /// Sets everything up in one call made by the contract account itself (the deployment
    /// transaction): the gate, the staging duration, and the roles. Nothing of this needs a
    /// second transaction, so the contract account's key can be deleted right after.
    ///
    /// * `staging_duration`: nanoseconds between staging code and the earliest deployment; > 0.
    /// * `registry`, `certificate_kind`, `attestors`: what `deploy_certified` accepts.
    /// * `stagers`: the accounts that may stage code.
    #[init]
    #[private]
    pub fn new(
        staging_duration: Duration,
        registry: AccountId,
        certificate_kind: String,
        attestors: Vec<AccountId>,
        stagers: Vec<AccountId>,
    ) -> Self {
        let me = env::current_account_id();
        require!(staging_duration > 0, "Gate: the staging duration must be positive");
        require!(registry != me, "Gate: the registry must be another account");
        require!(!certificate_kind.is_empty(), "Gate: the certificate kind must not be empty");
        require!(!attestors.is_empty(), "Gate: at least one accepted attestor");
        let mut contract = Self {
            balances: LookupMap::new(b"b"),
            gate: Gate { registry, kind: certificate_kind, attestors },
        };
        require!(contract.acl_init_super_admin(me.clone()), "Failed to initialize super admin");
        // the staging duration, through the plugin's own initializer
        require!(
            contract.acl_grant_role(Role::DurationManager.into(), me.clone()) == Some(true),
            "Failed to grant DurationManager",
        );
        contract.up_init_staging_duration(staging_duration);
        require!(
            contract.acl_revoke_role(Role::DurationManager.into(), me.clone()) == Some(true),
            "Failed to revoke DurationManager",
        );
        // the only holder of CodeDeployer: this account
        require!(
            contract.acl_grant_role(Role::CodeDeployer.into(), me.clone()) == Some(true),
            "Failed to grant CodeDeployer",
        );
        for stager in stagers {
            require!(
                contract.acl_grant_role(Role::CodeStager.into(), stager).is_some(),
                "Failed to grant CodeStager",
            );
        }
        contract
    }

    /// The only way to a deployment. Callable by anyone; the caller pays the gas (300 Tgas is
    /// enough for the examples; what is not used is refunded) and attaches no deposit.
    ///
    /// Fails at once if nothing is staged or the staging delay has not passed. Otherwise asks the
    /// registry for the valid certificates of the staged code's hash; `on_certificates` decides.
    pub fn deploy_certified(&self) -> Promise {
        let hash = self.up_staged_code_hash().unwrap_or_else(|| env::panic_str("Gate: no staged code"));
        let staging_timestamp = self
            .up_get_delay_status()
            .staging_timestamp
            .unwrap_or_else(|| env::panic_str("Gate: staging timestamp isn't set"));
        if env::block_timestamp() < staging_timestamp {
            env::panic_str(&format!("Gate: deploy too early: staging ends on {staging_timestamp}"));
        }
        env::log_str(&format!("Gate: asking {} for a {} certificate of {}", self.gate.registry, self.gate.kind, hash));
        let query = near_sdk::serde_json::json!({ "code_hash": hash, "kind": self.gate.kind });
        let callback = near_sdk::serde_json::json!({ "hash": hash });
        Promise::new(self.gate.registry.clone())
            .function_call_weight(
                "get_valid_kind".to_owned(),
                query.to_string().into_bytes(),
                NearToken::from_yoctonear(0),
                GAS_REGISTRY,
                GasWeight(WEIGHT_REGISTRY),
            )
            .then(Promise::new(env::current_account_id()).function_call_weight(
                "on_certificates".to_owned(),
                callback.to_string().into_bytes(),
                NearToken::from_yoctonear(0),
                GAS_CALLBACK,
                GasWeight(WEIGHT_CALLBACK),
            ))
    }

    /// The callback of `deploy_certified`: `hash` is the hash the registry was asked about.
    /// Deploys only if the registry's answer holds a certificate that is not revoked, is for
    /// `hash` and the accepted kind, and comes from an accepted attestor. The deployment itself is
    /// the plugin's `up_deploy_code(hash, None)`: it panics unless the code staged now has this
    /// hash and its staging timestamp has passed. Any panic here leaves the contract as it was.
    #[private]
    pub fn on_certificates(
        &mut self,
        hash: String,
        #[callback_result] certificates: Result<Vec<Certificate>, PromiseError>,
    ) -> Promise {
        let certificates = certificates.unwrap_or_else(|_| env::panic_str("Gate: the registry call failed"));
        let accepted = certificates.iter().find(|c| {
            !c.revoked && c.code_hash == hash && c.body.kind == self.gate.kind && self.gate.attestors.contains(&c.attestor)
        });
        let Some(certificate) = accepted else {
            env::panic_str(&format!(
                "Gate: no valid {} certificate from an accepted attestor for {}",
                self.gate.kind, hash
            ))
        };
        env::log_str(&format!("Gate: certificate of {} accepted for {}", certificate.attestor, hash));
        self.up_deploy_code(hash, None)
    }

    /// What the gate accepts.
    pub fn gate(&self) -> Gate {
        self.gate.clone()
    }

    /// Credits the attached NEAR to the caller.
    #[payable]
    pub fn deposit(&mut self) {
        let who = env::predecessor_account_id();
        let amount = env::attached_deposit().as_yoctonear();
        let balance = self.balances.get(&who).copied().unwrap_or(0);
        let new_balance = balance.checked_add(amount).unwrap_or_else(|| env::panic_str("Vault: overflow"));
        self.balances.insert(who, new_balance);
    }

    /// Pays `amount` of the caller's balance back to the caller. The exit path.
    pub fn withdraw(&mut self, amount: U128) -> Promise {
        let who = env::predecessor_account_id();
        let balance = self.balances.get(&who).copied().unwrap_or(0);
        let new_balance =
            balance.checked_sub(amount.0).unwrap_or_else(|| env::panic_str("Vault: insufficient balance"));
        self.balances.insert(who.clone(), new_balance);
        Promise::new(who).transfer(NearToken::from_yoctonear(amount.0))
    }

    pub fn balance_of(&self, account_id: AccountId) -> U128 {
        U128(self.balances.get(&account_id).copied().unwrap_or(0))
    }

    /// Which build is running.
    pub fn version(&self) -> u32 {
        VERSION
    }
}
