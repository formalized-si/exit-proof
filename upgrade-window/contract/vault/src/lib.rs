//! Example contract for the exit-window conformance run.
//!
//! `Upgradable` + `AccessControllable` of near-plugins v0.5.1, configured like the plugin's own
//! example (four roles; `DAO` may call every protected method), around a trivial NEAR vault:
//! `deposit` credits the attached NEAR to the caller, `withdraw` pays it back. The vault has no
//! owner method, no pause and no fee: nothing but a code change can stop a withdrawal.

use near_plugins::{AccessControlRole, AccessControllable, Upgradable, access_control};
// `try_from_slice` in the code the `Upgradable` derive generates needs the trait in scope.
use near_sdk::borsh::BorshDeserialize;
use near_sdk::json_types::U128;
use near_sdk::serde::{Deserialize, Serialize};
use near_sdk::store::LookupMap;
use near_sdk::{AccountId, Duration, NearToken, PanicOnDefault, Promise, env, near, require};

#[cfg(not(any(feature = "v2", feature = "v3")))]
const VERSION: u32 = 1;
#[cfg(all(feature = "v2", not(feature = "v3")))]
const VERSION: u32 = 2;
#[cfg(feature = "v3")]
const VERSION: u32 = 3;

/// Roles for the protected `Upgradable` methods.
#[derive(AccessControlRole, Deserialize, Serialize, Copy, Clone)]
#[serde(crate = "near_sdk::serde")]
pub enum Role {
    /// May call every protected `Upgradable` method.
    DAO,
    /// May call `up_stage_code` only.
    CodeStager,
    /// May call `up_deploy_code` only.
    CodeDeployer,
    /// May call `up_init_staging_duration`, `up_stage_update_staging_duration` and
    /// `up_apply_update_staging_duration`.
    DurationManager,
}

#[access_control(role_type(Role))]
#[near(contract_state)]
#[derive(Upgradable, PanicOnDefault)]
#[upgradable(access_control_roles(
    code_stagers(Role::CodeStager, Role::DAO),
    code_deployers(Role::CodeDeployer, Role::DAO),
    duration_initializers(Role::DurationManager, Role::DAO),
    duration_update_stagers(Role::DurationManager, Role::DAO),
    duration_update_appliers(Role::DurationManager, Role::DAO),
))]
pub struct Vault {
    balances: LookupMap<AccountId, u128>,
}

#[near]
impl Vault {
    /// The contract account becomes the ACL super-admin (as in the plugin's example), so roles
    /// are granted and revoked by transactions of the contract account itself.
    /// `staging_duration`: nanoseconds between staging and deploying code; `None` leaves it unset.
    #[init]
    pub fn new(staging_duration: Option<Duration>) -> Self {
        let mut contract = Self { balances: LookupMap::new(b"b") };
        require!(
            contract.acl_init_super_admin(env::current_account_id()),
            "Failed to initialize super admin",
        );
        if let Some(staging_duration) = staging_duration {
            contract.acl_grant_role(Role::DurationManager.into(), env::current_account_id());
            contract.up_init_staging_duration(staging_duration);
            contract.acl_revoke_role(Role::DurationManager.into(), env::current_account_id());
        }
        contract
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

    /// Targets for the function call that `up_deploy_code` can attach to a deployment.
    #[private]
    pub fn migrate_ok(&mut self) {}

    #[private]
    pub fn migrate_fail(&mut self) {
        env::panic_str("Vault: migration refused");
    }
}
