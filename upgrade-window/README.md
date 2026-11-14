# Exit window: the `Upgradable` plugin of near-plugins v0.5.1

Exit Proof answers "can I always get my money back from this NEAR contract, and who could stop
me?". For immutable code the answer is a Lean exit theorem. Most live contracts are upgradable,
so a second tier is needed: a contract is **exit-window safe** if any change of its code becomes
effective only after a publicly visible delay `D`, long enough for users to leave.

Many NEAR contracts get their upgrade path from the `Upgradable` plugin of
[near-plugins](https://github.com/near/near-plugins) (`up_stage_code`, `up_deploy_code`,
`up_init_staging_duration`, …). This directory holds, for the plugin version a current mainnet
user pins:

1. **A Lean model** of the plugin's state machine, statement by statement from its source.
2. **Theorems W1–W5** (Lean 4.35, no `sorry`): what the staging delay guarantees, the exact
   earliest time a deployment can succeed, the ways around a naive reading of the delay, and the
   exit window a user gets.
3. **Conformance**: an example vault built with the pinned plugin, executed on the nearcore
   runtime and compared with the model on 1000 random traces; 12 one-line mutants of the plugin,
   each detected.
4. **`check-upgrade-window.py <account>`**: reads a mainnet account and prints the window it has now.

## The problem

"No full-access key" does not mean the code cannot change: the right to replace the code lives in
contract methods and roles. The plugin offers a delay between staging new code and deploying it.
Whether that delay protects a depositor depends on three things nobody can see from an explorer:

- is a delay set at all;
- can the holders of the upgrade roles get around it;
- is there a signal a depositor can watch, and how long before the new code takes effect does it appear.

Read on mainnet on 2026-11-12 (`evidence/mainnet_readings.txt`): `token.sweat`,
`lst.rhealab.near`, `ctl-intents.near` and `omni.bridge.near` all expose the plugin and all four
report `staging_duration: null` — by theorem W4, no exit window.

## Do X — see Y

| Do | Command | See |
|---|---|---|
| Check a mainnet account | `./check-upgrade-window.py <account>` (add `--json`) | delay, staged code, pending duration change, window now |
| Read the statements | — | `lean/UpgradeWindow/Theorems.lean` (docstrings), table below |
| Re-check the proofs | `cd lean && lake build && lake env lean Axioms.lean` | `evidence/axioms.txt` |
| See the statements happen on the wasm | `./check.sh` (step 5) | `evidence/witness.json` |
| Compare the wasm with the model | `./scripts/conformance.sh` | `evidence/conformance.json` |
| Check that deviations are caught | `./check.sh --mutants` | `evidence/mutants.json`, `evidence/mutants.diff` |
| Repeat everything | `./check.sh` (≈2 min), `./check.sh --mutants` (≈9 min) | `evidence/check_run.txt` |

Needs: Linux x86-64, `elan` (Lean 4.35.0 is installed from `lean/lean-toolchain`), `rustup` (Rust
1.95.0 for the harness, 1.86.0 with `wasm32-unknown-unknown` for the vault, from the
`rust-toolchain.toml` files), a C/C++ compiler, `cmake` and libclang (for nearcore's RocksDB
bindings), `python3`, `git`; cargo-near 0.22 for rebuilding the vault and for the mutants. The
harness is built against the public `near/near-contract-sim` at commit `8e4b69b` (which pins
nearcore 2.14.0); both are git dependencies, locked in `harness/Cargo.lock`. Without root, libclang
can be taken from the Python package: `python3 -m pip install libclang`, then set `LIBCLANG_PATH`
to its `site-packages/clang/native` directory and add there a link named after the library's
soname (`ln -s libclang.so libclang.so.18.1`). Build directories can be moved with
`CARGO_TARGET_DIR` and `UW_CONTRACT_TARGET` (`scripts/env.sh`). `check-upgrade-window.py` needs
only Python 3.

`check.sh` exits with 0 only if the proofs build without `sorry`, the axioms are among `propext`,
`Classical.choice`, `Quot.sound`, the plugin source matches `PLUGIN_PIN.json`, the vault wasm
files have the pinned hashes, every witness scenario holds and both conformance runs report no
divergence and no monitor violation (with `--mutants`: also the control passes and every mutant
is detected in the expected statement). The six vault builds the checks run on are committed
(`contract/out/`, `contract/out-unchecked/`), checked against `contract/VAULT_WASM_SHA256` and
`contract/VAULT_UNCHECKED_WASM_SHA256`, and never overwritten. When cargo-near is installed,
`check.sh` also rebuilds them from source into `runs/` and requires the same bytes; rustc embeds
the path of cargo's home in panic locations, so `scripts/build-contract.sh` maps it to the path of
the pinned builds. The wasm hashes of the mutant builds in `evidence/mutants.json` depend on the
directory they were built in (the patched plugin is a path dependency); the results and the counts
do not.

Measured on a machine with none of the toolchains installed (fresh home directory, 32 cores, 2026-11-12): `./check.sh` took 522 s and `./check.sh --mutants` 560 s more, both with exit code 0; with the toolchains and the harness already built, `./check.sh` takes about 2 minutes.

## Results

| | Result |
|---|---|
| Pinned plugin | near-plugins **v0.5.1**, commit `312e016e0574d5756f6eba37acc82d9a237b2e3e` — the `Cargo.lock` entry of `Sweat-Foundation/sweat-token@75dc5b48` (near-sdk 5.26.1, Rust 1.86). Source hashes in `PLUGIN_PIN.json`, checked by `scripts/fetch-plugin.sh` |
| Theorems | W1–W5 and their variants: 34 theorems listed in `lean/Axioms.lean`, Lean 4.35, no `sorry`; axioms `propext`, `Quot.sound` (plus `Classical.choice` in `W1_delay`, `W2_visibility`, `deploy_origin`, `W3_tight`) |
| Is there a way around the delay? | **Yes, three**, all inside the plugin; the corrected bound `safeUntil` is proved and proved tight for builds with overflow checks, and a lower bound `safeUntilU` is proved for builds without (section "W3") |
| Witness scenarios on the wasm | 7 scenarios, 31 checks, all hold (`evidence/witness.json`) |
| Conformance | **1000 traces, 37 736 receipts, 49 948 blocks: 0 divergences, 0 monitor violations**; a second run with another seed, 5000 traces, 192 437 receipts: the same (`evidence/conformance_seed777.json`). The build without overflow checks against the model of that build: 1000 traces, 37 757 receipts, 0 divergences (`evidence/conformance_unchecked.json`) |
| Mutants | **12 of 12 detected**, each first divergence in the expected statement; unmutated control passes |
| Mainnet, 4 accounts | all four: plugin interface present, `staging_duration` unset → **no exit window** |
| Build | the example vault rebuilds byte for byte (`contract/VAULT_WASM_SHA256`), 198 808 bytes |

## The statements

`t`, `D`, `now` are block timestamps and durations in nanoseconds (u64). "Permitted" = the
access-control check passed. Every theorem holds for **every** assignment of permissions in a
trace: an adversary holding all roles, or changing roles at will, is included.

| | Statement | Theorem |
|---|---|---|
| **W1 delay** | Starting with nothing staged: a successful `up_deploy_code` deploys exactly the code of the last permitted `up_stage_code`, and its block timestamp is at least `min(t + D, u64::MAX)`, `t` being the block timestamp of that staging and `D` the staging duration at that moment (`deploy_origin` states the same with `D = 0` when no duration was set). | `W1_delay`, `deploy_origin` |
| **W2 visibility** | From that staging until the deploy, the view `up_staged_code_hash` returns one and the same hash at every moment; the deploy succeeds only if its `hash` argument equals it, and the promise carries the code with that hash. | `W2_visibility` |
| **W3 no deploy before `safeUntil`** | From any state at block timestamp `t0`, along any trace with non-decreasing timestamps, an `up_deploy_code` call succeeds only at a block timestamp `≥ safeUntil(state, t0)`. A batch that later changes the code either was already in flight at `t0` or was created by such a call. The bound is tight: from every well-formed state (all reachable ones are) and with all roles, some deploy call succeeds at exactly `max(t0, safeUntil(state, t0))` (in the proof: of the staged code when its timestamp is the minimum, of newly staged code otherwise). | `W3_no_deploy_before`, `W3_code_change_any`, `W3_code_change`, `W3_tight` |
| **W3a/b duration changes** | A call changes the duration only by `up_init_staging_duration` when none is set, or by `up_apply_update_staging_duration`, which installs the staged value and needs the block timestamp to have reached the update's timestamp; that timestamp is written only by `up_stage_update_staging_duration`, as its own block timestamp plus the duration then in force. | `W3a_duration_change`, `W3b_update_staged` |
| **W4 the null case** | With no staging duration, any code can be staged and its deployment accepted at the same block timestamp; with nothing in flight, three events at one timestamp (stage, deploy, the batch succeeding) replace the code. On the wasm: one transaction, the code replaced by the next receipt (`evidence/witness.json`). | `W4_no_window`, `W4_witness` |
| **W5 a quiet reading** | If at block timestamp `t0` the plugin's state shows duration `D` and no alarm, no `up_deploy_code` call succeeds before `t0 + D` (saturating at `u64::MAX`); a change of the code before `t0 + D` can only come from a deploy batch that was already in flight at `t0`, and with none in flight there is no such change. | `W5_quiet_reading`, `W5_quiet_reading_code_any`, `W5_quiet_reading_code` |
| **W5 notice** | From such a state: before any successful `up_deploy_code` call, and — with no deploy batch in flight at the start — before any change of the code, there is a first event that raises the alarm, at some block timestamp `ta`, and the call / the change comes at `ta + D` or later. | `W5_notice`, `W5_code_change` |
| **W5 exits** | Arithmetic on top of the two rows above, conditional on premises that are assumed, not proved: a watcher who reads again within `P` and an exit that takes at most `T`, with `P + T ≤ D` — then the exit is over no later than any successful deploy call (`W5_polling_call`) and, with no deploy batch in flight at the first reading, no later than the change of code (`W5_polling`); or an exit started at the alarm with `T ≤ D` (`W5_exit_window`, `W5_exit_before_code_change`). All four also need `t + D` to fit in u64. | `W5_polling_call`, `W5_polling`, `W5_exit_window`, `W5_exit_before_code_change` |
| **W3 / W5 without overflow checks** | For a build without overflow checks (shortcut 3 below), statements about the deploy call only: no `up_deploy_code` call succeeds before `safeUntilU` — `safeUntil` with every duration above a threshold `B` counted as 0 — on traces whose block timestamps stay at or below `u64::MAX − B`; and the quiet-reading statement for the deploy call, with the alarm extended by "a current or staged duration above `B`". A lower bound, not tight. | `W3U_no_deploy_before`, `W5U_quiet_reading`, `callU_eq_call` |

**Alarm** (`Model.lean`, `alarm`): code is staged (`staging_timestamp` is set), or a staged
duration update is shorter than the current duration. For a build without overflow checks
(`Unchecked.lean`, `alarmU`): also a current or staged duration above `B`.

What is by construction rather than proved: in the model the code on the account changes only
when a deploy batch executes (assumption A3). `W3_code_change` and `W5_code_change` are about
events after which the code is a *different* code; a re-deployment of identical code with an
attached function call is covered by the statements about the deploy call.

### W3: is there a shortcut around the delay?

The naive statement — "with duration `D`, no code is deployed earlier than `D` after its staging
became visible" — is **false**. Three ways around it, each a theorem with a witness and each run
on the wasm (`evidence/witness.json`):

| | Shortcut | Theorem |
|---|---|---|
| 1 | **Code staged before the delay existed.** Code staged while no duration is set keeps its staging timestamp: after `up_init_staging_duration(7 days)` the status shows a 7-day delay, and that code is deployable at once. (The staging timestamp is written when the code is staged and no later change of the duration touches it — `deploy_origin` — so code staged under an earlier, shorter duration keeps that one too.) | `W3_prestaged_shortcut` |
| 2 | **Shrink the delay first.** Stage an update of the duration to 0, apply it `D` later, then stage and deploy new code in one transaction. The code itself was visible for no time; what was visible for `D` is the staged duration update. | `W3_shrink_shortcut` |
| 3 | **A build without overflow checks.** `up_stage_update_staging_duration` computes `block_timestamp + duration` with a plain `+`. With `overflow-checks = true` (the example) an overflow panics. Without (cargo's release profile unless the workspace says otherwise) it wraps: if `now + D > u64::MAX`, an update staged now carries a timestamp in the past and is applicable at once. So a duration that large is no delay — and neither is an ordinary `D` once an update to such a value has been staged and applied: stage an update to `u64::MAX` (a *longer* duration: no alarm of the checked build), apply it `D` later, and at that same block timestamp remove the delay and deploy. | `W3_unchecked_shortcut`, `W3U_grow_then_remove`, `alarmU_flags_huge_update` |

Not shortcuts (covered by the model, ruled out by W1/W3): re-staging (replaces code and
restarts its clock), cancelling by staging empty input (removes code and timestamp),
`up_init_staging_duration` a second time (refused), repeating `up_apply_update_staging_duration`
(re-installs the same value), re-staging a duration update (restarts its clock).

**The corrected statement** uses one number a watcher can compute from `up_get_delay_status`:

```
safeUntil(status, now) = min( now + staging_duration,                       -- code staged from now on
                              staging_timestamp            if code is staged,
                              max(now, new_staging_duration_timestamp)
                                + new_staging_duration     if a duration update is staged )
```

(sums saturate at `u64::MAX`; with no duration the first term is `now`). Then:

- no `up_deploy_code` call can succeed before `safeUntil`, whoever holds the roles (`W3_no_deploy_before`);
- `safeUntil` never decreases, whatever is called and however long one waits (`safeUntil_run`):
  a watcher who polls every `P` and sees a window of at least `P + T` still has `T` at the next poll;
- it is tight (`W3_tight`);
- with no alarm, `safeUntil = now + D` (`quiet_safeUntil`).

For a build without overflow checks the first of these holds with `safeUntilU`: every duration
above `B` replaced by 0 (`W3U_no_deploy_before`, for block timestamps up to `u64::MAX − B`; with
`B = 2^63` that is until the year 2262, and durations above `B` exceed 292 years). It is a lower
bound, deliberately not tight: a duration above `B` that would not overflow yet is counted as 0
all the same. Where no `block_timestamp + duration` overflows the two builds make the same call
(`callU_eq_call`).
`check-upgrade-window.py` cannot know how a deployed contract was built, so it computes
`safeUntilU` with `B = 2^63`.

### W5: what a watcher gets, and what is assumed

- **A watcher that polls** relies on the quiet reading: duration `D`, no alarm at `t0` ⇒ no deploy
  call before `t0 + D` (`W5_quiet_reading`), whatever happens in between and whether or not the
  watcher sees it; and a change of the code before `t0 + D` can only come from a batch already
  in flight at `t0` (`W5_quiet_reading_code_any`). The alarm itself can be raised and cleared inside one block (stage and cancel
  in one transaction), so a poller may never see the event `W5_notice` speaks of; it does not
  need to. `T` has to include the time to notice, and v0.5.1 emits no events for these calls.
- **A deploy batch in flight is invisible in the views.** `W5_quiet_reading_code`,
  `W5_code_change` and `W5_polling` assume none at `t0`. One can exist for the block or two after a successful `up_deploy_code`; in particular,
  with no duration set, one block can stage, deploy, un-stage and initialise a duration: the next
  reading is quiet with duration `D`, and the code changes one block later (run on the wasm:
  `inflight_invisible` in `evidence/witness.json`). A quiet reading says nothing about a batch
  created just before it; the account's recent receipts do.
- **The exit itself is an assumption.** `W5_polling`, `W5_exit_window` and
  `W5_exit_before_code_change` take "the exit is complete within `T`" as a premise about the host
  contract and add arithmetic. For the example vault two small theorems support it at the level
  of the model — `vault_exit` (a withdrawal of the whole balance succeeds in one call in every
  vault state) and `vault_others` (no other account's call changes a balance) — and the
  conformance run supports it on the wasm (balances and withdrawal outcomes agree with the model
  in every trace). They say nothing about time, and there is one way the upgrade roles do get in
  the way, run on the wasm (`A5_storage_staking` in `evidence/witness.json`): staged code is
  stored by the contract and its storage is paid from the contract's balance, depositors' NEAR
  included. With 199 KB staged (about 2 NEAR), a full withdrawal from a vault holding only its
  deposits fails with `LackBalanceForState` until the staged code is removed; about 10 NEAR per
  MiB of staged code, at most 4 MiB.

## The model (`lean/UpgradeWindow/Model.lean`)

- The five storage slots under `__up__` and the five protected methods, statement by statement
  from `near-plugins-derive/src/upgradable.rs` (line numbers in the comments), with every panic.
- u64 arithmetic as written: `saturating_add` for the staging timestamp, checked `+` for the
  duration update's timestamp.
- `up_deploy_code` returns a promise: a batch on the contract's own account
  `[DeployContract(code), FunctionCall(args)?, FunctionCall(up_verify_state)]`, executed by a
  later receipt, all or nothing. The model keeps the batches in flight and the code on the account.
- Parameters: the code hash function `H` (bs58 of sha256), and on every call a boolean `allowed`
  — the outcome of the access-control check. Theorems quantify over all of them.
- The function call attached to a deployment runs as the contract itself and may be one of the
  plugin's own methods; in the model that is the batch followed by a call at the same timestamp.
- `lean/UpgradeWindow/Unchecked.lean`: the same machine for a build without overflow checks
  (`Up.callU`, `runU`), its bound `safeUntilU` and its theorems.
- `lean/UpgradeWindow/Example.lean`: the example's four roles, a minimal access-control state and
  the vault — used by the conformance run, not by W1–W5.
- `lean/UpgradeWindow/Examples.lean`: one concrete run (stage, deploy one hour later, batch) on
  which the hypotheses of W1, W3, W5 (notice, code change, polling) and of the unchecked
  variant hold, with the theorems applied to it (the statements are not vacuous).

## Conformance (`scripts/conformance.sh`)

| Part | What it does |
|---|---|
| `contract/vault` | Example contract: `AccessControllable` + `Upgradable` of the pinned plugin (roles `DAO`, `CodeStager`, `CodeDeployer`, `DurationManager`) around a NEAR vault with `deposit` / `withdraw`; dependency versions from the `Cargo.lock` of sweat-token@75dc5b48; built with cargo-near in three versions that differ in `version()` |
| `harness/` (`uw-gen`) | Deploys the wasm on near-contract-sim (nearcore 2.14.0 runtime in process). Random traces: staging of three vault builds, non-wasm bytes, a stub without `withdraw`, empty input; deploys with right and wrong hashes and with attached function calls that succeed, fail or do not exist; duration init / update / apply with durations from 0 to `u64::MAX`; clock jumps to one nanosecond before, exactly at and after each timestamp; role grants, revocations, renunciations; calls by accounts without roles; deposits and withdrawals; malformed arguments, deposits on non-payable methods, re-init. Operations share blocks, so a deploy batch can run after another staging |
| `lean/Main.lean` (`uwmodel`) | Replays every receipt through `Up.call` / `Sys.step` |
| `scripts/compare.py` | Per receipt: success or failure, the panic text (with its numbers), the return value, the receipts created (the deploy batch's actions, methods, arguments, gas, deposit; the withdrawal transfer). Per block: the five storage slots read from the trie, the same through the views, the staged code, the account's code hash and `version()`, role grants, vault balances |
| Model-free monitors | From the wasm's data only: `safeUntil` computed from storage after every block never decreases; no deploy call succeeds before it; a deploy runs at or after the staging timestamp, with the hash the view showed; a successful batch makes the account's code hash that hash |

Coverage of the 1000-trace run (`evidence/conformance.json`): 1116 accepted deploys (77 at exactly
the staging timestamp, 27 refused one nanosecond before it, 505 refused as too early, 302 wrong
hash), 605 deploy batches succeeded and 511 rolled back, 577 code replacements (22 by the stub),
944 duration updates applied (76 at exactly their timestamp, 18 refused one nanosecond before),
193 overflow panics, 6017 calls refused by access control, 99 traces reaching a saturated staging
timestamp, 355 traces starting without a duration.

Witness scenarios (`uw-gen witness`, `evidence/witness.json`), with the clock stopped at chosen
timestamps: W4 in one transaction with a stub (the next withdrawal fails: `MethodNotFound`);
W1/W2/W5 with `D` = 1 h (withdrawal inside the window, deploy refused at `t + D − 1`, wrong hash
refused, accepted at `t + D`, and the stale staged copy re-deployed 30 days later with a
`#[private]` call attached); shortcuts 1 and 2; shortcut 3 on the same source built without
overflow checks, next to the checked build's panic; storage staking by staged code blocking a
withdrawal; a deploy batch in flight behind a quiet reading.

The build without overflow checks is compared with its own model the same way
(`UW_UNCHECKED=1 ./scripts/conformance.sh contract/out-unchecked`): 145 duration updates whose
timestamp wrapped, 0 divergences, and the monitors, computed with `safeUntilU`, never fired.

## Mutants (`scripts/mutants.py`, `evidence/mutants.json`, `evidence/mutants.diff`)

One changed line of `near-plugins-derive/src/upgradable.rs` each; all three vault builds
recompiled with cargo-near; the conformance run with default settings.

| Mutant | Changed line | Result | First divergence → statement | Diverging traces of 1000 | Model-free monitors (blocks / calls) |
|---|---|---|---|---|---|
| M0 control | none (the same path patch) | **PASS** | — | 0 | — |
| M1 | up_deploy_code: comparison flipped (deploy allowed only before the staging timestamp) | FAIL | a deploy after the staging timestamp is refused → **W1** | 657 | deploy before `safeUntil` 330, deploy before the staging timestamp 324 |
| M2 | up_deploy_code: accepted one nanosecond before the staging timestamp | FAIL | a deploy 1 ns before the staging timestamp succeeds → **W1** | 27 | deploy before `safeUntil` 27, deploy before the staging timestamp 27 |
| M3 | up_stage_code: staging timestamp = block timestamp, the duration is not added | FAIL | staging timestamp in storage → **W1** | 603 | `safeUntil` decreased 453, deploy before `safeUntil` 233 |
| M4 | up_deploy_code: the hash argument is not checked | FAIL | a deploy with another hash succeeds → **W2** | 227 | deploy with another hash 289 |
| M5 | up_stage_update_staging_duration: the update is applicable at once | FAIL | the update's timestamp in storage → **W3** | 612 | `safeUntil` decreased 325, deploy before `safeUntil` 36 |
| M6 | up_stage_update_staging_duration: writes the staging duration itself | FAIL | staging duration in storage → **W3** | 653 | `safeUntil` decreased 232, deploy before `safeUntil` 29 |
| M7 | up_apply_update_staging_duration: the timestamp is not checked | FAIL | an early apply succeeds → **W3** | 145 | `safeUntil` decreased 55, deploy before `safeUntil` 7 |
| M8 | up_init_staging_duration: allowed when a duration is already set | FAIL | a second init succeeds → **W3** | 545 | `safeUntil` decreased 237, deploy before `safeUntil` 66 |
| M9 | up_stage_update_staging_duration: wrapping instead of checked addition | FAIL | an overflowing update is accepted → **W3** | 94 | `safeUntil` decreased 84, deploy before `safeUntil` 20 |
| M10 | up_stage_code: wrapping instead of saturating addition | FAIL | staging timestamp in storage (wrapped, not saturated) → **W1** | 99 | `safeUntil` decreased 80, deploy before `safeUntil` 61 |
| M11 | up_stage_code with empty input: the staging timestamp is left in storage | FAIL | staging timestamp still in storage after removal → **W1** | 295 | — |
| M12 | up_deploy_code: checks the code stagers' roles instead of the deployers' | FAIL | who may deploy → **ACL** | 793 | — |

The last column is the model-free channel: the wasm contradicting W1–W3 by its own data, without
the model. M11 and M12 change what the plugin stores or whom it lets in, not when a deploy can
succeed, so only the model comparison sees them.

## Mainnet readings (`evidence/mainnet_readings.txt`, `.json`)

`./check-upgrade-window.py <account>`, 2026-11-12, one final block per account. Role holders are
reported as counts only.

| Account | Plugin interface | Staging duration | Staged code | Pending duration change | Full-access keys | Exit window now |
|---|---|---|---|---|---|---|
| `token.sweat` | yes | none | a copy of the deployed code | none | 0 | **none** |
| `lst.rhealab.near` | yes | none | none | none | 0 | **none** |
| `ctl-intents.near` | yes | none | a copy of the deployed code | none | 0 | **none** |
| `omni.bridge.near` | yes | none | a copy of the deployed code | none | 0 | **none** |

The checker detects the plugin's interface, not its version: it does not compare the deployed
wasm with v0.5.1.

## Limits

| The theorems assume | Not covered — check separately (the scanner) |
|---|---|
| **A1. Access control is arbitrary.** Nothing is assumed about who holds which role; that is the strength of W1–W5, and also their limit: they say *when*, never *who* | Who holds the roles, how many keys stand behind them; a super-admin can grant itself any role at once |
| **A2. Only the plugin's five methods write the plugin's storage** (the `__up__` slots) | Host code that calls the helpers the derive also generates (`up_set_staging_duration_unchecked`, `up_storage_write`, `up_set_timestamp`, `up_set_duration`) — in a constructor, a setter, or a migration reachable through the function call attached to a deployment; a host method that writes arbitrary storage keys; a storage-prefix collision |
| **A3. The code changes only through `up_deploy_code`** | Full-access keys on the account (`DeployContract` directly — the checker counts them), custom upgrade or migration methods of the host contract, deletion and re-creation of the account, a global contract referenced by account id |
| **A4. The deployed code is the modelled plugin** | The checker sees the interface only. After the first code change the new code decides everything: the theorems are about the window before it |
| **A5. Exits complete within `T` and cannot be blocked by the role holders** (premise of the W5 exit corollaries; not proved for any contract here) | Pause roles (the `Pausable` plugin), freezes, deny lists, exits that need a third party; storage staking by staged code (shown above for the example vault) |
| **A6. Block timestamps do not decrease** | — (protocol rule) |
| **A7. Overflow checks on** (`Model.lean`, W1–W5), **or** the variant for builds without them (`Unchecked.lean`: durations above `B` count as nothing, block timestamps up to `u64::MAX − B`) | The build profile of a deployed contract: cargo's release profile has overflow checks off unless the workspace turns them on, and `cargo near build` uses the release profile by default. For the unchecked variant only the statements about the deploy call are proved (`W3U_no_deploy_before`, `W5U_quiet_reading`): no tightness, no statement about the code on the account or batches in flight, no notice form |

Further limits:

- **The attached function call is not visible in advance.** W2 covers the code. The arguments of
  `up_deploy_code` (method name, arguments, deposit, gas of the call run right after the
  deployment, as the contract itself) are chosen at deploy time.
- **No events.** v0.5.1 defines `stage_code` / `deploy_code` events and never emits them; none of
  the successful calls of the five protected methods in the conformance runs logged anything
  (`protected_calls_ok_that_logged_something: 0`). A watcher has to poll the views.
- **A deploy batch in flight is not visible in the views** (section W5); `W3_code_change`,
  `W5_code_change`, `W5_quiet_reading_code` and `W5_polling` start from a state without one,
  `W3_code_change_any` and `W5_quiet_reading_code_any` say what holds with one.
- **Conformance is a comparison on 1000 traces of one example contract, not a proof** about wasm.
  Outside the proved model: the argument-decoding layer (JSON as near-sdk 5.26.1 reads it, the
  deposit check, `#[private]`), which is checked on the harness inputs only; gas and storage
  staking, which are not modelled; the sha256/bs58 hash, which is a parameter.
- **Mainnet readings are four accounts at one block each.** They say what the plugin's views
  return, not how those contracts are built or governed.

## Files

- `lean/UpgradeWindow/Model.lean`, `Theorems.lean`, `Unchecked.lean`, `Example.lean`, `Examples.lean`; `lean/Main.lean` (`uwmodel`, `uwmodel --unchecked`); `lean/Axioms.lean`
- `PLUGIN_PIN.json`, `scripts/fetch-plugin.sh`
- `contract/vault/` (source, `Cargo.lock`, toolchain), `scripts/build-contract.sh`; the committed builds
  `contract/out/` and `contract/out-unchecked/` with their pinned hashes `contract/VAULT_WASM_SHA256` and
  `contract/VAULT_UNCHECKED_WASM_SHA256`; `NOTICE`
- `harness/` (`uw-gen`: `traces`, `witness`, `info`)
- `scripts/conformance.sh`, `scripts/compare.py`, `scripts/mutants.py`, `scripts/env.sh`, `check.sh`
- `check-upgrade-window.py`
- `evidence/`: `axioms.txt`, `witness.json`, `conformance.json`, `conformance_seed777.json`, `conformance_unchecked.json`, `mutants.json`, `mutants.diff`, `vault_wasm_sha256.txt`, `mainnet_readings.txt`, `mainnet_readings.json`, `check_run.txt`
- `check.sh` and the scripts write their working output to `runs/`, `mutants/` and `plugin/` (the plugin
  source cloned by `scripts/fetch-plugin.sh`) and the harness build to `harness/target/`; none of these is
  part of the repository.
