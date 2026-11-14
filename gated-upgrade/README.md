# Gated upgrades: a certificate gate in front of the `Upgradable` plugin

A proof about an upgradable contract is a proof about its current code: it dies with the next
upgrade. This directory holds a contract for which that sentence stops being the end of the story.
The code of the **gated vault** can be replaced only by code that

- **(a)** was staged on chain at least a fixed time `D` in advance, with its hash visible all that
  time, and
- **(b)** has, at the moment of deployment, a valid certificate from an accepted attestor in an
  on-chain certificate registry.

An upgrade without a certificate cannot land; the time to re-verify the next version is the
announcement window; and if the certificate of the next version says "this is again a gated
vault", the guarantee carries over to the version after it.

What is here: the contract (`contract/gated-vault`), a Lean model of it with the statement above as
a theorem (`lean/GatedUpgrade`), tests on the nearcore runtime (`harness/`), and a live example on
NEAR testnet (`TESTNET.md`). Each claim below is marked with what it rests on:

| Mark | Meaning |
|---|---|
| **proved** | a Lean 4.35 theorem about the model (`lean/`), no `sorry`, axioms within `propext`, `Quot.sound`, `Classical.choice` |
| **tested** | executed on the wasm with the nearcore 2.14.0 runtime in near-contract-sim: named scenarios, and random traces watched by a monitor |
| **testnet** | executed once on NEAR testnet, transaction ids in `TESTNET.md` |
| **read** | read from the source, not checked by execution |
| **assumed** | a hypothesis, listed under "Hypotheses" |

## Do X — see Y

| Do | Command | See |
|---|---|---|
| Read the statement | — | `lean/GatedUpgrade/Theorems.lean`, `gated_code_change` |
| Re-check the proofs | `cd lean && lake build && lake env lean Axioms.lean` | `evidence/axioms.txt` |
| Run the scenarios and the traces | `./check.sh` | `evidence/scenarios.json`, `evidence/traces.json` |
| Check that weakened gates are caught | `./check.sh --mutants` | `evidence/mutants.json` |
| Read the testnet example back | `python3 testnet/read.py vault.gated-upgrade.testnet` | the vault's code hash, keys, gate, roles, staged code; the registry's certificates |
| Compare the chain with `TESTNET.md` | `./check.sh --testnet` | every recorded transaction and the final state |
| Repeat everything | `./check.sh --mutants --testnet` | `evidence/check_run.txt` |

Needs: Linux x86-64, `elan` (Lean 4.35.0), `rustup` (Rust 1.95.0 for the harness, 1.86.0 with
`wasm32-unknown-unknown` for the vault), a C/C++ compiler, `cmake` and libclang (for nearcore's
RocksDB bindings; `scripts/env.local.sh.example`), `python3`; cargo-near 0.22 for rebuilding the
contracts and for the mutants. The harness is built against `near/near-contract-sim` at commit
`8e4b69b` (nearcore 2.14.0), locked in `harness/Cargo.lock`. `testnet/` needs node with
near-api-js (the one inside near-cli 4) for sending, and only Python for reading.

## The design, as built

```
 stager ──up_stage_code(code)──▶ vault        staged hash and staging timestamp = now + D are public
                                              (up_staged_code_hash, up_get_delay_status)
 attestor ──attest(hash, cert)──▶ registry    at any time before the deployment

 anyone ──deploy_certified()──▶ vault         panics unless code is staged and now ≥ staging timestamp
            vault ──get_valid_kind(hash, kind)──▶ registry
            vault ◀──────── answer ──────────────┘
            vault.on_certificates(hash)   #[private]
               panics unless the answer holds a certificate with: not revoked, code_hash = hash,
               kind = the accepted kind, attestor ∈ the accepted attestors
               then the plugin's up_deploy_code(hash, None):
                  panics unless the role check passes (predecessor = the vault itself),
                  now ≥ staging timestamp, and the code staged NOW has this hash
            vault ──[DeployContract(code), up_verify_state()]──▶ vault     the code changes here
```

- The upgrade path is the unchanged `Upgradable` plugin of near-plugins v0.5.1 (the version the
  upgrade-window kit (`../upgrade-window/`) models). The plugin's `up_deploy_code` needs the role `CodeDeployer`; `new`
  grants it to the contract's own account and to nobody else. The contract account is the only
  access-control super-admin and is meant to have no access keys.
- `deploy_certified()` and its callback `on_certificates(hash)` are the only code of the vault that
  reaches `up_deploy_code`.
- The registry account, the accepted kind and the accepted attestors are arguments of `new`, are
  stored in the contract state, and no method writes them. `gate()` shows them.

### What differs from the brief, and why

| | Change | Reason |
|---|---|---|
| 1 | No `DAO` role; one role per kind of method; `DurationManager` is held by nobody | With a role that may call everything, or a holder of `DurationManager`, the delay can be shortened first (the kit's shortcut 2). Here the staging duration is constant: `dur_run` (**proved**) |
| 2 | The deployment never carries an attached function call (`up_deploy_code(hash, None)`) | The kit lists "the attached call is chosen at deploy time and is not visible in advance" as a limit; the gate removes the choice |
| 3 | The callback deploys the hash that was *asked about*, not "whatever is staged now" | Otherwise code staged between the registry call and the callback would ride on another code's certificate. Mutant M8 is exactly that mistake and is caught |
| 4 | The callback checks every field of a certificate itself (`revoked`, `code_hash`, `kind`, `attestor`) | The proof then needs from the registry only that the answer is a part of what it holds. Mutants M1–M4 remove one check each and are caught |
| 5 | `new` is `#[private]`, does all of the setup in the deployment transaction, and refuses `D = 0`, itself as the registry, an empty kind, an empty attestor list | Nobody else can initialise the contract, and no second transaction by the contract account is needed: its key can be deleted at once |
| 6 | `deploy_certified` checks "staged, and the delay has passed" before asking the registry | Saves the caller's gas; the plugin's own checks in the callback stay the ones that count |
| 7 | The gate stores nothing between the call and the callback | Nothing can get stuck: after any failed step `deploy_certified` can simply be called again |

## What the contract guarantees, case by case

| Case | What happens | Rests on |
|---|---|---|
| Certified code, delay passed | anyone's `deploy_certified` installs it | **tested** (`certified_upgrade`), **testnet** (scenario 1), model example `certified_deployed` (**proved**) |
| No certificate; a certificate by an attestor the vault does not accept; of another kind; for another hash | the callback panics, no deploy batch, the code hash does not change | **proved** (`uncertified_never_installed`), **tested** (`uncertified_refused`), **testnet** (scenario 2) |
| `deploy_certified` before the delay | panics at once, the registry is not asked | **tested**, **testnet** (scenario 1) |
| Code re-staged between the registry call and the callback — another code | the callback's deploy call panics (`Deploy code too early` for the new code's own delay; `wrong hash` if that delay had passed): nothing is deployed | **proved** (the installed code is the one the registry was asked about), **tested** (`restaged_between_check_and_deploy`) |
| … the same code re-staged | its delay restarts; the callback panics: nothing is deployed | **tested** |
| … the staged code removed | the callback panics: nothing is deployed | **tested** |
| Code re-staged after the callback, before the deploy batch | the batch carries the bytes the callback read: the checked code is installed, the new one is merely staged | **proved** (model example `restaged_after_callback_installs_checked_code`), **tested** |
| Certificate revoked before the registry executes the call | not counted: refused | **proved**, **tested** (`revoked_certificate`) |
| Certificate revoked after the registry answered (one to two blocks before the code changes) | **the deployment goes through.** The guarantee is about the moment of the registry call | **tested** as a limit; cannot be closed on an asynchronous chain |
| The registry call fails (no such account, no code, out of gas) | the callback sees a failed result and panics | **tested** (`failed_steps`) |
| The callback fails (panic, out of gas) | no state is written, no batch is created; call again | **tested** (out of gas with 1 MB of staged code) |
| The deploy batch fails (certified bytes are not a contract, no `up_verify_state`, not enough balance for storage) | rolled back by the protocol, the old code stays | **tested** (bytes that are not wasm) |
| A stranger calls `on_certificates` directly | `Method on_certificates is private` | **tested** (7 accounts); and behind it the plugin's role check |
| `up_deploy_code` called directly, by any account including the stager and the attestors | `Insufficient permissions` | **proved** (`external_not_allowed`), **tested** (7 accounts, with and without an attached call; 5904 calls in the traces) |
| Somebody tries to obtain the deployer role, become an admin or a super-admin | every `acl_*` call returns `null`/`false` or panics; the permissions do not change | **proved** (`aclInv_run`), **tested** (77 calls) |
| Somebody tries to change the staging duration | `Insufficient permissions` | **proved** (`dur_run`), **tested** |
| After a certified upgrade to a build of the same source | the same gate is in force | **tested** (`gate_survives_upgrade`), **testnet** (scenario 2 runs on the upgraded code) |

**Who pays.** The caller of `deploy_certified` pays the gas of the whole chain of receipts and
attaches no deposit; unused gas is refunded. Measured on the simulator (**tested**): the whole
deployment of the 220 KB vault burns 43 Tgas (11 for `deploy_certified`, 1.5 for the registry, 13.5
for the callback, 15.5 for the batch); with 1 MB of staged code 165 Tgas. A call with too little gas
fails in its first receipt or in the callback and changes nothing. The cost grows with the code
size, so with the protocol's 300 Tgas per transaction there is a code size above which this gate
cannot deploy at all (by extrapolation about 1.8 MB; not tested above 1 MB). Staged code is stored
by the vault and its storage is paid from the vault's balance, as in the kit (its limit A5).

## The statement proved

`lean/GatedUpgrade/Theorems.lean`, theorem **`gated_code_change`**. In words:

> Start from a quiet state of the gated vault with staging duration `D` at block timestamp `t0`
> (nothing staged, no deploy batch in flight, no registry answer on its way; this is the state
> after `new`). Take any sequence of events with non-decreasing block timestamps: calls of the
> plugin's methods and of the `acl_*` methods by any accounts other than the contract account,
> `deploy_certified` by anyone, registry calls and callbacks that succeed or fail, deploy batches
> that succeed or fail, and arbitrary changes of the registry's content at any moment. If an
> event at timestamp `t` changes the code on the account to `new`, then
>
> 1. that event is a deploy batch that succeeded;
> 2. the batch was created by a successful callback `on_certificates` at some `tc ≤ t`, whose
>    plugin call `up_deploy_code(H new, None)` succeeded and read exactly `new`;
> 3. the answer that callback consumed was produced by a registry call for `H new` that the
>    registry executed at some `tq ≤ tc`, and **the registry's state at that moment held a
>    certificate with `code_hash = H new`, `kind` = the accepted kind, not revoked, and an
>    attestor from the accepted list**;
> 4. `new` was staged by a permitted `up_stage_code` at some `ts` with `ts + D ≤ tc` (saturating
>    at `u64::MAX`), and from that staging until the callback the view `up_staged_code_hash`
>    showed `H new` at every moment;
> 5. `t0 + D ≤ tc`.

`H` is the code hash (bs58 of sha256; a parameter of the model). Companion theorems:

| Theorem | Statement | Axioms |
|---|---|---|
| `gated_code_change` | the statement above | propext, Quot.sound, Classical.choice |
| `gated_no_deploy_before` | the same from any state with the access-control invariant, no batch in flight and no answer on its way (code may already be staged): items 1–3, and `safeUntil(plugin state, t0) ≤ tc ≤ t` with the kit's `safeUntil` | propext, Quot.sound |
| `uncertified_never_installed`, `uncertified_never_current` | if along a trace the registry never holds an accepted certificate for the hash `h`, no code change installs code with hash `h`, and the running code never has hash `h` | propext, Quot.sound (+ Classical.choice) |
| `aclInv_run`, `external_not_allowed`, `dur_run` | along any such trace only the contract account is super-admin, admin, code deployer or duration manager; a call of `up_deploy_code` or of a duration method by any other account is refused; the staging duration never changes | propext (+ Quot.sound, Classical.choice) |
| `init_fresh` | the state after `new` is a quiet state | propext |
| `grun_sys`, `projTrace_split` | every run of the gated vault projects onto a run of the kit's plugin model, so the kit's theorems (`deploy_origin`, `W3_no_deploy_before`, …) apply | propext |

The plugin part of the model is the kit's `UpgradeWindow` model, copied unchanged
(`lean/UPGRADE_WINDOW_SHA256`); the gated vault's step function calls the kit's `Sys.step`.
`lean/GatedUpgrade/Examples.lean` runs the model on concrete data so that no statement is true
only vacuously: a run in which certified code is deployed at exactly `t + D`, with
`gated_code_change` applied to it; `deploy_certified` one nanosecond early does nothing; an
uncertified run, with `uncertified_never_current` applied; certificates of another attestor, kind
or hash; a certificate revoked before the registry call; the three re-staging cases; a direct
deploy by the stager and by a stranger who first tries `acl_grant_role`. Two examples state limits:
`revoked_after_call_still_deployed`, and `contract_key_bypasses_gate` (a receipt with the contract
account as predecessor deploys uncertified code — hypothesis H1 is necessary).

### Hypotheses

| | Hypothesis | Where it enters | How it is supported |
|---|---|---|---|
| H1 | **No receipt calling a plugin or `acl_*` method has the contract account as predecessor.** On NEAR such a receipt comes from a transaction signed with an access key of the account, or from the contract's own code | `External` in every theorem | the account has no access keys (**testnet**: read from the chain); the vault's code calls itself only in the callback and in the deploy batch (**read**); the simulator's "what if the account had a key" run deploys uncertified code (**tested**, `control_contract_key`) |
| H2 | **The code on the account changes only when a deploy batch created by `up_deploy_code` executes** (the kit's A3): no access keys, no other method that deploys, no global contract by account id, the account is not deleted and re-created | built into the model | no access keys (**testnet**); no other deploy action in the source (**read**); in the traces every change of the code hash coincides with such a batch (**tested**) |
| H3 | **The callback receives the result of the registry call it was created with**, once; a receipt runs entirely or has no effect; block timestamps do not decrease | built into the model | protocol rules (**assumed**) |
| H4 | **The registry's answer to `get_valid_kind` consists of certificates it holds at that moment.** The proof uses nothing else about the registry; who attests and who revokes is arbitrary | `Reg.answer` | the registry account runs the pinned registry wasm — the bytes recorded for the mainnet registry — and has no access keys (**testnet**); in the traces every answer equals the monitor's own record of attestations and revocations (**tested**) |
| H5 | **The model describes the wasm.** It is a transcription by hand of `contract/gated-vault/src/lib.rs` and of the plugin | everything | **tested**, not proved: scenarios, the monitor (which re-implements the model's rule for every step), mutants; the kit's conformance run covers the plugin under another host contract |
| H6 | **After a code change, the installed code is again the modelled contract** — otherwise the theorem speaks about the first change only | every later change | what the certificate of the next version has to establish; here v2 and v3 are builds of the same source that differ in `version()` |
| H7 | The kit's A2 and A7: only the plugin's methods write the plugin's storage slots (`new` writes the staging duration through the plugin's own initialiser); overflow checks are on (`overflow-checks = true`) | the plugin model | **read** |

Outside the model: gas, storage staking, JSON decoding, collisions of the hash. The statements
are about the hash of the installed code.

## Tests

`./check.sh --mutants --testnet` took 7 min 8 s on the recorded run (32 cores, toolchains and the
harness already built); the mutant builds are most of it:

| Step | Result of the recorded run (`evidence/check_run.txt`) |
|---|---|
| Lean | builds; 37 statements listed in `lean/Axioms.lean`, axioms within the three allowed |
| Plugin model | `lean/UpgradeWindow*` has the hashes of the kit's files |
| Contracts | the four wasm files have the pinned hashes (`contract/WASM_SHA256`); a rebuild from source with cargo-near gives the same bytes; the registry wasm is the one recorded for `registry.exitproof.near` (`a8984200…`), built from an unchanged copy of its source |
| Scenarios | **10 scenarios, 82 checks, all hold** (`evidence/scenarios.json`, every receipt with its outcome) |
| Traces | **2000 random traces, 281 198 receipts, 117 568 blocks: 0 violations** (`evidence/traces.json`) |
| Mutants | control passes and reproduces the pinned bytes; **11 of 11 mutants detected** (`evidence/mutants.json`) |
| Testnet | all 17 recorded transactions and 14 statements about the final state read back as recorded (`testnet/verify.py`) |

**Scenarios** (`harness/src/main.rs`, `gu-test scenarios`): `certified_upgrade`,
`uncertified_refused`, `restaged_between_check_and_deploy`, `revoked_certificate`,
`callback_checks_every_field` (the callback delivered with forged answers the registry would never
give: revoked, other hash, other kind, other attestor, empty, not a list, failed), `no_way_around_the_gate`
(direct callback, direct deploy, 77 `acl_*` calls, duration methods, staging by non-stagers, a
second `new`), `init`, `failed_steps` (gas from 5 to 300 Tgas, 1 MB of staged code, a missing
registry, a registry without code, certified bytes that are no contract), `gate_survives_upgrade`,
and `control_contract_key` (a limit, see H1).

**Traces and the monitor** (`gu-test traces`, `scripts/traces.sh`). Random operations by six
accounts sharing blocks: 17 595 stagings submitted (three builds, a stub, bytes that are no
contract, empty input), 17 817 attestations (three attestors, three kinds, five hashes), 7 828
revocations, 27 447 `deploy_certified` with 30 to 300 Tgas, 6 007 direct `up_deploy_code`, 3 951
direct `on_certificates`, duration and `acl_*` calls, and clock jumps to one nanosecond before,
exactly at and after the staging timestamp. The monitor reads the receipts in execution order and
the vault's state after every block, keeps its own record of the registry, and checks on every
trace: the statement of the theorem at every change of the code hash (822 changes; 2 392
deployments started, each with an accepted certificate in the answer and the staged code at least
`D` old); the registry's answers against its own record (11 061 registry calls); the model's rule
for every `deploy_certified` and every callback, including the panic text (8 633 callbacks refused:
7 874 no valid certificate, 625 too early, 89 nothing staged, 45 wrong hash); and that the
permissions, the gate and the staging duration never change. Once a certified stub without methods
has been installed, calls on it fail with `MethodNotFound`; the monitor then keeps checking only
the code hash (H6).

**Mutants** (`scripts/mutants.py`): one changed line of the vault's source each, v1 rebuilt, the
scenarios and 300 traces run against it.

| Mutant | Changed line | Scenario checks failed | Trace violations |
|---|---|---|---|
| M0 control | none | 0 | 0 |
| M1 | the attestor of a certificate is not checked | 5 | 137 |
| M2 | a revoked certificate counts | 2 | 0 |
| M3 | the kind of a certificate is not checked | 2 | 0 |
| M4 | the hash of a certificate is not checked | 2 | 0 |
| M5 | `on_certificates` is not `#[private]` | 1 | 502 |
| M6 | the plugin's deploy method also accepts the stagers' role | 2 | 226 |
| M7 | `deploy_certified` asks the registry before the delay has passed | 1 | 662 |
| M8 | the callback deploys whatever is staged at callback time | 3 | 9 |
| M9 | `new` is not `#[private]` | 1 | 0 |
| M10 | `new` grants the deployer role to the stagers as well | 7 | 16 752 |
| M11 | any certificate in the answer counts | 8 | 137 |

M2–M4 change nothing as long as the registry filters its answer correctly: only the scenario with
forged answers sees them. With M5 a direct call is still refused, by the plugin's role check instead
of `#[private]`; the tests see the different panic.

## Testnet

`TESTNET.md`: `vault.gated-upgrade.testnet` (no access keys, `D` = 3 minutes, a deposit of 0.05
NEAR) and `registry.gated-upgrade.testnet` (the registry wasm, no access keys). Scenario 1: the v2
build is staged, attested during the window, refused before the delay, deployed after it by an
account without any role; the account's code hash changes. Scenario 2, on the upgraded code: the
v3 build is staged without a certificate; `deploy_certified` and a direct `up_deploy_code` by the
stager are refused; the code hash does not change. `./check.sh --testnet` reads all of it back.
`gated-quiet-vault.testnet` is the same vault code (v1) with a seven-day delay and nothing staged: the scanner gives
it stage 1, "certified upgrades only" (`TESTNET.md`, "A second vault, with nothing staged").

## Limits

- **A certificate is a statement by an attestor, not a proof checked on chain.** The registry
  records who attested what; the gate checks that an accepted attestor stands behind the hash.
  What the certificate has to say for the chain of guarantees to continue (H6) is not enforced.
- **Who holds the keys.** An accepted attestor together with a stager can install any code after
  `D`. The delay is what protects users then. Every run of the gated vault projects onto a run of
  the kit's plugin model (`grun_sys`, **proved**), so the kit's W5 statements about the exit window
  hold for the projected run; they were not restated for the gated vault here, and their
  corollaries about exits keep their own premises. If one party holds both roles the gate adds
  nothing to the delay.
- **Revocation is not instant** (see the table): a revocation counts for every registry call
  executed after it.
- **Liveness is not guaranteed.** The stager can replace or remove staged code at any time (which
  restarts the delay); a registry attestor could attest very many certificates for one hash and
  make the answer too large or too dear to read (not tested); a code too large for 300 Tgas cannot
  be deployed through the gate; a stager who renounces its role ends all upgrades. None of these
  installs anything.
- **The accepted lists are fixed.** Replacing an attestor, the registry or the delay needs an
  upgrade through the gate itself.
- **The registry's owner** can change who may attest in the registry, not whom the vault accepts.
  The registry's code is fixed only as long as its account has no access keys: check both accounts.
- **What the scanner says about a gated vault.** `tools/exitproof.py` of this repository
  reads the gate from the contract's `gate()` view. With nothing staged, or with staged code still
  inside its delay, the vault is at stage 1 and the report says "certified upgrades only". With
  staged code past its delay the vault is at stage 0, whether or not the code has a certificate:
  uncertified code is deployed the moment one accepted attestor certifies it, so no time bound
  holds. The testnet example is in that state (scenario 2 leaves uncertified code staged).
- **The testnet example is one run of each scenario.** The certificate attested there says so.
- H1–H7 above.

## Files

- `contract/gated-vault/` (source, `Cargo.lock`, toolchain); `contract/registry/` (an unchanged
  copy of the registry source, `contract/REGISTRY_SOURCE_SHA256`); `contract/out/` (the four wasm
  files), `contract/WASM_SHA256`, `contract/REGISTRY_MAINNET_SHA256`; `scripts/build-contract.sh`
- `lean/GatedUpgrade/Model.lean`, `Theorems.lean`, `Examples.lean`; `lean/Axioms.lean`;
  `lean/UpgradeWindow/` (the kit's plugin model and theorems, unchanged), `lean/UPGRADE_WINDOW_SHA256`
- `harness/` (`gu-test`: `scenarios`, `traces`, `info`); `scripts/traces.sh`, `scripts/mutants.py`,
  `scripts/env.sh`, `scripts/bundle_hash.py`; `check.sh`
- `testnet/` (`setup.sh`, `scenario1.sh`, `scenario2.sh`, `tx.js`, `mkkey.py`, `make_attest.py`,
  `wait_staging.py`, `read.py`, `verify.py`; the record `tx.jsonl`, the attested certificate
  `attest_v2.json` with the bundle listing, the states read before and after each scenario);
  `TESTNET.md`
- `evidence/`: `axioms.txt`, `scenarios.json`, `traces.json`, `mutants.json`, `check_run.txt`
- `NOTICE`, `PLUGIN_PIN.json` (the plugin version, as in the kit)
- Build products and working output (`harness/target/`, `lean/.lake/`, `runs/`) are not part of the kit.
