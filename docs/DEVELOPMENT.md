# Developing Exit Proof

How the parts fit, what must not be edited, and how to make the usual changes. Read `../README.md` first.

## The parts and how data flows

```
 NEAR RPC (read-only) ──► tools/exitproof.py ──► exit stage + evidence ──► CLI text / --json
   account, keys, wasm,      scan → verdict → stage        │                tools/mcp_server.py   (agents)
   views, NearBlocks                  ▲                    │                tools/agent_demo.py   (reference agent)
                                      │                    └──────────────► tools/census_*.py     (aggregates in docs/, evidence/)
 registry.exitproof.near ─────────────┘
   certificates keyed by code hash            written by registry/attest.py from registry/certificates/*.json
                                              with the bundle hash of a proof directory (tools/bundle_hash.py)

 proof directories (each self-contained, each with check.sh):
   pool-proof/  wnear-proof/  token-standard/  upgrade-window/   (attested: frozen)
   intents-proof/  gated-upgrade/  token-monitors/  pool-mutants/
   Lean model + theorems ── conformance harness (the exact wasm on the nearcore runtime, random traces) ── evidence
```

| Path | Role | Entry points |
|---|---|---|
| `tools/exitproof.py` | scanner: `scan` reads the chain, `verdict` classifies code-change / fund-moving / pausing powers, `stage` applies `docs/STAGES.md`, `public_view` drops holder identities | `python3 tools/exitproof.py <account> [--json] [--fast] [--no-history] [--network testnet]` |
| `tools/rpc.py` | JSON-RPC client: pacing, `RpcUnavailable`; a call starts at the endpoint that answered last, waits (doubling) after a "too many requests" answer, leaves a silent endpoint after 10 s | env `EXITPROOF_RPC`, `EXITPROOF_PACE`, `EXITPROOF_NETWORK` |
| `tools/intents_backing.py` | the live ledger of `intents.near` against what it holds, per fungible token, with the census verdict of each token; output `evidence/intents-live-backing.json` | `python3 tools/intents_backing.py --table` (saved reading); without arguments it reads the chain again (about 40 minutes) |
| `tools/proofs.json` | proofs known to the scanner by code hash; `kind` other than `exit` never raises a stage, `"attested": false` is printed as "not attested on chain" | read by `exitproof.py` |
| `tools/token_check.py` | does a token behave as the proved NEP-141 standard: lookup of its code hash in `evidence/token-census.json`, live read of a transfer tax, extensions, exit stage; counts the certificates of `evidence/token-certificates/`, shows a certificate brought by the caller as a claim | `python3 tools/token_check.py <token> [--json]` |
| `tools/watch.py` | what changed since the last run for a set of accounts: code hash, stage, keys, upgrade delay, staged code, certificates, token tax | `python3 tools/watch.py <accounts> --state file.json`; exit status 1 on a change |
| `web/` | the page: `worker.js` runs `exitproof.py` and `token_check.py` unchanged on Pyodide and replaces only `urllib.request.urlopen` with a blocking request of the worker; `app.js` draws the answers and reads the numbers from the evidence files; `files.json` lists the files the worker copies (checked by the self-test). `styles.css` and `page.css` are the shared design of formalized.si, `exit.css` is this page's own | `python3 -m http.server 8000`, open `/web/` |
| `tools/mcp_server.py`, `agent_demo.py`, `exit_plan.py` | what agents and users call | see the docstring of each file |
| `tools/census_validators.py`, `census_contracts.py`, `census_table.py`, `pools_live.py`, `pools_origin.py` | the numbers in `docs/CENSUS.md` and `README.md`; outputs go to `evidence/`. `pools_origin.py` reads the deployment history of every pool of the proved code, the origin part of stage 2 | see the docstring of each file |
| `check-all.sh` | one command for the repository: numbers check, self-test, and with `--proofs` the `check.sh` of every proof directory (the attested ones in scratch copies) | `./check-all.sh [--proofs] [--offline]` |
| `tools/numbers_check.py` | the numbers the documents quote from runs, against the evidence files: whole numbers that stand together in one paragraph or table row, every mention of the most quoted claims, and that the evidence behind the numbers of `intents-proof/` was made from its present sources. It does not read the meaning of a sentence; add a fact here when a document starts quoting a new number | `python3 tools/numbers_check.py` |
| `intents-proof/scripts/source_hash.py` | one hash for the sources that decide the results in `intents-proof/evidence/`; `evidence/PROVENANCE.json` records the hash each evidence file was made from | `--stamp <files>` right after the run that wrote them; `--check` lists the state of every file |
| `tools/deploy_history.py` | every code deployment of an account, from the indexer's receipts with a DEPLOY_CONTRACT action; for a proof entry that names more than one deployment (`origin.<account>.full_history` in `tools/proofs.json`) | `python3 tools/deploy_history.py wrap.near > evidence/wrap-near-deployments.json` (reads NearBlocks API v1 receipts, switched off on mainnet on 2026-11-22; API v3 has no filter by action) |
| `pool-mutants/` | one-line changes of the pool model against the traces of `pool-proof/`, in a copy of it | `pool-mutants/run.sh [work dir]` |
| `tools/name_audit.py` | audit of the scanner's method-name rules: for codes with no code-change path by names, the exported names that look related; a hit is a hole in the rules | `python3 tools/name_audit.py <directory of wasm files>` |
| `tools/selftest.py` | regression check, run before every commit | `python3 tools/selftest.py` (`--offline` skips the RPC part) |
| `tools/stage1_demo.sh`, `stage_code.js` | deploy the stage-1 examples on testnet | `PARENT=<testnet account> tools/stage1_demo.sh` |
| `registry/` | the registry contract (near-sdk 5.30.1), certificates as files, `attest.py`, `deploy.sh` | `cargo test` in `registry/`; `registry/attest.py --dry-run` |
| `token-monitors/` | certification kit for a token team: trace generator, 14 model-free monitors, config format, certificate, self-check; its certificates are read by `tools/token_check.py` | `token-monitors/check.sh`, `token-monitors/certify.sh <wasm> <config>` |
| `gated-upgrade/` | a vault whose upgrades need a certificate in the registry; not attested | `gated-upgrade/check.sh [--mutants] [--testnet]` |
| `intents-proof/` | the token ledger of NEAR Intents; not attested, so it can still be edited | `intents-proof/check.sh [--mutants] [--rebuild] [--tla]`, `intents-proof/scripts/verify_upgrade.sh <commit>` |
| `pool-proof/`, `wnear-proof/`, `token-standard/`, `upgrade-window/` | one proof family each | `<dir>/check.sh` |
| `docs/` | stage rubric, background and sources, design decisions, census, review, demo script | — |
| `CLAIMS.md`, `EVIDENCE.md` | every claim with its evidence level; every on-chain transaction | — |

Local-only directories, ignored by git: `codes/` (cache of downloaded contract wasm), `internal/` (working notes),
`runs/`, `mutants/`, `plugin/` and build directories inside the proof directories.

## Frozen directories

`pool-proof/`, `wnear-proof/`, `token-standard/` and `upgrade-window/` are **attested on chain**: the registry stores a
hash of each directory's content (`tools/bundle_hash.py`). Any edit, even of a README, changes the hash, and the
certificate no longer matches the checkout. `tools/selftest.py` fails when that happens.

Running a directory's `check.sh` also changes the hash of the working tree: the checks rewrite their run logs
(timings, build paths) and leave new output files. Nothing attested has been edited in that case;
`python3 tools/bundle_hash.py <dir> --git` hashes the committed content, and
`git checkout -- <dir> && git clean -fdq <dir>` restores the directory. A cleaner fix — moving all run output out
of the hashed files — needs new attestations and is listed in `ROADMAP.md`.

To change one of them: make the change, run its `check.sh` to exit code 0, attest again
(`NETWORK=mainnet REGISTRY=registry.exitproof.near ATTESTOR=<attestor> python3 registry/attest.py <name>`, about
0.02–0.03 NEAR of storage), then update `ATTESTED` in `tools/selftest.py` and the table in `EVIDENCE.md`. The registry is
append-only: the older certificate stays; revoke it with `revoke(index, reason)` if it should no longer be shown.

The registry contract itself has no access keys and no upgrade method. Its certificate kinds are fixed in the deployed
code (`exit`, `token-standard`, `upgrade-window`); a new kind means a new registry deployment and a change of
`REGISTRY` in `tools/exitproof.py`.

## Rules the code keeps

- **Evidence levels.** A claim is `proved` (Lean theorem about a model), `tested` (model against the exact wasm on the
  nearcore runtime), `read` (chain state or a contract's own view) or `heuristic` (method and role names). Never present
  a lower level as a higher one; `CLAIMS.md` is the reference.
- **Every number in `README.md` and `docs/` comes from a file in `evidence/` or a proof directory.** Change the
  script and re-run it; do not edit numbers by hand. Two kinds of file were not produced by a script of this
  repository: the token census (`evidence/token-census.json`; its runner and per-family configurations are not
  included, `token-monitors/` re-runs one token's code with the same kind of monitors) and the rebuild attempts of
  the 2020 pool code (`docs/REPRO.md`).
- **Reports show how strongly a power is guarded, never who holds it.** `public_view` and the census outputs carry
  counts and kinds only; error messages do not name controller accounts.
- **Read-only.** Nothing in `tools/` signs or sends a transaction, except `stage1_demo.sh` (testnet) which says so.
- **No dependencies** for `tools/*.py` beyond the Python standard library.

## Usual changes

**A scanner rule** (a new upgrade method name, a role, a plugin). Edit the patterns at the top of
`tools/exitproof.py` (`CODE_RE`, `NOT_SELF_CODE_RE`, `MIGRATION_RE`, `FUNDS_RE`, `FREEZE_RE`, `ROLE_CLASS`), add the
name to `NAMES` in `tools/selftest.py` with the class you expect, run `tools/selftest.py`. If the rule can move a
contract between stages, re-run the contracts census and update `docs/CENSUS.md` from its output:
`python3 tools/census_contracts.py tools/contracts.txt evidence/contracts-census.json`, then
`python3 tools/census_table.py evidence/contracts-census.json`.

**A stage rule.** `stage()` in `tools/exitproof.py` and the table in `docs/STAGES.md` must say the same thing; add an
account that shows the rule to `STAGES` in `tools/selftest.py`.

**A new proof family** (another contract or library). Copy the shape of the smallest one, `upgrade-window/`:
`lean/` (model, theorems, `Axioms.lean` printing the axioms of every theorem, an executable model), `harness/` (trace
generator on `near-contract-sim`), `scripts/` (comparison of wasm and model, mutants), committed wasm with pinned
hashes, `check.sh` that exits 0 only when everything holds, `README.md` with the exact statements and limits. Then add
`registry/certificates/<name>.json`, run `registry/attest.py <name> --dry-run`, attest, and add the directory to
`ATTESTED` in `tools/selftest.py`, to `CLAIMS.md` and to `EVIDENCE.md`. What made the existing proofs credible, in order:
a model that is executable, conformance on the exact deployed bytes, mutants that the comparison must detect,
non-vacuity examples, an independent kernel check (`docs/REVIEW.md`).

**Another network or RPC.** `rpc.use_network(name)` switches all later calls; `EXITPROOF_RPC` overrides the endpoint
list. The registry is always read from mainnet (`EXITPROOF_REGISTRY_RPC`), because certificates are keyed by code hash.

## RPC facts worth knowing

- `view_access_key_list` answers `TOO_MANY_ACCESS_KEYS` for accounts with more than 100 keys; it must be paginated
  with `limit` and `after_key` (the previous page's `last_key`). `keys()` in `tools/exitproof.py` does this.
- Public endpoints rate-limit; a transient failure raises `RpcUnavailable` and is never read as "account not found".
  For long runs set `EXITPROOF_PACE=0.4`.
- The deployment history comes from NearBlocks (`INDEXER` in `tools/exitproof.py`, `EXITPROOF_INDEXER` sets
  another base): API v3 `/v3/accounts/<id>/contract/deployments`, with v1 as a fallback until it is switched off
  (testnet v1 answers 410; mainnet v1 stops on 2026-11-22). The list holds the first and the latest deployment
  only. The public API limits requests per minute; a scan retries with a growing pause.
- A wasm read from the RPC is kept in `codes/` under its code hash only after its sha256 has been checked against
  that hash; a cached file is checked again when it is used.
- A contract may use a global contract (by hash or by account id); `effective_code()` resolves it. Code referenced
  by account id follows whatever that account deploys, so it counts as a code-change path.
- An argument of a function call can be larger than the 128 KB limit of one command-line argument
  (`up_stage_code` takes a whole wasm): `tools/stage_code.js` sends it through near-api-js.

## Toolchains

Python 3.10+ for `tools/`. For the proof directories: Lean 4.35.0 (through `elan`, pinned in each `lean-toolchain`),
Rust (pinned in each `rust-toolchain.toml`), cargo-near 0.22 for contract builds, a C/C++ compiler, cmake and libclang
for the nearcore runtime. Each `check.sh` states what it needs and how long it takes on a clean machine.
