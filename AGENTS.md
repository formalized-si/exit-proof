# Checking this repository

This file is for automated reviewers and coding agents. It makes no claim of its own. It lists each check, the
tools that the check needs, the time that it takes and the output to expect. The claims are in
[README.md](README.md) and, one by one with their level of evidence, in [CLAIMS.md](CLAIMS.md).

## Start here

```sh
./check-all.sh
```

The command needs Python 3.10 or newer and nothing else, and takes one to three minutes. It compares the numbers
that the documents quote with the evidence files, then runs the self-test: the hashes of the attested
directories, the stage rules, the MCP server, and the stages and token verdicts of real accounts read from NEAR
mainnet and testnet. A run that passes prints three lines that end with `facts agree`, `checks passed` and
`RESULT: PASS   (logs in runs/all/)`, and has no `FAIL` line.

Without a network, `./check-all.sh --offline` runs the part that reads no chain, in a few seconds.

## Where things are

| Path | Contents |
|---|---|
| `tools/exitproof.py` | The scanner: the exit stage of an account and the evidence behind it. `stage()` holds the rules, `origin()` the origin rule of stage 2 |
| `tools/token_check.py`, `tools/watch.py`, `tools/exit_plan.py`, `tools/agent_demo.py`, `tools/mcp_server.py` | What users and agents call. Each docstring states the usage and the exit statuses |
| `tools/proofs.json` | The proofs the scanner knows, by code hash, with their assumptions |
| `tools/numbers_check.py`, `tools/selftest.py` | The two checks behind `./check-all.sh` |
| `tools/deploy_history.py` | The full list of an account's code deployments, read once for a proof that names more than one (`evidence/wrap-near-deployments.json`) |
| `pool-proof/`, `wnear-proof/`, `token-standard/`, `upgrade-window/` | One proof each: Lean model and theorems, a harness on the deployed wasm, evidence, `check.sh`. **Frozen**: the mainnet registry pins a hash of each directory |
| `intents-proof/` | The token ledger of NEAR Intents: Lean, harness, TLA+, the upgrade check, `check.sh` |
| `gated-upgrade/` | A vault that upgrades only to certified code: contract, Lean theorem, tests, testnet records |
| `pool-mutants/` | One-line changes of the pool model replayed against the pool's traces, run in a copy of `pool-proof/` |
| `token-monitors/` | A kit that certifies a token wasm with model-free monitors |
| `web/` | The page. `worker.js` loads Python for the browser and runs `tools/exitproof.py` and `tools/token_check.py` as they are; `files.json` lists what it copies |
| `registry/` | The registry contract deployed as `registry.exitproof.near`, and the certificates as files |
| `evidence/` | Records of runs and readings that the documents quote |
| `docs/` | The stage rules, the census, the design decisions, the review, the roadmap |

## What to run

| Command | Needs | Time | Network | A run that passes ends with |
|---|---|---|---|---|
| `./check-all.sh` | Python 3.10+ | 1 to 3 min | read-only RPC to NEAR mainnet and testnet, one indexer | `RESULT: PASS   (logs in runs/all/)` |
| `./check-all.sh --offline` | Python 3.10+ | seconds | none | `RESULT: PASS   (logs in runs/all/)` |
| `python3 tools/numbers_check.py` | Python 3.10+ | under 1 s | none | `N/N facts agree`, the two numbers equal |
| `python3 tools/selftest.py` | Python 3.10+ | 1 to 3 min | as `./check-all.sh` | `N/N checks passed`, the two numbers equal |
| `python3 -m http.server 8000`, then open `http://localhost:8000/web/` | Python 3, a browser | the first answer takes about 5 s, later ones 1 to 3 s | the browser fetches Python for the browser (about 10 MB) from a CDN, and reads public RPC | the card shows a stage with its reasons, for example `2 PROVEN EXIT` for `astro-stakers.poolv1.near` |
| `./check-all.sh --proofs` | Linux x86-64, `elan`, `rustup`, a C/C++ compiler, `cmake`, libclang, `java` | 70 min with nothing built | crates and toolchains, once; read-only RPC | `RESULT: PASS   (logs in runs/all/)` after nine `PASS` lines |
| `pool-proof/check.sh` | as above without `java` | 11 min with nothing built, then 2 to 5 | crates, once | `RESULT: EXACT` |
| `pool-mutants/run.sh` | as `pool-proof/check.sh` | that check plus about a minute per change | crates, once | `control EXACT: 1; mutants noticed: 8 of 8` |
| `wnear-proof/check.sh` | the same | under 1 min once the simulator is built | none | `RESULT: EXACT` |
| `token-standard/check.sh` | the same | under 1 min once built | none | `RESULT: PASS` |
| `upgrade-window/check.sh` | the same | 3 min | git clone of near-plugins v0.5.1, once | `RESULT: PASS` |
| `intents-proof/check.sh --mutants --tla` | the same, and `java` | 38 min with nothing built, 26 once built | the TLC jar, once | `RESULT: PASS`; before it `mutants: 121; detected: 114; equivalent: 7; not detected or failed: 0 []; control: PASS` |
| `intents-proof/check.sh --rebuild` | `docker`, cargo-near 0.22 | not timed in the last run | the source and a docker image | `RESULT: BYTE-IDENTICAL` |
| `gated-upgrade/check.sh --testnet` | as `pool-proof` | 2 min once built | read-only RPC to testnet | `RESULT: PASS` |
| `token-monitors/check.sh` | the same | 13 min | crates, once; one read-only `view_code` from mainnet | `RESULT: PASS` |
| The other mutant runs: `wnear-proof/check.sh --all`, `token-standard/check.sh --all`, `upgrade-window/check.sh --mutants`, `gated-upgrade/check.sh --mutants`, `pool-mutants/run.sh` | the same | minutes each once built | as above | the mutant counts the README quotes (8/8, 10/10, 12/12, 11/11, 8 of 8) |

The times of the long checks are those of one run of `./check-all.sh --proofs` on a fresh copy, on a shared
32-core machine under load, on 13 November 2026. The four frozen directories are checked in scratch copies under
`runs/all/`, because a check writes run logs into its directory.

## A statement, and the line that supports it

| Statement of the README | Command | Look for |
|---|---|---|
| A pool of the proved code is at stage 2 | `python3 tools/exitproof.py astro-stakers.poolv1.near` | the second line starts with `EXIT STAGE 2 — PROVEN EXIT` and names one code deployment |
| A token whose code can change with no delay is at stage 0 | `python3 tools/exitproof.py token.sweat` | `EXIT STAGE 0 — KEYHOLDER TRUST: upgrade plugin with no exit window` |
| An account that only has the proved code hash is not at stage 2 | `python3 tools/selftest.py --offline` | `ok   stage 2 needs the origin of the account's state` and `ok   stage 2 needs an account with no access key at all` |
| Stage 1 is not given on names alone, on views that did not answer, a past staging timestamp or a gate that is not the proved one | `python3 tools/selftest.py --offline` | `ok   stage 1 needs the plugin established` |
| A token whose owner can freeze or destroy a holder's balance is not a pass | `python3 tools/token_check.py usdt.tether-token.near --json` | `"behaves_as_standard_now": null` and `holder_balance_powers` |
| The pool replay notices a wrong model | `python3 tools/numbers_check.py` | `ok   pool replay: the control agrees and every model change is noticed` |
| The 19 code hashes of `intents.near` | `intents-proof/evidence/intents-code-history.json` | its `check_one_row` command, at any `from_height` |
| The share of stake by stage | `python3 tools/numbers_check.py` | `ok   stake by stage [evidence/stake-by-stage.json] in README.md` |
| The registry holds the four certificates, and they pin this checkout | `python3 tools/selftest.py` | four lines `ok   registry certificate for <directory>/ pins this checkout's bundle hash` |
| A certificate as stored on chain | `python3 tools/registry_get.py J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY` | JSON with `"kind": "exit"` and `artifact_sha256` |
| The statements of the Intents proof and their axioms | `cat intents-proof/evidence/axioms.txt` | one line per statement, axioms within `propext`, `Quot.sound`, `Classical.choice` |
| Every receipt of the deployed wasm agrees with the model | `python3 -m json.tool intents-proof/evidence/conformance.json` | `"disagree": 0` in every part |
| The replay notices one-line changes of the model | `python3 tools/numbers_check.py` | the lines that start `ok   model changes` |
| The evidence of the Intents proof was made from the present sources | `python3 intents-proof/scripts/source_hash.py --check` | `present sources`, or a note for a dated record |
| A token with a transfer tax is reported as deviating | `python3 tools/token_check.py batman-4.nearlytrade.near` | `TOKEN CHECK: DEVIATES FROM NEP-141` |
| A hand-edited token certificate is refused | `python3 tools/selftest.py --offline` | `ok   a token certificate edited by hand is found inconsistent` |
| A gated vault refuses uncertified code | `gated-upgrade/check.sh --testnet`, or read `gated-upgrade/TESTNET.md` | `RESULT: PASS` |

## Before a change

[CONTRIBUTING.md](CONTRIBUTING.md) has the rules. The two that a tool most often breaks: do not edit a file in
`pool-proof/`, `wnear-proof/`, `token-standard/` or `upgrade-window/`, and do not edit a record under an
`evidence/` directory by hand.

The docstring of each tool lists its exit statuses. None of them exits with 0 when the chain could not be read,
and none turns an unread chain into a verdict.
