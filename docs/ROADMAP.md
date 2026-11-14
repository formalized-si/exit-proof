# Status and next steps (2026-11-14)

## What works today

| Part | State |
|---|---|
| Exit theorems for the core staking pool (86.2% of all NEAR stake) and wNEAR | proved in Lean, conformance on the deployed bytes, independently reviewed (`REVIEW.md`), attested on mainnet; the pool replay notices 8 of 8 one-line changes of its model (`pool-mutants/`) |
| Token standard `near-contract-standards` 5.29.0 | proved; a reference token certified against the exact model; `certify-token.sh` for other builds on this library version; four tokens taken from mainnet certified with the model-free monitors of `token-monitors/`; not yet independently reviewed |
| Upgrade window of `near-plugins` v0.5.1 | proved (34 theorems), conformance and mutants, attested; live stage-1 examples on testnet |
| Scanner and exit stages | works on any mainnet or testnet account; 28 of 28 large contracts scanned; verdicts below stage 2 rest partly on names and self-reported views |
| Registry `registry.exitproof.near` | keyless, 4 certificates, one attestor |
| The page (`web/`) | the scanner and the token check run in the browser, unchanged, on Python compiled to WebAssembly; the numbers of the page are read from the evidence files; hosted at `formalized-si.github.io/exit-proof`, with links to an answer (`#check=<account>`) |
| Agent interface | MCP stdio server with three tools (`exit_check`, `exit_plan`, `token_check`), reference agent (dry run) |
| Intents Proof (`intents-proof/`) | ledger backing proved for a standard token and for wNEAR; who can lower a balance, with the authorisation of each way, the source of keys, role holders and refunds (standard token); byte-identical rebuild; replay, mutants, TLA+, blind re-statement, upgrade gate; `./check.sh --mutants --tla` passes on a clean copy |
| Verified upgrades (`gated-upgrade/`) | a vault that upgrades only to certified code: theorem, tests, live testnet example; the scanner reports the gate |
| Token census and token check | 86 code hashes: 371 of the 395 fungible tokens of the Intents ledger and 163 of 217 exchange-listed tokens have a verdict from runs of the deployed code; `tools/token_check.py`, MCP tool |
| Regression check | `tools/selftest.py`, 51 checks; `tools/numbers_check.py` checks the numbers the documents quote against the evidence files (by its rules: whole numbers that stand together, every mention of the most quoted claims, the sources each evidence file was made from) |

## Known gaps

1. **The page answers for one account at a time.** `web/` runs the scanner in the browser, hosted on the
   repository's pages. It has no list of contracts with their stages, and the first answer waits for about 10 MB
   of Python to load (the page starts loading it when a visitor comes near a form).
2. **The exact token model covers two library versions.** `token-standard/` is exact for `near-contract-standards`
   5.29.0 and `wnear-proof/` for 3.1.0. The census has 86 code hashes (84 held by the Intents ledger), 71 of them run; their verdicts come from runs of the deployed code with model-free monitors (`evidence/token-census.json`),
   which is weaker than a comparison with a proved model of their own library version.
3. **One attestor, one key.** A certificate is as good as its attestor's word plus the re-check command. The one
   attestor and the owner that admits attestors are the same single-key account. The registry returns the valid
   certificates of every attestor ever admitted, and only an attestor can revoke its own: removing an attestor does
   not withdraw what it attested, so a reader has to choose whom to believe (the scanner's list is `exitproof.near`).
   A second independent attestor, or re-checks run by anyone and recorded on chain, would make stage 2 less
   dependent on us.
4. **The tie between model and wasm is tested, not proved.** Conformance on random traces plus mutants is strong
   evidence but not a theorem about the bytes.
5. **Stage 1 has no mainnet member.** The four upgrade-plugin users we read have no delay set. The proof kit and the
   testnet examples show what a delay (`up_init_staging_duration`) and a certificate of the code hash would give their
   users.
6. **Stage 0/1/U classification is heuristic** for contracts without a certificate; roles guarded by generic names
   cannot be mapped to methods from outside. A code-change method with a name outside the rules (`get_upgrade`,
   `apply_deployment`, `rotate`) gives U, and next to the upgrade plugin stage 0 unless the code hash is certified or proved here; a certified
   plugin with such a method beside it would still read as stage 1. Reading the paths from the wasm (a call graph from the exported methods to the
   deploy and add-key host functions) would replace the names; near-sdk 3 and earlier link every host function
   through one table, so the imports alone do not tell.
7. **Running a `check.sh` changes the hash of three proof directories** (`pool-proof/`, `wnear-proof/`,
   `token-standard/`): run logs with timings are among the hashed files. A fresh checkout and
   `bundle_hash.py --git` give the attested hash; the working tree after a check does not. The fix is to keep run
   output out of the hashed set and attest the three directories again.
8. **Certificates on chain say "Exit Proof repository" without a URL** (`artifact_location`). The repository is
   public now; a link needs a new attestation of each certificate, which is a mainnet transaction.
9. **A token certificate is a file, not an on-chain record.** `token-monitors/` lets a token team certify its own
   wasm with the model-free monitors (any library version, any initialiser), and `token_check` counts the
   certificates of `evidence/token-certificates/` by code hash; a certificate brought by the caller is shown as a
   claim until the caller has re-run it, because a file is not authenticated. Missing: attestation of such a
   certificate in the registry, so that an agent finds it without the file; a config that exercises a token's
   extensions (fee, pause, bridge exit) — a PASS says nothing about methods the config did not call; and the
   run of the census itself, which is still not in this repository.
10. **The method is not a kit yet.** The upgrade check, the trace generator, the replay and the mutant drivers of
   `intents-proof/` are written for one contract (its commit, its files, its ledger write sites). The token-side
   models, the kernel re-check, the bundle hash, the registry and the shape of `check.sh` carry over as they are.
   A second contract of similar size is weeks of work for an engineer who has this repository as the example.
11. **The full answer is slow on the public endpoints.** The stage alone needs 4–20 reads (`--fast`, `detail:
   "stage"`: two or three seconds). Describing who holds each power needs up to 100 reads; when the endpoints
   rate-limit the caller's address that takes a minute or more. Descriptions of holder accounts could be cached.
12. **The replay of NEAR Intents does not generate every intent.** No `token_diff` intent, no `auth_call`, no key
   change during a trace: the balancing of a swap between signers and its fees are moves that balance by
   assumption in the model (`intents-proof/lean/NOTES.md` §4, item 7), and no source mutant touches them.
13. **The live ledger is not read against the whole invariant.** The theorems start from an empty ledger under the
   latest of the 18 codes `intents.near` has had (`intents-proof/evidence/intents-code-history.json`); the live
   reading compares each token's supply in the ledger with the holdings, not the sum of all balances with
   `total_supplies`, and in-flight receipts are not read.

## Directions, most valuable first

1. Give the page a list of the largest contracts with their stages, kept current by the watch.
2. `token_diff` intents with fees and `auth_call` in the Intents replay, with model and source changes on that
   path, then a lemma that a payload whose deltas cancel is a composition of moves (gap 12).
3. Theorems for the multi-token (NEP-245) paths of the Intents ledger, where the 2026 loss happened; the same
   strict-world statements for wNEAR.
4. Attest token certificates in the registry (gap 9) and show them in the scanner; run the census from this
   repository.
5. Exit theorems for the next largest holders of deposits: liquid staking contracts and the farm-enabled pool code
   (11.1% of stake, currently stage 0 because of its `upgrade` method).
6. A second attestor and on-chain re-check records.
7. The method as a kit for a second contract (gap 10); code-change paths from the wasm (gap 6).
8. Independent review of `token-standard/` and `upgrade-window/` in the manner of `REVIEW.md`.
