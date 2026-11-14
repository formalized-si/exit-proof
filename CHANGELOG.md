# Changelog

This file lists the changes by day. We wrote the project for NEAR HACKATHON 2026, from 11 to 14 November.

## 14 November 2026

Two independent reviews of the repository as it stood on 13 November: one in the manner of the hackathon's automated screening,
one by a formal-verification reviewer. Both rebuilt the proofs and re-ran the checks. What they found, and what
changed:

- **The scanner gives no favourable answer the evidence does not support.** Stage 2 needs an account with no access
  key of any kind (a function-call key pays its gas from the account's balance) and its own code, not a global
  contract. A view the exit window depends on that does not answer gives stage 0, and the staging timestamp bounds
  the window whenever it is set, as in the proved bound. With the upgrade plugin only its five methods are exempt,
  and `deploy_certified` only for the builds of the proved gated vault. Bytes whose hash is not the account's code
  hash are refused. An unread registry is no answer. Method names are matched without regard to case, and six more
  upgrade names are recognised. The reference agent stakes at stage 1 only on a certified plugin.
- **The deployment history: the indexer lists the first and the latest deployment.** One row still means one
  deployment. For `wrap.near`, whose proof covers two, the full list was read once from every deployment receipt
  (`tools/deploy_history.py`, `evidence/wrap-near-deployments.json`): two, the ones the proof names. The scanner
  reads NearBlocks API v3 (v1 is switched off on 2026-11-22) and keeps v1 as a fallback.
- **A token whose owner can freeze or destroy a holder's balance is not reported as standard now**: the token check
  lists those methods and answers unknown (USDt: pause, blacklist, destroy).
- **The pool replay is measured**: 8 of 8 one-line changes of the pool model are noticed (`pool-mutants/`).
- **The history of `intents.near`**: 19 code hashes, 18 code changes since 2024-11-05, read from archival state
  (`intents-proof/evidence/intents-code-history.json`). The census field `deployments: 2` is the indexer's list.
- **What the Intents replay does not reach is stated**: no `token_diff` intent, no fees, no `auth_call`.
- **The numbers check reads the headline numbers of the README** (validators, large contracts, the runs of each
  proof directory), and the README has a section on the hackathon window.
- **A third, cold screening of the pushed commit** found four more places and they are closed: a key-list read that
  says "unknown account" for an account just read is no answer (it gave an empty key list); stage 1 needs the plugin
  established for the code (a certificate or a proof of this repository), names alone give stage 0; the exit window
  is measured on the chain's clock; the token check reads a fee only from a view that holds a recognised fee field
  (a fraction, the 21st tier and top-level fields included), and the watch reports a tax switch after a run that
  could not read it.
- **The repository is public and the page is hosted** at `formalized-si.github.io/exit-proof`. The page shows where
  each line of evidence comes from, gives a link to an answer (`#check=<account>`), starts loading the scanner when
  a visitor comes near a form, and has two more parts: the registry on mainnet with its transactions, and what an
  agent, a contract team, a token team and a reviewer run.

## 13 November 2026

- **Who can lower a balance in NEAR Intents, with the checks made.** A second layer of the model, the strict
  world, binds a refund to its transfer call, gives an owner's operation its authorisation (a direct call, or a
  signed payload with a registered key and an unused nonce) and changes the role table by the near-plugins rules
  only. It refines the first world step by step, so the earlier theorems hold in it. `T4_authorised` names six
  ways a balance can fall. The proof has 136 statements.
- **The replay computes more and copies less.** The role table, the refunds in flight and the public keys of an
  account come from the model and are compared with the wasm after every receipt. The generator has eleven
  probes. Of 121 one-line changes of the model the replay notices 114; no receipt can show the other 7.
- **Stage 2 needs the origin of the state.** An independent review showed that the proved code hash, an empty key
  list and a certificate are not enough: an account can hold a state that other code made. The scanner now gives
  stage 2 only when the deployment history lists one code deployment, or exactly the deployments the proof names,
  and only for a certificate of an accepted attestor. The exit plan and the reference agent follow the same rule.
- **A token certificate brought by a caller is a claim.** The token check verifies that the file is consistent and
  shows it; it counts the certificate only after the caller has re-run it.
- **Verified upgrades.** A vault that deploys new code only if the registry holds a certificate for its hash:
  contract, Lean theorem, tests on the nearcore runtime, two examples on testnet.
- **A kit for token teams.** `token-monitors/` runs any fungible-token wasm on random traces with 14 monitors of
  the proved properties and writes a certificate. Four codes taken from mainnet passed.
- **The upgrade check got a static part.** A reviewer's three source variants passed the first, dynamic-only
  version. It now also compares the modelled source files, the places that write the ledger and the exported
  methods. Eight of eight variants are rejected.
- **The checks check more.** The numbers check requires the numbers of a fact to stand together and reads every
  mention of the most quoted claims. Each evidence file of the Intents proof records the sources it was made
  from. `./check-all.sh` runs everything in one command. All long runs were repeated on the final sources.
- **A page.** `web/` runs the scanner and the token check in the browser, unchanged, on Python compiled to
  WebAssembly. The pictures and the page follow the design of formalized.si.
- The scanner fails closed in more cases: a contract that governs itself is stage 0, a function-call key on the
  contract's own account counts when it reaches a callback, a code that cannot be read gives no verdict.

## 12 November 2026

- **Exit stages and the scanner.** For any NEAR account: who can change its code, who can move or freeze funds in
  it, and its stage. A census of 340 validators and of 28 large contracts.
- **Four proofs with their conformance harnesses**: the core staking pool, wNEAR, the token standard of
  near-contract-standards 5.29.0, the staging delay of the near-plugins upgrade plugin. Each model runs against
  the exact wasm on the nearcore runtime, with one-line mutants.
- **A registry on NEAR mainnet.** `registry.exitproof.near` was deployed, received four certificates and had its
  only access key deleted.
- **The live state of the proved pools.** At one block all 196 pools of the proved code satisfy the precondition
  of the exit theorem.
- **Two stage-1 examples on testnet**, one quiet and one with an upgrade staged.
- An independent adversarial review of the pool and wNEAR proofs narrowed several one-line claims.
- An MCP server, a reference agent and an exit plan for a delegator.
- **The Intents proof began**: the model of the token ledger, backing, settlement and credit on arrival; the
  byte-identical rebuild of the deployed code from source; a TLA+ specification of the same ledger; a blind
  re-statement of the theorems that found two wrong sentences.
- **A census of token code**: 86 code hashes of the tokens that the Intents ledger holds or the largest exchange lists, 71 of them run with monitors of the
  proved token properties.

## 11 November 2026

- We started from the question "if I put money into this contract, can I always get it back?", and read which
  pool code the validators of the epoch run.
