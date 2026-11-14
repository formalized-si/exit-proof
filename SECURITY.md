# Security

Exit Proof is a hackathon project. Its tools only read chain state. Its registry on NEAR mainnet stores
certificates and holds no funds. No outside party audited it. A stage, a verdict or a certificate from this
repository is evidence to weigh, not a guarantee to rely on with money.

## Reporting

Use GitHub's private reporting for this repository: **Security → Report a vulnerability**. Do not open a public
issue for a report in scope until we fix it or 30 days pass.

A useful report has three parts:

- The input: an account id, a certificate file, a transaction or a call.
- The command that shows the effect.
- The result that you expected instead.

This repository reads contracts of other teams. A weakness in one of **those** contracts is not a report for us:
send it to the team that owns the contract.

## In scope

- **A tool gives a better answer than its rules allow.** The scanner reports stage 2 without an exit certificate
  from an accepted attestor, without the origin of the account's state or with a code-change path present;
  stage 1 with a window that is not there; `token_check` reports a token as standard from a certificate that is
  not for its code; the MCP server answers `ok` when the chain was not read.
- **The registry contract** (`registry/`, deployed as `registry.exitproof.near`) stores a certificate from an
  account that is not an attestor, changes or removes a stored record, or lets anyone but the attestor revoke.
- **The gated vault** (`gated-upgrade/`) installs code that has no valid certificate of the accepted kind, or
  installs it before its window.
- **A proof is not what it says.** A `check.sh` passes with a `sorry`, an added axiom or a statement that is
  vacuous; a theorem in a README says more than its Lean statement.
- **A check passes when it should not.** `tools/numbers_check.py` or `tools/selftest.py` accepts a document or a
  rule that contradicts the evidence.

## Known limits, not vulnerabilities

The README, [CLAIMS.md](CLAIMS.md) and [docs/ROADMAP.md](docs/ROADMAP.md) state these limits:

- Theorems are about Lean models. The tie to the deployed bytes is hash equality plus execution on random
  traces, measured with one-line changes of the model. It is not a proof about wasm.
- The registry does not check proofs on chain. A certificate is an attestor's statement with a command that
  re-checks it. The one attestor so far, and the owner that admits attestors, is an account with one key.
- Below stage 2 the scanner's verdict rests partly on method names and on the contract's own view methods. A
  contract can misreport.
- The origin part of stage 2 comes from an indexer's list of deployments.
- A token certificate is a file. It is a record of a run on random traces, not a proof.
- The Intents proof covers the fungible-token paths, for a token that behaves as the standard. It does not cover
  the multi-token and NFT paths, gas, or the signature standards.

## History

On 13 November 2026 an independent review found two paths to an answer better than the rules allowed. An account
that held the proved pool code hash and no keys was reported at stage 2 whatever its state had been made by; a
token certificate with a hand-edited code hash was accepted. Both are closed and are cases of
`tools/selftest.py`.

On 14 November 2026 two more independent screenings found further paths: a function-call key, a global contract or
a deployment history read only in part could still give stage 2; a key-list read that said "unknown account" for an
account just read gave an empty key list (stage 2, PROCEED and an exit plan); stage 1 could come from method names
and the contract's own views alone; a token whose owner can freeze or destroy balances read as standard now. All are
closed and are cases of `tools/selftest.py` (CHANGELOG.md, 14 November).
