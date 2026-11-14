# Contributing

Issues and pull requests are welcome. This page gives the setup, the commands to run before you send a change,
and the rules that keep the checks meaningful.

## Set up

| For | You need |
|---|---|
| The scanner, the token check, the MCP server, the numbers check and the self-test | Python 3.10 or newer, standard library only |
| The Lean proofs | Lean 4.35.0 through `elan` (no Mathlib) |
| A full check of a proof directory: the model against the deployed wasm on the nearcore runtime | Linux x86-64, `rustup`, a C/C++ compiler, `cmake`, libclang; `java` for the TLA+ runs; `docker` and cargo-near 0.22 for the rebuilds from source |

Nothing in this repository signs a transaction unless you run a deploy or attest script with your own key.
Everything else reads public RPC.

## Before you send a change

```sh
./check-all.sh             # the numbers in the documents against the evidence files, then the self-test: 1 to 3 minutes
./check-all.sh --offline   # the same without the network: a few seconds
```

A change inside a proof directory also needs that directory's `check.sh`. `./check-all.sh --proofs` runs all
seven; on a machine with nothing built that takes about 70 minutes. [AGENTS.md](AGENTS.md) lists every command
with its time and the last line of a run that passes.

## Rules that keep the checks meaningful

- **Four directories are frozen.** `pool-proof/`, `wnear-proof/`, `token-standard/` and `upgrade-window/` are
  recorded in the mainnet registry by a hash of their contents. Any edit inside, a README included, ends the
  match, and `tools/selftest.py` fails. Change them only together with a new attestation
  ([docs/DEVELOPMENT.md](docs/DEVELOPMENT.md) has the steps), and say so in the pull request.
- **A run writes each record. Do not edit one by hand.** Files under `evidence/` and under the `evidence/` of a
  proof directory come from the scripts named in [docs/DEVELOPMENT.md](docs/DEVELOPMENT.md). For
  `intents-proof/`, stamp a new record with `scripts/source_hash.py --stamp <file>` right after the run:
  the numbers check fails for evidence that was made from other sources.
- **A number in a document has an evidence file behind it.** If you quote a new number, add its fact to
  `tools/numbers_check.py`. If you change a rule of the scanner, add its case to `tools/selftest.py`.
- **Never present a lower level of evidence as a higher one.** A claim is proved (a Lean theorem about a model),
  tested (the model against the exact wasm), read (chain state or a contract's own answer) or heuristic (method
  and role names). [CLAIMS.md](CLAIMS.md) is the reference; a new claim gets its row there.
- **A failure to read the chain is never a verdict.** A tool that cannot read what it needs answers "unreadable"
  and exits with a non-zero status. It does not answer with a stage, a pass or "not found".
- **Reports show how strongly a power is guarded, never who holds it.** Outputs carry counts and kinds of
  holders, not account names of key holders.
- **Say what is assumed.** If a change adds an assumption, add it to the assumptions of the proof entry in
  `tools/proofs.json`, to the README of the directory and to [CLAIMS.md](CLAIMS.md).
