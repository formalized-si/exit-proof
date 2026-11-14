# Third-party notices

The MIT license in `LICENSE` covers what this project wrote. It does not replace the licenses of the components
below. Each proof directory has a `NOTICE` file with the exact files, hashes and sources.

## Stored in this repository

- **NEAR core contracts**, <https://github.com/near/core-contracts>, MIT OR Apache-2.0. The staking pool v0.4.0 at
  commit `1cacc9dbd57db7af2504c181edd707299869bce7` (`pool-proof/wasm/staking_pool.wasm`) and wNEAR at commit
  `54f8267436058567b66efdaba3e790394f7f1529` (`wnear-proof/wasm/w_near.wasm`, and its copy in
  `intents-proof/harness/wasm/`). Both are unmodified build artifacts of those commits. They are the objects of
  the proofs.
- **The code that `wrap.near` held before block 35438886** (`wnear-proof/evidence/old_9kQaNisc.wasm`), as a public
  archival node returned it. It is kept as evidence for the history of that account.
- **NEAR Intents**, <https://github.com/near/intents>, MIT, Copyright (c) 2025 NEAR Foundation.
  `intents-proof/harness/wasm/intents.wasm` is the code deployed at `intents.near`, as a public RPC returned it.
  It is byte-identical to the build of commit `16d04f6ec4401263f8914638710260da50bb46b0`.
- **near-sdk-rs**, <https://github.com/near/near-sdk-rs>, MIT OR Apache-2.0. The fungible-token example at tag
  `near-sdk-v5.29.0` (commit `1aac824cc543b2f201831f888c85396529716742`): its source, copied unmodified, in
  `token-standard/token/example-ft/` and `token-monitors/reference/token/`, and wasm files built from it. The two
  mock tokens of `intents-proof/harness/` are that example with one deliberate change each.
- **near-plugins** v0.5.1, <https://github.com/near/near-plugins>, commit
  `312e016e0574d5756f6eba37acc82d9a237b2e3e`, CC0-1.0, and **near-sdk** 5.26.1 and 5.30.1, MIT OR Apache-2.0.
  Their compiled code is inside the vault wasm files of `upgrade-window/` and `gated-upgrade/` and inside the
  registry build. The `Cargo.lock` next to each contract pins every crate.
- **Inter Tight** (copyright The Inter Project Authors) and **IBM Plex Mono** (copyright IBM Corp.), SIL Open Font
  License 1.1: the fonts of the page in `web/` and of the pictures in `docs/assets/`. The font files and both license texts
  are in `web/fonts/`.
- **The formalized wordmark and symbol** (`web/assets/formalized-white.svg`, `formalized-mark.svg`) are the mark of
  the team that wrote this project. The MIT license of the code does not extend to the mark.

## Used and not stored

- **Lean 4**, tag `v4.35.0`, Apache-2.0, with the tools that ship with the toolchain. No Mathlib.
- **near-contract-sim** at commit `8e4b69b999c185a1a26fa5e025db042436888856` with the **nearcore** 2.14.0 runtime:
  the harnesses build against it. cargo fetches both at build time, each under the license stated in its package.
- **near-contract-standards** 5.29.0 and 3.1.0: the mutation tests apply one-line changes to a copy taken from
  the local cargo registry at build time. Neither the library source nor a mutated wasm is stored.
- **Pyodide** 0.26.4 (CPython for WebAssembly, MPL-2.0): the page in `web/` loads it from the jsDelivr CDN when a
  visitor asks for an answer.
- **TLA+ tools** v1.8.0 (`tla2tools.jar`, MIT): `intents-proof/tla/run.sh` downloads the file and checks its
  sha256.
- **cargo-near** 0.22 and the docker image that a contract names in its own metadata, for the rebuilds from
  source.
- **Contract code read from NEAR mainnet** by the scanner and the token check goes to a local cache (`codes/`),
  which is not part of the repository. The certificates in `evidence/token-certificates/` are records of runs of
  such code and contain none of it.

The stage ladder follows the idea of L2BEAT's Stages for rollups and DeFiScan's stages for DeFi protocols. No code
or text of either is used.
