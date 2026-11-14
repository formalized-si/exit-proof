# Rebuilding the pool code from source (attempt of 2026-11-12)

The goal: to show that the bytes `J1arLz48…` (the code of the 196 `*.poolv1.near` pools) are built from the
source `near/core-contracts@1cacc9d`, and do not merely equal the committed `res/staking_pool.wasm`.

The result: **not reproduced byte for byte.** The link between the code and the source remains two facts:
the hash of the deployed code = the artefact committed at `1cacc9d`; the Lean model agreed with the execution
of exactly these bytes (`../pool-proof/REPORT.md`).

| Attempt | Compiler | Bytes | Hash | Result |
|---|---|---:|---|---|
| vendored, without dev-deps | 1.45.0 / 1.44.1 / 1.45.1 / nightly-2020-05-15 | 261 396 / 261 715 / 258 517 / 262 784 | different | no match |
| vendored, without dev-deps + the author's paths | 1.43.0 / 1.43.1 | 262 370 / 262 351 | different | no match |
| the original Cargo.toml + Cargo.lock, git CLI, the author's paths | 1.43.0 | 262 367 | `7Ah8KQQ3…` | no match |
| the deployed code | — | 262 183 | `J1arLz48…` | — |

What could be established from the wasm itself:
- the strings of the deployed code carry the compiler hash `4fb7144ed159…` = rustc 1.43.0 and the path
  `/Users/ekwork/.cargo/registry/src/github.com-1ecc6299db9ec823/` — a 2020 build on its author's machine;
- our build with the same compiler has the same export and import tables (md5 of the text form), but 1111
  functions against 1106; the strings of the panic locations differ (`<::core::macros::panic macros>`).

"The author's paths" means building with `--remap-path-prefix` so that the cargo home maps to the path seen in
the deployed wasm. The build scripts and logs of these attempts are not part of this repository. The next check,
if needed: a macOS host of that period (macro spans may be handled differently) or the exact output of the
author's `cargo -vV`.
