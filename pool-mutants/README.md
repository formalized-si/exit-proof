# Does the pool replay notice a wrong model?

`pool-proof/` ties its Lean model of the staking pool to the deployed wasm by running both on the same 1149 random
traces and comparing them after every step. A comparison that agrees is evidence only if it would disagree with a
model that is wrong. This directory measures that: each line of `mutants.txt` changes one line of the model
(`pool-proof/lean/StakingPool/Model.lean`), and the changed model is run on the same traces.

| Id | Change of the model | Traces that differ, of 1149 |
|---|---|---:|
| P0 | none (control) | 0 |
| P1 | withdraw unlocks one epoch early | 119 |
| P2 | unstake delay 3 epochs instead of 4 | 1135 |
| P3 | unstake pays the rounded-down amount | 665 |
| P4 | withdraw ignores the liquid balance | 51 |
| P5 | ping drops the "total balance must not fall" check | 33 |
| P6 | deposit credits one yocto more | 1149 |
| P7 | the owner's fee is added twice | 685 |
| P8 | stake charges the rounded-up amount | 695 |

**8 of 8 one-line changes are noticed**, and the unchanged model agrees on every trace. The two changes that only
fault traces reach (P4, P5) are seen by 3 to 5% of the traces. The changes cover the exit arithmetic, the unlock
delay and two balance guards; they are a sample, not one change per guard as for NEAR Intents
(`intents-proof/MUTANTS-REVIEW.md`).

The run (`evidence/results.json`) was made by an independent reviewer on a fresh copy of the repository as it stood on
13 November, in which `pool-proof/` is the same as here, on 2026-11-14.

## Run it

```bash
pool-mutants/run.sh [WORK_DIR]
```

It copies `pool-proof/` to `WORK_DIR` (a new temporary directory by default), so the attested directory and its
bundle hash stay as they are; runs its `check.sh` there (the traces of the exact wasm and the unchanged model must
agree); then, for each line of `mutants.txt`, builds the executable model alone with the change (`mkdefs.py` keeps
the definitions of `World.lean` and drops the theorems, which a wrong model would not prove) and compares it with
the same traces. It ends with `control EXACT: 1; mutants noticed: 8 of 8` and exits with 0 only then. It needs
what `pool-proof/check.sh` needs (Linux x86-64, `elan`, `rustup`, a C/C++ compiler, `cmake`, libclang), and takes
about as long as that check plus a minute per change.

`mutants.txt` has one change per line: `id|what|the line in Model.lean|the line that replaces it`.
