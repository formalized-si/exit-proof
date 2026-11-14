# Demo script (about 90 seconds)

One complete moment: an agent is asked to stake; it checks the exit stage first and makes the right call for two
real mainnet pools — then the viewer sees what the stage rests on.

1. **Problem, one sentence on screen (5 s).** "Before you stake or deposit on NEAR: can you always get it back?
   'No full-access keys' is not an answer."
2. **Stage 2 (20 s).** `python3 tools/agent_demo.py astro-stakers.poolv1.near 100`
   → `stage: 2 — PROVEN EXIT`, the on-chain certificate (`registry.exitproof.near`, theorem `StakingPool.exit_guarantee`,
   re-check command) → `decision: PROCEED` and the transaction it would sign.
3. **Stage 0 (15 s).** `python3 tools/agent_demo.py liver.pool.near 100`
   → `decision: REFUSE`, then the reasons: exit stage 0 (KEYHOLDER TRUST), upgrade method(s) without a delay.
4. **The exit itself (10 s).** `python3 tools/exit_plan.py figment.poolv1.near <a delegator>` → two calls, the earliest time
   of the second, the theorem behind each.
5. **Why this is not a heuristic (20 s).** Split screen: the statement of `exit_guarantee` in
   `pool-proof/lean/StakingPool/Exit.lean`, and `pool-proof/check.sh` finishing: axioms
   `[propext, Classical.choice, Quot.sound]`, `1149 traces EXACT`.
6. **Scale (10 s).** "86.2% of all NEAR stake is at stage 2. 196 of 196 pools checked on live state, 256 564 delegator
   accounts." (`docs/CENSUS.md`, `evidence/pools-live.json`)
7. **The gap (10 s).** `python3 upgrade-window/check-upgrade-window.py token.sweat` → `exit window now  none`.
   "The upgrade plugin has a delay that would give users time to leave. On the contracts we read, it is not set."
   Then what it looks like when it is set: `python3 tools/exitproof.py staged-vault.exitproof-demo.testnet --network testnet`
   → `EXIT STAGE 1 — EXIT WINDOW … NEW CODE IS STAGED`: the upgrade is announced on chain and depositors have days to leave.
8. **Next step (5 s).** "Add `exit_check` to your agent (MCP). Builders: `certify-token.sh`, and the delay plus a certificate of the code."

Recording notes: steps 2–4 and 7 run live in about 10 s each (read-only RPC). Step 5 can be a recorded run; say so.

## Second script: Intents Proof (about 90 seconds)

One complete moment: the ledger of the contract that lost $3.8M is proved for standard tokens, the proof is tied to
the bytes on mainnet, and the same tools tell an agent which tokens are outside the proof.

1. **Problem, one sentence on screen (5 s).** "A NEAR contract credits what a callback *reported*. Does the ledger of
   NEAR Intents ever show more than the contract holds?"
2. **The theorem (15 s).** `intents-proof/lean/Intents/Theorems.lean`, the statement of `T1_backing`: every reachable
   state, any order of receipts, any receipt failing. `lean/Axioms.lean` → `[propext, Quot.sound, Classical.choice]`.
3. **Tied to mainnet (15 s).** `scripts/rebuild.sh` ending with the sha256 of the code at `intents.near`; then
   `evidence/conformance.json`: 311 697 receipts of the deployed wasm replayed through the model, 308 469 agree, 0 disagree.
4. **The assumption is real (15 s).** `python3 tools/token_check.py batman-4.nearlytrade.near` →
   `DEVIATES FROM NEP-141 … transfer tax ON`. Then `python3 tools/intents_backing.py --table`: 354 tokens with a
   standard verdict, ledger never above the holdings; two tokens outside the assumption, where the ledger is above the
   holdings.
5. **It survives the next upgrade (15 s).** `scripts/verify_upgrade.sh fce0936b` → `"verdict": "NEEDS REVIEW"`: the run agrees, no
   new place writes the ledger, three modelled files changed; then one source mutant → `DIVERGES`.
6. **A contract that cannot skip the check (15 s).** `python3 tools/exitproof.py gated-quiet-vault.testnet --network
   testnet` → `EXIT STAGE 1 — EXIT WINDOW (168 h, certified upgrades only)`; then the refused `deploy_certified` of
   uncertified code on `vault.gated-upgrade.testnet` in `gated-upgrade/TESTNET.md` (that vault was left with
   uncertified code staged, and the scanner reports it as stage 0).
7. **Limits, said aloud (5 s).** "Fungible-token paths. The multi-token path, where the 2026 loss happened, has no
   theorem yet."
8. **Next step (5 s).** "`token_check` and `exit_check` are MCP tools; `watch.py` tells you when the code changed and
   the certificate stopped applying."

Recording notes: steps 4 and 6 run live (read-only RPC). Steps 3 and 5 take minutes: show recorded runs and say so.
