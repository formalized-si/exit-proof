# Exit Stages

A stage answers one question for a depositor: **if I put money into this contract, what guarantees that I can get it
back?** Each stage is defined by evidence anyone can re-check, not by a reviewer's opinion.

| Stage | Meaning | Required evidence |
|---|---|---|
| **2 — Proven exit** | The code cannot change, and a depositor can always withdraw by its own calls. | (a) no code-change path: no full-access key, no upgrade method, no global contract referenced by account id `[chain]`,`[code]`, and no access key of any kind (a function-call key pays its gas from the account's balance, an outflow the theorems assume away) `[chain]`; (b) a machine-checked exit theorem registered on chain for the exact code hash by an attestor the reader accepts `[proof]`; (c) origin: the account's state was made by this code — one code deployment in its history, or every deployment recorded by the proof and none since (`wrap.near`: two, reported as "under a stated condition") `[hist]`. The theorem's precondition on the live state is a separate reading: it is checked for the 196 staking pools of the census at one pinned block (`evidence/pools-live.json`, and their origin in `evidence/pools-origin.json`), not by the scanner on each call |
| **1 — Exit window** | The code can change, but only after a publicly visible delay `D`; a user who starts leaving when the new code hash is staged is out before it takes effect, provided their exit takes less than `D`. | (a) no code-change method other than the five of the upgrade plugin is found by name `[name]`, and the plugin's current window is `D > 0` on the chain's clock `[view]`; (b) no full-access key, no other upgrade method, no global contract by account id `[chain]`,`[code]`; (c) no privileged party can pause exits or move deposits `[name]`,`[view]`; (d) every view these readings come from answered; (e) the code runs the plugin unchanged: an `upgrade-window` certificate for its code hash from an accepted attestor, or a proof of this repository for it in `tools/proofs.json` (the gated vault) `[proof]`. The delay property itself is proved for the plugin (`upgrade-window/`). Without (e) the plugin is recognised by names only, and the answer is stage 0 |
| **0 — Keyholder trust** | The code can change with no notice (or exits can be paused / deposits moved by a privileged party). Safety rests on whoever holds that power. | the scanner names the path and the strength of its guard: DAO vote, multisig quorum, another contract, several keys of one account, or a single key |
| **U — Unproven** | No code-change path was found, but no exit theorem covers this account. | absence of evidence, stated as such: no theorem for the code hash, or the account has a key or a history the theorem does not cover |

Notes

- Stages are computed from chain state at the time of the query; a contract moves down the moment a key is added, a
  delay is removed or the code hash stops matching its certificate.
- Evidence tags: `[chain]` current state, `[code]` the deployed wasm's exports, `[view]` the contract's own view methods
  (self-reported), `[hist]` the account's deployment history as an indexer lists it, `[proof]` a Lean theorem
  registered on chain by code hash. Stage 2 never rests on `[view]` alone.
- What is on chain for stage 2 is an attestation: an account says that the proof in the named directory, with the
  named hash, is about this code hash, and names the command that re-checks it. The scanner checks neither the proof
  nor the theorem's precondition on the live state; it checks the code hash, the absence of a code-change path, the
  attestor and the origin.
- A stage is about exits, not about everything that can go wrong (oracle risk, economic design, bridges).
- Climbing the ladder: turn on the plugin's staging delay, drop pause powers over withdrawals and get an
  `upgrade-window` certificate for the code hash (the kit of `upgrade-window/` runs the wasm against the plugin model)
  → stage 1; freeze the
  code (remove keys and upgrade methods) and obtain an exit theorem → stage 2. The kits in `token-standard/` and
  `upgrade-window/` are the builder-side tools for this.

## How the stage is computed (`tools/exitproof.py`, function `stage`)

1. Read the account: access keys, code hash, global-contract reference.
2. Read the wasm's exported methods; classify upgrade-like, fund-moving and pausing methods by name, and read the
   contract's own role and delay views (`acl_*`, `up_get_delay_status`, owner getters).
   Migration entry points (`migrate`, `migrate_*`), views, callbacks and methods that deploy another contract are
   not counted as code-change paths. A role named `DAO` counts as a pause or fund-moving power only when the
   code has a method of that kind.
3. Look up certificates for the code hash in the on-chain registry: kind `exit` for stage 2, kind `upgrade-window`
   as one of the two bases stage 1 needs (the other is a proof of this repository for the code hash). The registry is on mainnet and keyed by code hash, so it is also consulted
   for testnet accounts.
4. Apply the table above. The report prints the stage, the reasons, and every line of evidence with its tag.

Rules that make the answer fail closed (each has a check in `tools/selftest.py`):

- **No code read, no verdict.** If the contract's code cannot be read, the scan refuses instead of reporting an
  empty method list as "no code-change path found". Bytes whose hash is not the code hash the account names are
  neither used nor kept. When no code-change path is found and the registry does not answer, there is no answer:
  the registry decides between U and 2. A key list that does not end is no key list.
- **Stage 2 needs the certificate on chain, from an accepted attestor.** An entry in the local list
  `tools/proofs.json` is not enough, and neither is a certificate of an attestor outside the scanner's list
  (`ATTESTORS` in `tools/exitproof.py`, default `exitproof.near`; `EXITPROOF_ATTESTORS` sets another). The registry
  itself keeps a certificate of any attestor its owner admitted, and only the attestor can revoke it.
- **Stage 2 needs the origin of the state.** An exit theorem is about states the proved code reaches from its own
  initialisation. A deployment keeps the storage of an account, so an account that ran other code first can hold a
  state the theorem says nothing about, under the certified code hash and with no keys left. The indexer
  (NearBlocks, API v3, v1 as a fallback) lists the first and the latest code deployment of an account, so one row
  means one deployment. Stage 2 is given only when it lists one, or when the proof entry names the deployments it
  covers, records the full list of them read once from every deployment receipt of the account
  (`tools/deploy_history.py`; for `wrap.near` 2, in `evidence/wrap-near-deployments.json`), and the indexer still
  lists the first and the latest of those (a later deployment would be the new latest). An account that runs a
  global contract gets no stage 2: which code wrote its state is not in this history. Otherwise the answer is U,
  and when the history cannot be read there is no answer. This part of the evidence is as good as the indexer.
- **A condition goes into the headline.** When the theorem holds under a condition on the live state that is not
  fully checked (wNEAR: an invariant of 2.68 million balance records, and a state left by an earlier code), the
  report says `PROVEN EXIT UNDER A STATED CONDITION` and prints the condition first.
- **A string that is not an account id gets no answer**, and an account that does not exist is reported as not
  found, with the other network named when the name belongs there.
- **A contract that governs itself is stage 0.** A DAO (a passed proposal can replace its own code), a multisig (a
  confirmed request can deploy code or add a key) and a contract whose participants vote on an update have a
  code-change path with no delay; the report names the guard.
- **A function-call key on the contract's own account is stage 0** when it is unlimited or reaches a callback or
  a privileged method: its holder calls the contract as itself, so private callbacks and own-account-only methods
  accept the call. A key limited to an ordinary public method (a relayer key) is listed and changes nothing.
- **A gate is not a window.** A gated vault whose staged code has passed its delay is one attestation away from a
  deploy; no time bound holds in that state, and it is reported as stage 0. `deploy_certified` is taken as part of
  the plugin path only for the builds of this repository's gated vault, whose gate is proved (`gated-upgrade/`);
  for any other code it is an upgrade method without a delay, whatever the contract's `gate` view says.
- **Stage 1 fails closed.** A view the window or the powers that would close it are read from (`up_get_delay_status`,
  `up_staged_code_hash`, `acl_role_variants`) that does not answer gives stage 0. The staging timestamp bounds the
  window whenever it is set, as in the proved bound `safeUntil`. With the plugin, only its five methods are its
  path: any other code method, `up_`-named or not, is a path of its own. Method names are matched without regard to
  case.
- **Stage 1 says how long.** `delay_seconds` is part of the answer; three minutes and seven days are both stage 1,
  and the reader decides what is enough (the reference agent requires 24 hours by default, and stakes at stage 1
  only when the code hash has an `upgrade-window` certificate from an accepted attestor).
- **A proof that is not an exit proof never raises the stage.** It is reported as `other_proofs`, apart from
  `exit_proof`.
