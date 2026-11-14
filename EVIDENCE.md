# On-chain evidence (NEAR mainnet)

Registry: `registry.exitproof.near` · owner and first attestor: `exitproof.near`.
Explorer: `https://nearblocks.io/txns/<transaction id>`.

| Step | Transaction |
|---|---|
| create `exitproof.near` | `5uuZpR5dcoegza4r4DT3XkyTB4TjA51GhNhz1P1uvXPt` |
| create `registry.exitproof.near` | `Heaq2XrrtvDp8FRsM8qsRh1eHAvTkp2ZbfjuxeBsbzJV` |
| deploy the registry and call `new(owner = exitproof.near)`; wasm sha256 `a8984200f13b774e71ac24cfa260ee69efaaa6123e8da498e4b5cc815ce4ca9b` (`registry/`, near-sdk 5.30.1, built with cargo-near 0.22) | `Bb34SR1zsenLKVcjLrkacnvguYqtmGrghgN1e3Fub8t5` |

Attestations (`registry/attest.py`; each stores the certificate from `registry/certificates/<name>.json` with the bundle
hash computed by `tools/bundle_hash.py`):

| Certificate | Kind | Code hash | Bundle hash | Transaction |
|---|---|---|---|---|
| staking pool | `exit` | `J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY` | `2d4d8251bb777f346a4ee5b2367dc4a71d37e5643e7da925027e0ba63ee5b618` (`pool-proof/`) | `31oaqvX2N8WEvihboMQ7WoV4jt563F314fGoeERMdkFK` |
| wNEAR | `exit` | `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1` | `6c29def20cc0b1a9499559383bddfe729ff909b88ccbb81889acc46c40c875ee` (`wnear-proof/`) | `7h4KGyi9Quu2Fo5yvwtWuj8jA341mvv77spPcMZqBmec` |
| token standard, reference token | `token-standard` | `3Ty4ENxJ4EicohgXi9E2txgbqMh3DWSshPrtXxY8pksm` | `d298726f145773c834ba9ccc2a847f0de75636a760c04880d47ce051ab3f1794` (`token-standard/`) | `7cnk2Urb64ELBVouhACmznGw4rLqgyNjjXwRc4NHZaVf` |
| upgrade window, reference vault | `upgrade-window` | `7m2GRykdzJxaH4r8fmjZg5BJnVvvkKFqDm55GcLLfdPv` | `2c6d223219be21901e6fe3231e5b3fb780e71b8e204c56c20669b2c5a7d67439` (`upgrade-window/`) | `BpAq7sGTnFFfJoRQn3RcUya3qkXGny6EydeVbTTrZg7K` |

Registry made keyless (its only access key deleted; `near list-keys registry.exitproof.near` returns `[]`):
`F6ypQV24ZzofmRncQhZMkTaRb5HY2mfgdUSdq8CowCam`. Later attestations are method calls by an attestor account and need
no key on the registry.

A bundle hash is valid for the directory contents at the time of attestation; a later change to a proof directory
needs a new attestation (the old record stays readable, and can be marked revoked by its attestor).

Everything read from mainnet for the scanner, the censuses and the live pool check is read-only RPC.

## Stage-1 examples on NEAR testnet (`tools/stage1_demo.sh`, 2026-11-12)

The reference vault of `upgrade-window/` (code hash `7m2GRykdzJxaH4r8fmjZg5BJnVvvkKFqDm55GcLLfdPv`, the hash certified
in the mainnet registry) with a staging delay of 7 days. The vault accounts have no access keys; the only party
that can stage and deploy code is the holder of the `DAO` role, `gov.exitproof-demo.testnet`.

| Account | State | Transactions |
|---|---|---|
| `quiet-vault.exitproof-demo.testnet` | no code staged; exit window 7 days | deploy + `new` `BoSySi3WYVppwc5nkT6hDPetPnrUBpRa1KRDz6tPgV6w`, key deleted `BR44GVGLG6uPVJPBurRRZr9WJYjhm2tSY8AgnbawXC6t` |
| `staged-vault.exitproof-demo.testnet` | code `Cq3X1GtMCfYsrbjnpWj96jbi642iKRoZxXJ6HJyh3g5X` staged; no deploy before 2026-11-19 17:47:15 UTC | deploy + `new` `HMcBvf5neLDEfbUJNs9LCbhJGp49qMD58yzQMLLGm93s`, key deleted `JDAPwBCcprG7SpPyTKQ3BAgwnQA1zAGhxsWT2q8U2XgC`, `up_stage_code` `ftQc7MT9t6HxRxF6ERsgMVZFxtRR5iG9jL3qeddmNUa` |

