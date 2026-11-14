# Background: why "can I get my money back?" needs a proof

## The question, in the words of people who run NEAR

- "Now we need to actually prove like the property you really care. Like if I put money into the smart contract, I can
  withdraw it back, right? … which by the way requires that the smart contract is not upgradable because otherwise the
  whoever has upgrade key can upgrade to a new version that can steal the money." — Illia Polosukhin, 2026-11-06
  ([video](https://www.youtube.com/watch?v=xpou72TAJ-s)).
- "NEAR is very heavily investing in formal verification efforts. Our ultimate goal is to formally prove the protocol and
  all the core contracts, and to provide a practical tool for others to formally verify their contracts in a fast and
  affordable way." — Illia Polosukhin, 2026-10-02
  ([post](https://x.com/ilblackdragon/status/2106094405564408006)).
- "Formally verified dependencies are needed, but then properties expression need to be readable and bundled with code."
  — Illia Polosukhin, 2026-11-06 ([post](https://x.com/ilblackdragon/status/2118513421272613012)).
- "Developers must also establish that the model accurately represents the relevant behavior of the deployed software."
  — near.org, "Formal verification 101", 2026-10-16.
- NEAR Intents post-mortem, 2026-10-16: "Please follow the advancements of formal verification, so you can secure your
  contracts even more in the future." ([post](https://x.com/AlexAuroraDev/status/2111124226962870770))

## What went wrong in 2026

| Event | Loss | Relevance |
|---|---|---|
| SWEAT token, 2026-04-29 | $3.5M | the caller check of `ft_resolve_transfer` was gone after a code upgrade; the token account has no full-access keys, so an explorer would have called it "locked" ([Fireblocks write-up, 2026-06-16](https://www.fireblocks.com/blog/near-zero-day-sweat-hot-token-exploit)). Read from an archival RPC: the account's code hash changed at block 195 422 580 (2026-04-24 17:12 UTC); a view-call probe of `ft_resolve_transfer` rejects a foreign caller before that block and not after it |
| NEAR Intents, 2026-09-29 … 10-01 | $3.8M | a gap between the two steps of a `*_transfer_call` deposit ([near/intents PR #362](https://github.com/near/intents/pull/362)) |

Both are in the asynchronous two-step token flow. The first is in the NEP-141 `ft_transfer_call` flow, which the
token-standard proofs in this repository cover, and it was an upgrade that took effect with no notice period. The
second was on the multi-token (NEP-245) deposit path of NEAR Intents: `intents-proof/` proves the fungible-token
paths of that contract and has no theorem for that path.

## What existing tools show

- Explorers show whether an account has full-access keys. NearBlocks adds the caveat itself: "This account has no full
  access keys. The contract may still be upgradable through a privileged method."
- Upgrade watchers alert after the code hash has changed.
- NEAR's own tooling (near-contract-sim, near-tla) helps developers test and model-check their own contracts.

None of these tells a depositor, before the deposit, whether an exit is guaranteed, or how long they would have to
leave if the code is about to change. That is the gap Exit Proof fills: a stage per contract, each stage backed by
checkable evidence.

## Questions integrators already ask

- "Is there a reproducible-build attestation tying the deployed WebAssembly to a named tag?"
  ([Near-One/btc-bridge#78](https://github.com/Near-One/btc-bridge/issues/78), 2026-09-21)
- "Which currently deployed contracts and versions does this [audit] cover?"
  ([gov.near.org/t/42679](https://gov.near.org/t/42679), 2026-10-12)
