#!/usr/bin/env python3
"""The readable properties of near-contract-standards 5.29.0, bundled with their Lean proofs.

usage: properties.py write  LEAN_DIR OUT.json   regenerate properties.json from the Lean sources
       properties.py check  LEAN_DIR PROPS.json verify every statement hash against the sources

A theorem's statement text is everything from `theorem NAME` up to the `:=` that starts its
proof, with runs of whitespace collapsed to one space; its sha256 is what properties.json pins.
The model files' hashes are pinned too: a statement means what the model's definitions say.
"""
import hashlib
import json
import os
import re
import sys

STANDARD = "near-contract-standards 5.29.0: FungibleToken (NEP-141 core) + StorageManagement (NEP-145), as exposed by the near-sdk-rs fungible-token example (tag near-sdk-v5.29.0)"

PROPERTIES = [
    {
        "id": "P1",
        "title": "Conservation",
        "text": "In every reachable state, total_supply equals the sum of all account balances.",
        "lean": ["P1_conservation", "P1_inv_step"],
    },
    {
        "id": "P2",
        "title": "transfer_call settlement",
        "text": ("When the settlement callback of an ft_transfer_call of `amount` from a sender to a receiver runs, "
                 "whatever the receiver's ft_on_transfer did (returned any number, unparsable bytes, a value longer "
                 "than 42 bytes, or failed), the refund to the sender is at most `amount` and at most what the "
                 "receiver still holds; the receiver loses exactly the refund and no other account changes; if the "
                 "sender is still registered, the sender gains exactly the refund, so the sender + receiver total "
                 "and the supply are conserved; if the sender has unregistered, the refund is burned. In a "
                 "reachable state the callback cannot fail for arithmetic reasons."),
        "lean": ["P2_settlement", "P2_settlement_call", "P2_settlement_never_fails"],
    },
    {
        "id": "P3",
        "title": "Callback ownership",
        "text": ("ft_resolve_transfer takes effect only as the token's own settlement callback: called by any other "
                 "account, by another contract, as another contract's callback with promise results of its choice, "
                 "or by a transaction signed with the token account's own key, it fails and changes nothing."),
        "lean": ["P3_callback_private", "P3_callback_private_sys"],
    },
    {
        "id": "P4",
        "title": "Balance ownership",
        "text": ("No step other than a call by the holder lowers the holder's balance, except the settlement of an "
                 "ft_transfer_call made to that holder, which takes back at most the amount of that transfer. The "
                 "holder's own calls that can lower it are exactly ft_transfer, ft_transfer_call and "
                 "storage_unregister(force = true); a settlement in flight exists only for a transfer that "
                 "credited the holder exactly that amount."),
        "lean": ["P4_balance_ownership", "P4_who_can_lower", "P4_pending_origin"],
    },
    {
        "id": "P5",
        "title": "Storage",
        "text": ("storage_unregister with 1 yoctoNEAR: with force = true it removes the caller's account and burns its "
                 "whole balance (total_supply drops by exactly that balance) and pays the caller the storage minimum "
                 "plus 1 yoctoNEAR; with a zero balance it does the same with or without force and burns nothing; "
                 "without force and with a positive balance it fails and changes nothing; for an unregistered "
                 "caller it changes nothing and returns false. storage_deposit registers an account for exactly the "
                 "storage minimum and refunds the rest to the caller. In every reachable state the token holds "
                 "enough NEAR for its base storage plus one storage refund per registered account."),
        "lean": ["P5_unregister_force", "P5_unregister_zero", "P5_unregister_refused", "P5_unregister_unknown",
                 "P5_storage_deposit", "P5_storage_solvent"],
    },
]

MODEL_FILES = ["ProvedFT/Map.lean", "ProvedFT/Model.lean", "ProvedFT/Lemmas.lean", "ProvedFT/Theorems.lean"]


def sha(s):
    return hashlib.sha256(s.encode() if isinstance(s, str) else s).hexdigest()


def statements(theorems_src):
    out = {}
    for m in re.finditer(r"^theorem\s+(\S+)", theorems_src, re.M):
        name = m.group(1)
        rest = theorems_src[m.start():]
        end = rest.index(":=")
        out[name] = " ".join(rest[:end].split())
    return out


def build(lean_dir):
    src = open(os.path.join(lean_dir, "ProvedFT/Theorems.lean")).read()
    stm = statements(src)
    props = []
    for p in PROPERTIES:
        thms = []
        for n in p["lean"]:
            if n not in stm:
                raise SystemExit(f"theorem {n} not found in Theorems.lean")
            thms.append({"name": f"ProvedFT.{n}", "statement": stm[n], "statement_sha256": sha(stm[n])})
        props.append({"id": p["id"], "title": p["title"], "text": p["text"], "text_sha256": sha(p["text"]),
                      "theorems": thms})
    files = {f: sha(open(os.path.join(lean_dir, f), "rb").read()) for f in MODEL_FILES}
    toolchain = open(os.path.join(lean_dir, "lean-toolchain")).read().strip()
    return {"standard": STANDARD, "lean_toolchain": toolchain, "lean_files_sha256": files, "properties": props}


def main():
    mode, lean_dir, path = sys.argv[1], sys.argv[2], sys.argv[3]
    cur = build(lean_dir)
    if mode == "write":
        with open(path, "w") as f:
            json.dump(cur, f, indent=1)
            f.write("\n")
        print(f"wrote {path}: {sum(len(p['theorems']) for p in cur['properties'])} theorems")
        return 0
    pinned = json.load(open(path))
    bad = []
    for p0, p1 in zip(pinned["properties"], cur["properties"]):
        for t0, t1 in zip(p0["theorems"], p1["theorems"]):
            if t0["statement_sha256"] != t1["statement_sha256"]:
                bad.append(f"{t0['name']}: statement changed")
    for f, h in pinned["lean_files_sha256"].items():
        if cur["lean_files_sha256"].get(f) != h:
            bad.append(f"{f}: file changed")
    print(json.dumps({"ok": not bad, "problems": bad}))
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
