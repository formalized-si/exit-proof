"""Audit of the scanner's method-name rules over a set of contract codes.

usage: name_audit.py <directory with *.wasm> [<directory> ...]     (default: the local cache codes/)

Without a certificate the scanner decides "no code-change path found" from the exported method names of a
contract. This script takes every distinct wasm file it is given, keeps those for which the name rules find no
code-change path, and prints every exported name in them that looks related to code, keys, votes or proposals.
A name in that list that does change the contract's own code is a hole in the rules: add it to CODE_RE in
exitproof.py and to NAMES in selftest.py. Run of 2026-11-13 over 115 distinct codes (the token census, the large
contracts, the accounts an independent reviewer sampled): 69 without a path by names, and no such name among them.
"""
import collections
import glob
import hashlib
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402

BROAD = re.compile(r"upgrad|deploy|migrat|code|vote|propos|request|confirm|_key|wasm|blob|factory|self_|set_contract|"
                   r"replace|install|stage|update_contract|contract_update", re.I)


def main(dirs):
    seen, files = set(), []
    for d in dirs:
        for p in sorted(glob.glob(os.path.join(d, "*.wasm"))):
            h = hashlib.sha256(open(p, "rb").read()).hexdigest()
            if h not in seen:
                seen.add(h)
                files.append(p)
    total = quiet = 0
    resid, example = collections.Counter(), {}
    for f in files:
        try:
            ex, _ = exitproof.wasm_tables(f)
        except Exception:
            continue
        total += 1
        s = set(ex)
        code = [e for e in ex if exitproof.CODE_RE.search(e) and not exitproof.NOT_SELF_CODE_RE.search(e)
                and not exitproof.MIGRATION_RE.search(e)]
        if code or {"add_proposal", "act_proposal"} <= s or {"add_request", "confirm"} <= s or "add_request_and_confirm" in s:
            continue
        quiet += 1
        for e in ex:
            if BROAD.search(e):
                resid[e] += 1
                example.setdefault(e, os.path.basename(f)[:16])
    print(f"{total} distinct codes; {quiet} with no code-change path by names; exported names in them that look related:")
    for e, n in resid.most_common():
        print(f"  {n:4d}  {e}   (for example in {example[e]})")
    if not resid:
        print("  none")


if __name__ == "__main__":
    main(sys.argv[1:] or [exitproof.CODES])
