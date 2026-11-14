#!/usr/bin/env python3
"""One hash for the sources that decide the results in evidence/: the Lean model, theorems and replay program, the
trace generator, the monitors, the scripts that run them, the TLA+ specification and the list of pinned wasm files.

usage: source_hash.py                       print the hash of the sources in this directory
       source_hash.py --stamp FILE ...      record in evidence/PROVENANCE.json that these evidence files were made
                                            from the present sources (run it right after the run that wrote them)
       source_hash.py --check               list the evidence files and whether each was made from the present sources

An evidence file quoted by a document should be of the present sources: ../tools/numbers_check.py fails when a file
it reads a headline number from is recorded with another hash. harness/build.sh is left out on purpose: it
only builds the harness and holds no rule that decides a result.
"""
import datetime
import glob
import hashlib
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PATTERNS = ["check.sh", "lean/*.lean", "lean/Intents/*.lean", "lean/IntentsW/*.lean", "lean/ProvedFT/*.lean",
            "lean/WNear/*.lean", "lean/lakefile.toml", "lean/lean-toolchain", "lean/lake-manifest.json", "lean/check.sh",
            "lean/kernel-check.sh", "lean/nanoda.json", "harness/src/*.rs", "harness/Cargo.toml", "harness/Cargo.lock",
            "harness/rust-toolchain.toml", "harness/run.sh", "harness/scripts/*.py", "harness/scripts/env.sh",
            "harness/wasm/SHA256SUMS", "scripts/*.sh", "scripts/*.py", "tla/*.tla", "tla/*.cfg", "tla/run.sh"]
PROVENANCE = os.path.join(ROOT, "evidence", "PROVENANCE.json")


def files(root=ROOT):
    out = set()
    for pat in PATTERNS:
        out.update(os.path.relpath(p, root) for p in glob.glob(os.path.join(root, pat)) if os.path.isfile(p))
    out.discard(os.path.join("scripts", "source_hash.py"))   # this script reads the sources; it decides no result
    return sorted(out)


def source_hash(root=ROOT):
    h = hashlib.sha256()
    for rel in files(root):
        with open(os.path.join(root, rel), "rb") as f:
            h.update(f"{hashlib.sha256(f.read()).hexdigest()}  {rel}\n".encode())
    return h.hexdigest()


def load():
    try:
        with open(PROVENANCE) as f:
            return json.load(f)
    except (OSError, ValueError):
        return {"files": {}}


if __name__ == "__main__":
    now = source_hash()
    if "--stamp" in sys.argv:
        d = load()
        for name in sys.argv[sys.argv.index("--stamp") + 1:]:
            name = os.path.basename(name)
            if not os.path.isfile(os.path.join(ROOT, "evidence", name)):
                sys.exit(f"no evidence/{name}")
            d["files"][name] = {"sources": now, "stamped_utc": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")}
        d["files"] = dict(sorted(d["files"].items()))
        with open(PROVENANCE, "w") as f:
            json.dump(d, f, indent=1)
            f.write("\n")
    elif "--check" in sys.argv:
        d = load()["files"]
        for name in sorted(os.listdir(os.path.join(ROOT, "evidence"))):
            if name == "PROVENANCE.json":
                continue
            rec = d.get(name)
            state = "no record" if rec is None else ("present sources" if rec["sources"] == now else
                                                     rec.get("note") or f"other sources ({rec['sources'][:12]}…)")
            print(f"{name:42} {state}")
    else:
        print(now)
