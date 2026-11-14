"""Deterministic hash of the proof bundle of this kit, used as `artifact_sha256` in a certificate.

usage: python3 scripts/bundle_hash.py [--list]
The bundle is every regular file under contract/, lean/ and harness/ except build products
(directories .lake, target, build, __pycache__). The hash is sha256 over the lines
"<relative path>\t<sha256 of file>\n", sorted by path — the scheme of the exit-proof registry's
tools/bundle_hash.py. --list prints those lines.
"""
import hashlib
import os
import sys

KIT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PARTS = ("contract", "lean", "harness")
EXCLUDE_DIRS = {".lake", "target", "build", "__pycache__"}


def lines():
    out = []
    for part in PARTS:
        for d, dirs, fs in os.walk(os.path.join(KIT, part)):
            dirs[:] = sorted(x for x in dirs if x not in EXCLUDE_DIRS)
            for f in sorted(fs):
                p = os.path.join(d, f)
                if os.path.isfile(p) and not os.path.islink(p):
                    rel = os.path.relpath(p, KIT).replace(os.sep, "/")
                    out.append((rel, hashlib.sha256(open(p, "rb").read()).hexdigest()))
    return sorted(out)


def bundle_hash():
    h = hashlib.sha256()
    ls = lines()
    for rel, fh in ls:
        h.update(f"{rel}\t{fh}\n".encode())
    return h.hexdigest(), len(ls)


if __name__ == "__main__":
    if "--list" in sys.argv:
        for rel, fh in lines():
            print(f"{rel}\t{fh}")
    d, n = bundle_hash()
    print(d, n, "files")
