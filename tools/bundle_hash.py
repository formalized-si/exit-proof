"""Deterministic hash of a proof directory, used as `artifact_sha256` in registry certificates.

usage: bundle_hash.py <directory> [--list] [--git]
The hash is sha256 over the lines "<relative path>\t<sha256 of file>\n", sorted by path, for every regular file
under the directory except build products and raw run outputs (see EXCLUDE_*). Anyone with a checkout of the
repository can recompute it and compare with the value stored on chain.

--git hashes the directory as committed at HEAD instead of the working tree. Use it after running a check.sh:
the checks rewrite their run logs (timings, build paths) inside the directory, and the working tree then no longer
hashes to the attested value although nothing that was attested has been edited.
"""
import fnmatch
import hashlib
import os
import sys

# "runs", "mutants" and "plugin" are working directories that upgrade-window/check.sh creates
EXCLUDE_DIRS = {".lake", "target", "build", "__pycache__", "node_modules", ".git", "runs", "mutants", "plugin"}
EXCLUDE_FILES = ["*.olean", "*.ilean", "*.pyc", ".DS_Store", "out/traces*", "out/model*", "out/*.jsonl", "out/*.log"]


def files(root):
    for d, dirs, fs in os.walk(root):
        dirs[:] = sorted(x for x in dirs if x not in EXCLUDE_DIRS)
        for f in sorted(fs):
            rel = os.path.relpath(os.path.join(d, f), root).replace(os.sep, "/")
            if any(fnmatch.fnmatch(rel, pat) or fnmatch.fnmatch(f, pat) for pat in EXCLUDE_FILES):
                continue
            if os.path.isfile(os.path.join(d, f)) and not os.path.islink(os.path.join(d, f)):
                yield rel


def bundle_hash(root):
    h = hashlib.sha256()
    n = 0
    for rel in sorted(files(root)):
        fh = hashlib.sha256(open(os.path.join(root, rel), "rb").read()).hexdigest()
        h.update(f"{rel}\t{fh}\n".encode())
        n += 1
    return h.hexdigest(), n


def git_bundle_hash(root):
    """The same hash over the directory's files as committed at HEAD."""
    import io
    import subprocess
    import tarfile
    root = os.path.realpath(root)
    try:
        top = os.path.realpath(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=root, text=True,
                                                       stderr=subprocess.DEVNULL).strip())
        prefix = os.path.relpath(root, top).replace(os.sep, "/")
        data = subprocess.check_output(["git", "archive", "HEAD", "--", prefix], cwd=top, stderr=subprocess.DEVNULL)
    except (subprocess.CalledProcessError, OSError):
        sys.exit("--git hashes the directory as committed at HEAD: it needs a git checkout of this repository and the "
                 "git command. Without --git the working tree is hashed, which equals the attested hash only before "
                 "any check.sh has been run in the directory.")
    lines = []
    with tarfile.open(fileobj=io.BytesIO(data)) as tf:
        for m in tf:
            if not m.isreg():
                continue
            rel = os.path.relpath(m.name, prefix).replace(os.sep, "/")
            parts = rel.split("/")
            if any(p in EXCLUDE_DIRS for p in parts[:-1]):
                continue
            if any(fnmatch.fnmatch(rel, pat) or fnmatch.fnmatch(parts[-1], pat) for pat in EXCLUDE_FILES):
                continue
            lines.append((rel, hashlib.sha256(tf.extractfile(m).read()).hexdigest()))
    h = hashlib.sha256()
    for rel, fh in sorted(lines):
        h.update(f"{rel}\t{fh}\n".encode())
    return h.hexdigest(), len(lines)


if __name__ == "__main__":
    root = sys.argv[1]
    if "--list" in sys.argv:
        for rel in sorted(files(root)):
            print(rel)
    d, n = git_bundle_hash(root) if "--git" in sys.argv else bundle_hash(root)
    print(d, n, "files")
