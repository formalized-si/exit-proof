#!/usr/bin/env python3
"""Builds the reference token and its mutants with cargo-near.

usage: build.py OUT_DIR [ids...]

Writes OUT_DIR/wasm/<id>.wasm for `reference` (token/ as it is: the near-sdk-rs fungible-token
example with near-contract-standards 5.29.0) and for every entry of mutants.json (the same token
with one line changed in a copy of the library or of the token) and for the test fixtures listed
there (the same token with added methods), and OUT_DIR/build.json with the sha256 of each. A build is skipped when its wasm is already there and was made from the same
inputs. The library source is the crates.io release in the local cargo registry (cargo downloads
it if needed); the two files that get mutated are checked against the hashes in mutants.json.

Environment: TOKEN_TARGET_DIR (cargo target directory for the wasm builds; default OUT_DIR/target).
Needs: cargo, cargo-near, the Rust toolchain of token/rust-toolchain.toml with wasm32-unknown-unknown.
Exit status: 0 iff every build succeeded and all wasm files differ from each other.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOKEN = os.path.join(HERE, "token")
# The registry path of the build that defines the reference hash; rustc embeds the registry path in
# panic locations, so this machine's path is mapped to it.
PINNED_REGISTRY = "/home/ubuntu/.cargo/registry/src"


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def run(cmd, cwd, env):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)


def main():
    if len(sys.argv) < 2:
        print(__doc__); return 2
    out = os.path.abspath(sys.argv[1])
    only = set(sys.argv[2:])
    spec = json.load(open(os.path.join(HERE, "mutants.json")))
    lib_name = spec["library"]
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = env.get("TOKEN_TARGET_DIR") or os.path.join(out, "target")
    os.makedirs(os.path.join(out, "wasm"), exist_ok=True)
    md = run(["cargo", "metadata", "--format-version", "1", "--locked"], TOKEN, env)
    if md.returncode != 0:
        print("cargo metadata failed:\n" + md.stderr[-1500:]); return 1
    lib = None
    for p in json.loads(md.stdout)["packages"]:
        if f"{p['name']}-{p['version']}" == lib_name:
            lib = os.path.dirname(p["manifest_path"])
    if not lib:
        print(f"{lib_name} is not among the token's dependencies"); return 1
    registry = os.path.dirname(os.path.dirname(lib))
    for key, want in spec["sources_sha256"].items():
        where, rel = key.split(":", 1)
        got = sha(os.path.join(lib if where == "library" else TOKEN, rel))
        if got != want:
            print(f"{key}: sha256 {got}, mutants.json says {want}"); return 1
    inputs = hashlib.sha256()
    for rel in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "src/lib.rs"):
        inputs.update(sha(os.path.join(TOKEN, rel)).encode())
    builds = [{"id": "reference", "in": None, "old": None, "what": "the near-sdk-rs fungible-token example, near-contract-standards 5.29.0"}]
    builds += spec["mutants"] + spec.get("fixtures", [])
    results, failed = [], []
    for b in builds:
        mid = b["id"]
        if only and mid not in only:
            continue
        wasm = os.path.join(out, "wasm", mid + ".wasm")
        stamp = hashlib.sha256(inputs.hexdigest().encode() + json.dumps(b, sort_keys=True).encode()).hexdigest()
        stamp_file = wasm + ".inputs"
        if os.path.exists(wasm) and os.path.exists(stamp_file) and open(stamp_file).read().strip() == stamp:
            results.append({"id": mid, "sha256": sha(wasm), "bytes": os.path.getsize(wasm), "built": "earlier, same inputs"})
            print(f"{mid}: already built ({results[-1]['sha256'][:12]})", flush=True)
            continue
        d = os.path.join(out, "src", mid)
        shutil.rmtree(d, ignore_errors=True)
        os.makedirs(d)
        tok = os.path.join(d, "token")
        shutil.copytree(TOKEN, tok, ignore=shutil.ignore_patterns("target"))
        cmd = ["cargo", "near", "build", "non-reproducible-wasm", "--no-abi", "--out-dir", os.path.join(d, "out")]
        target = None
        if b["in"] == "library":
            shutil.copytree(lib, os.path.join(d, lib_name))
            with open(os.path.join(tok, "Cargo.toml"), "a") as f:
                f.write(f'\n[patch.crates-io]\nnear-contract-standards = {{ path = "../{lib_name}" }}\n')
            target = os.path.join(d, lib_name, b["file"])
        elif b["in"] == "token":
            target = os.path.join(tok, b["file"])
        else:
            cmd += ["--env", f"RUSTFLAGS=-C link-arg=-s --remap-path-prefix={registry}={PINNED_REGISTRY}"]
        edits = b.get("edits") or ([{"old": b["old"], "new": b["new"]}] if b.get("old") is not None else [])
        bad_edit = False
        for e in edits:
            src = open(target).read()
            if src.count(e["old"]) != 1:
                print(f"{mid}: the text to change occurs {src.count(e['old'])} times", flush=True)
                bad_edit = True; break
            open(target, "w").write(src.replace(e["old"], e["new"]))
        if bad_edit:
            failed.append(mid); continue
        r = run(cmd, tok, env)
        built = os.path.join(d, "out", "fungible_token.wasm")
        if r.returncode != 0 or not os.path.exists(built):
            print(f"{mid}: build failed\n" + (r.stdout + r.stderr)[-2000:], flush=True)
            failed.append(mid); continue
        shutil.copyfile(built, wasm)
        open(stamp_file, "w").write(stamp + "\n")
        shutil.rmtree(d, ignore_errors=True)
        results.append({"id": mid, "sha256": sha(wasm), "bytes": os.path.getsize(wasm), "built": "now"})
        print(f"{mid}: built ({results[-1]['sha256'][:12]}, {results[-1]['bytes']} bytes)", flush=True)
    hashes = [r["sha256"] for r in results]
    if len(set(hashes)) != len(hashes):
        print("two builds produced the same wasm"); failed.append("duplicate wasm")
    if not only:
        json.dump(results, open(os.path.join(out, "build.json"), "w"), indent=1)
    if failed:
        print("FAILED: " + ", ".join(failed)); return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
