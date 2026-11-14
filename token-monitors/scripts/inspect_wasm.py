#!/usr/bin/env python3
"""inspect_wasm.py TOKEN.wasm: the hashes of a wasm file and the methods it exports."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kitlib  # noqa: E402

if len(sys.argv) != 2:
    print(__doc__); sys.exit(3)
data = open(sys.argv[1], "rb").read()
try:
    exports = kitlib.wasm_exports(data)
except (ValueError, IndexError) as e:
    print(f"{sys.argv[1]}: {e}", file=sys.stderr); sys.exit(3)
std = kitlib.NEP141 + ["ft_resolve_transfer"] + kitlib.NEP145 + kitlib.NEP148
print(f"file            {sys.argv[1]} ({len(data)} bytes)")
print(f"sha256          {kitlib.sha256_bytes(data)}")
print(f"NEAR code hash  {kitlib.near_code_hash(data)}")
print("standard methods present:  " + (", ".join(m for m in std if m in exports) or "none"))
print("standard methods missing:  " + (", ".join(m for m in std if m not in exports) or "none"))
other = [m for m in exports if m not in std]
print("other exported methods:    " + (", ".join(other) or "none"))
likely = [m for m in other if m.startswith(("new", "init")) or m in ("initialize", "migrate")]
print("likely init methods:       " + (", ".join(m for m in likely if m != "migrate") or "none recognised by name"))
if "ft_resolve_transfer" not in exports:
    print("note: no ft_resolve_transfer export; if the settlement callback has another name, set `resolve_method` in the config")
