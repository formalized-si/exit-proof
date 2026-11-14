"""Writes a fresh ed25519 key file for a testnet account and prints the public key only.

usage: python3 testnet/mkkey.py <account id>
The file goes to ~/.near-credentials/testnet/<account id>.json with mode 0600; an existing file
is never overwritten. The private key is never printed. Needs the Python package `cryptography`.
"""
import json
import os
import sys

from cryptography.hazmat.primitives import serialization as s
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58(b):
    n = int.from_bytes(b, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = A[r] + out
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + out


account = sys.argv[1]
k = Ed25519PrivateKey.generate()
seed = k.private_bytes(s.Encoding.Raw, s.PrivateFormat.Raw, s.NoEncryption())
pub = k.public_key().public_bytes(s.Encoding.Raw, s.PublicFormat.Raw)
d = os.path.expanduser("~/.near-credentials/testnet")
os.makedirs(d, exist_ok=True)
p = os.path.join(d, account + ".json")
if os.path.exists(p):
    sys.exit(f"{p} exists; not overwriting")
fd = os.open(p, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
os.write(fd, json.dumps({"account_id": account, "public_key": "ed25519:" + b58(pub),
                         "private_key": "ed25519:" + b58(seed + pub)}).encode())
os.close(fd)
print("ed25519:" + b58(pub))
