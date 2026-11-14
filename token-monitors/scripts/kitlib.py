"""Shared helpers of the kit: hashes, the config format, wasm exports, the bundle hash."""
import base64
import binascii
import hashlib
import json
import os
import re

KIT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The accounts of the simulated world (the same names are compiled into harness/src/main.rs).
USERS = ["owner.near", "alice.near", "bob.near", "c1.near", "a" * 59 + ".near"]
RECEIVERS = ["recv1.near", "recv2.near"]
HOSTILE = "evil.near"
NEVER_CREATED = "ghost.near"
DEFAULT_TOKEN = "token.near"

NEP141 = ["ft_transfer", "ft_transfer_call", "ft_total_supply", "ft_balance_of"]
NEP145 = ["storage_deposit", "storage_withdraw", "storage_unregister", "storage_balance_bounds", "storage_balance_of"]
NEP148 = ["ft_metadata"]

TOP_KEYS = {
    "description", "token_account", "accounts", "init", "setup", "stubs", "funder", "track",
    "token_near", "timestamp_ns", "transfer_memos", "resolve_method",
}
INIT_KEYS = {"caller", "method", "args", "args_base64", "deposit", "gas_tgas"}
SETUP_KEYS = INIT_KEYS | {"receiver", "may_fail"}
ACCOUNT_RE = re.compile(r"^(([a-z\d]+[-_])*[a-z\d]+\.)*([a-z\d]+[-_])*[a-z\d]+$")
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha256_file(path):
    with open(path, "rb") as f:
        return sha256_bytes(f.read())


def b58encode(b):
    n = int.from_bytes(b, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + out


def near_code_hash(wasm_bytes):
    """The code hash NEAR shows for a contract: the sha256 of the wasm, base58."""
    return b58encode(hashlib.sha256(wasm_bytes).digest())


def canonical_json(v):
    return json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def config_sha256(cfg):
    """The identity of a config: sha256 of its JSON with sorted keys and no whitespace."""
    return sha256_bytes(canonical_json(cfg))


def is_account(s):
    return isinstance(s, str) and 2 <= len(s) <= 64 and ACCOUNT_RE.match(s) is not None


def _check_call(c, where, allowed, existing, token, errors):
    if not isinstance(c, dict):
        errors.append(f"{where}: must be an object"); return
    for k in sorted(set(c) - allowed):
        errors.append(f"{where}: unknown key `{k}` (known: {', '.join(sorted(allowed))})")
    if not isinstance(c.get("method"), str) or not c.get("method"):
        errors.append(f"{where}: `method` (a non-empty string) is required")
    for k in ("caller", "receiver"):
        if k in c and k in allowed:
            if not is_account(c[k]):
                errors.append(f"{where}: `{k}` is not a valid account id: {c[k]!r}")
            elif c[k] not in existing:
                errors.append(f"{where}: `{k}` {c[k]} does not exist in the simulated world; "
                              f"add it to `accounts` (existing: {', '.join(sorted(existing))})")
    if "args" in c and "args_base64" in c:
        errors.append(f"{where}: give `args` or `args_base64`, not both")
    if "args_base64" in c:
        try:
            if not isinstance(c["args_base64"], str):
                raise ValueError
            base64.b64decode(c["args_base64"], validate=True)
        except (ValueError, binascii.Error):
            errors.append(f"{where}: `args_base64` is not standard base64")
    if "deposit" in c and not (isinstance(c["deposit"], str) and c["deposit"].isdigit() and int(c["deposit"]) < 2 ** 128):
        errors.append(f"{where}: `deposit` must be yoctoNEAR as a decimal string, e.g. \"1\"")
    if "gas_tgas" in c and not (isinstance(c["gas_tgas"], int) and not isinstance(c["gas_tgas"], bool) and 1 <= c["gas_tgas"] <= 1000):
        errors.append(f"{where}: `gas_tgas` must be an integer from 1 to 1000")
    if "may_fail" in c and "may_fail" in allowed and not isinstance(c["may_fail"], bool):
        errors.append(f"{where}: `may_fail` must be true or false")


def validate_config(cfg):
    """Returns the list of problems of a config (empty: the config is well-formed)."""
    errors = []
    if not isinstance(cfg, dict):
        return ["the config must be a JSON object"]
    for k in sorted(set(cfg) - TOP_KEYS):
        errors.append(f"unknown key `{k}` (known: {', '.join(sorted(TOP_KEYS))})")
    builtin = set(USERS) | set(RECEIVERS) | {HOSTILE, NEVER_CREATED}
    token = cfg.get("token_account", DEFAULT_TOKEN)
    if not is_account(token):
        errors.append(f"`token_account` is not a valid account id: {token!r}")
    elif token in builtin:
        errors.append(f"`token_account` {token} is one of the accounts the simulated world already uses")
    if "description" in cfg and not isinstance(cfg["description"], str):
        errors.append("`description` must be a string")

    def acct_list(key, forbid):
        v = cfg.get(key, [])
        if not isinstance(v, list):
            errors.append(f"`{key}` must be a list of account ids"); return []
        out = []
        for a in v:
            if not is_account(a):
                errors.append(f"`{key}`: not a valid account id: {a!r}")
            elif a in forbid:
                errors.append(f"`{key}`: {a} is reserved by the simulated world")
            else:
                out.append(a)
        return out

    accounts = acct_list("accounts", {token, HOSTILE, NEVER_CREATED} | set(RECEIVERS))
    acct_list("track", set())
    stubs = cfg.get("stubs", [])
    stub_accounts = []
    if not isinstance(stubs, list):
        errors.append("`stubs` must be a list"); stubs = []
    for i, s in enumerate(stubs):
        w = f"stubs[{i}]"
        if not isinstance(s, dict):
            errors.append(f"{w}: must be an object"); continue
        for k in sorted(set(s) - {"account", "methods"}):
            errors.append(f"{w}: unknown key `{k}` (known: account, methods)")
        a = s.get("account")
        if not is_account(a):
            errors.append(f"{w}: `account` is not a valid account id: {a!r}")
        elif a in builtin or a == token or a in stub_accounts:
            errors.append(f"{w}: account {a} is already used")
        else:
            stub_accounts.append(a)
        m = s.get("methods")
        if not isinstance(m, dict) or not m:
            errors.append(f"{w}: `methods` must be an object: method name -> the JSON value it returns")
    existing = set(USERS) | set(RECEIVERS) | {HOSTILE, token} | set(accounts) | set(stub_accounts)
    if "init" in cfg:
        _check_call(cfg["init"], "init", INIT_KEYS, existing, token, errors)
    setup = cfg.get("setup", [])
    if not isinstance(setup, list):
        errors.append("`setup` must be a list of calls"); setup = []
    for i, c in enumerate(setup):
        _check_call(c, f"setup[{i}]", SETUP_KEYS, existing, token, errors)
    if "funder" in cfg:
        f = cfg["funder"]
        if not is_account(f):
            errors.append(f"`funder` is not a valid account id: {f!r}")
        elif f not in set(USERS) | set(accounts):
            errors.append(f"`funder` {f} must be one of the user accounts ({', '.join(USERS[:4])}, ...) or listed in `accounts`")
    tn = cfg.get("token_near", 50)
    if not (isinstance(tn, int) and not isinstance(tn, bool) and 1 <= tn <= 1_000_000):
        errors.append("`token_near` must be an integer number of NEAR from 1 to 1000000")
    ts = cfg.get("timestamp_ns", 0)
    if not (isinstance(ts, int) and not isinstance(ts, bool) and 0 <= ts < 2 ** 64):
        errors.append("`timestamp_ns` must be a non-negative integer (nanoseconds)")
    tm = cfg.get("transfer_memos", [])
    if not (isinstance(tm, list) and all(isinstance(x, str) for x in tm)):
        errors.append("`transfer_memos` must be a list of strings")
    rm = cfg.get("resolve_method", "ft_resolve_transfer")
    if not (isinstance(rm, str) and rm):
        errors.append("`resolve_method` must be a non-empty string")
    return errors


def load_config(path):
    """Reads and validates a config. Returns (config, errors)."""
    try:
        with open(path) as f:
            cfg = json.load(f)
    except (OSError, ValueError) as e:
        return None, [f"{path}: {e}"]
    return cfg, validate_config(cfg)


def wasm_exports(data):
    """The names of the functions a wasm module exports, sorted."""
    if data[:4] != b"\0asm":
        raise ValueError("not a wasm module (no \\0asm header)")

    def leb(p):
        r = s = 0
        while True:
            b = data[p]; p += 1
            r |= (b & 0x7F) << s; s += 7
            if not b & 0x80:
                return r, p

    pos, out = 8, []
    while pos < len(data):
        sid = data[pos]; pos += 1
        size, pos = leb(pos)
        if sid == 7:
            p = pos
            n, p = leb(p)
            for _ in range(n):
                ln, p = leb(p)
                name = data[p:p + ln].decode("utf-8", "replace"); p += ln
                kind = data[p]; p += 1
                _, p = leb(p)
                if kind == 0:
                    out.append(name)
        pos += size
    return sorted(out)


BUNDLE = [
    "VERSION", "certify.sh", "monitors/monitors.py",
    "harness/Cargo.toml", "harness/Cargo.lock", "harness/rust-toolchain.toml", "harness/src/main.rs",
    "scripts/env.sh", "scripts/build.sh", "scripts/check_config.py", "scripts/kitlib.py", "scripts/certificate.py",
]


def bundle_files():
    """The files that decide what a certificate run does (relative to the kit root)."""
    return sorted(BUNDLE)


def bundle_sha256():
    """One hash for the kit: sha256 over the lines "<sha256>  <path>" of bundle_files()."""
    h = hashlib.sha256()
    for r in bundle_files():
        h.update(f"{sha256_file(os.path.join(KIT_ROOT, r))}  {r}\n".encode())
    return h.hexdigest()


def kit_info():
    with open(os.path.join(KIT_ROOT, "VERSION")) as f:
        version = f.read().strip()
    lock = open(os.path.join(KIT_ROOT, "harness", "Cargo.lock")).read()
    sim = re.search(r'name = "near-contract-sim"\nversion = "([^"]+)"\nsource = "[^"#]*#([0-9a-f]+)"', lock)
    rt = re.search(r'name = "node-runtime"\nversion = "([^"]+)"\nsource = "[^"#]*#([0-9a-f]+)"', lock)
    return {
        "name": "token-monitors",
        "version": version,
        "bundle_sha256": bundle_sha256(),
        "simulator": f"near-contract-sim {sim.group(1)} (commit {sim.group(2)})" if sim else "unknown",
        "runtime": f"nearcore {rt.group(1)} (commit {rt.group(2)})" if rt else "unknown",
    }
