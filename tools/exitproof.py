"""Exit Proof scanner: the exit stage of a NEAR contract — who can change its code, who can move or freeze
other people's funds in it, and whether a proof of exit exists for its exact code.

usage: exitproof.py <account> [<account> ...] [--json] [--no-history] [--fast] [--network mainnet|testnet]
       --fast: the stage and its reasons only (a few reads); who holds each power is not read
       --no-history: the deployment history is read only where stage 2 depends on it
       exit status: 0 a report for every account, 1 an account was not found, 2 the chain could not be read

Read-only. Sources: public RPC (view_account, view_access_key_list, view_code,
call_function on view methods that the contract itself exports), NearBlocks
deployment history. Every statement in the report is tagged with where it came from:
  [chain]  read from current mainnet state
  [code]   read from the deployed wasm (export/import tables)
  [view]   returned by a view method of the contract (self-reported by its code)
  [hist]   deployment history (NearBlocks API)
  [proof]  machine-checked theorem registered for this exact code hash
  [name]   inferred from an exported method name only (heuristic, weakest)
"""
import base64
import hashlib
import json
import os
import re
import sys
import time
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rpc  # noqa: E402
from rpc import RpcUnavailable, call, is_unknown_account, q  # noqa: E402,F401

HERE = os.path.dirname(os.path.abspath(__file__))
CODES = os.environ.get("EXITPROOF_CODES", os.path.join(HERE, "..", "codes"))
PROOFS = os.path.join(HERE, "proofs.json")
# Attestors whose exit certificates count for stage 2. The registry keeps a certificate from any attestor its owner
# has admitted; which of them to believe is the reader's choice, made here and not on chain.
ATTESTORS = tuple(x for x in os.environ.get("EXITPROOF_ATTESTORS", "exitproof.near").split(",") if x)
# NEAR account ids: 2 to 64 characters, lower-case letters and digits in parts joined by "-" or "_", parts joined by "."
ACCOUNT_RE = re.compile(r"^(?=.{2,64}$)[a-z0-9]+([-_][a-z0-9]+)*(\.[a-z0-9]+([-_][a-z0-9]+)*)*$")
# Names of views: a method that only reads cannot pause, move, mint or hand over anything.
VIEW_RE = re.compile(r"^(is|get|has|view|list)_")

CODE_RE = re.compile(r"(^|_)(upgrade|deploy|set_code|stage_code|update_code|self_update)|^(state_)?migrate|(^|_)update_contract($|_code)|^up_(deploy_code|stage_code|init_staging_duration|stage_update_staging_duration|apply_update_staging_duration)$|add_full_access_key|attach_full_access_key|delete_account|^(submit|vote|propose)_(contract_)?update|(^|_)factory_update|(^|_)update($|_self$)|(^|_)set_wasm|store_code|code_update|apply_patch|(replace|install|swap|change)_code|set_contract_code", re.I)
# Names that match CODE_RE but do not change this contract's own code: views and callbacks, methods that deploy
# another contract (token factories), token metadata updates.
NOT_SELF_CODE_RE = re.compile(r"^(get|is|has)_|_callback$|deploy_.*token|deploy(ed|er|ment)|^upgrade_(name|icon|symbol)|^upgrade_.*_token$|^up_staged_code", re.I)
# Migration entry points run on code that is already deployed; alone they are not a code-change path.
MIGRATION_RE = re.compile(r"^(state_)?migrate(_(?!code|contract|deploy|upgrade)[a-z0-9]+)*$|^migrate_state$", re.I)
FUNDS_RE = re.compile(r"force|unrestricted|rescue|sweep|emergency|admin_(transfer|withdraw|call)|seize|confiscate|burn_from|withdraw_for|clawback|admin_call|do_auth_call", re.I)
FREEZE_RE = re.compile(r"(^|_)(pause|unpause)|pa_pause|blacklist|blocklist|denylist|deny_list|freeze|lock_account|account_lock|(^|_)ban(_|$)", re.I)
MINT_RE = re.compile(r"(^|_)mint(_|$)", re.I)
OWNER_RE = re.compile(r"set_owner|change_owner|transfer_owner|own_set_owner|own_propose|acl_grant|acl_add_super_admin|acl_add_admin|set_admin|add_admin|add_guardian|set_guardian", re.I)
# Role classes. Known role names first, regex fallback second. Recovery roles
# (Unpause*, *Unlocker) are not a threat to a depositor and are not counted.
ROLE_CLASS = {
    "code": {"Upgrader", "UpgradeManager", "StagingManager", "UpgradableCodeStager", "UpgradableCodeDeployer",
             "CodeStager", "CodeDeployer", "DurationManager"},
    "funds": {"UnrestrictedWithdrawer", "UnrestrictedAccountManager", "TreasuryManager", "Rescuer", "Withdrawer"},
    "freeze": {"PauseManager", "UnrestrictedAccountLocker", "DenylistManager", "BlacklistManager", "FreezeManager"},
}
ROLE_RE = {
    "code": re.compile(r"upgrad|deploy|stag|code", re.I),
    "funds": re.compile(r"withdraw|rescue|treasur|account_?manager|transfer|sweep", re.I),
    "freeze": re.compile(r"(?<!un)pause|(?<!un)lock(?!er.*un)|deny|black|freez", re.I),
}
BENIGN_RE = re.compile(r"^un(pause|lock)|unlocker|unpause", re.I)


def role_class(role):
    for c, names in ROLE_CLASS.items():
        if role in names:
            return c
    if BENIGN_RE.search(role):
        return None
    for c, rx in ROLE_RE.items():
        if rx.search(role):
            return c
    return None
# The deployment history: NearBlocks lists the first and the latest code deployment of an account. API v3 first;
# v1 (retired on testnet, switched off on mainnet on 2026-11-22) as a fallback. EXITPROOF_INDEXER replaces the base.
INDEXER = {"mainnet": os.environ.get("EXITPROOF_INDEXER", "https://api.nearblocks.io"),
           "testnet": os.environ.get("EXITPROOF_INDEXER", "https://api-testnet.nearblocks.io")}

def view(acc, method, args=None, eps=None):
    r = q("call_function", account_id=acc, method_name=method,
          args_base64=base64.b64encode(json.dumps(args or {}).encode()).decode(), eps=eps)
    res = r.get("result", {})
    if isinstance(res, dict) and "result" in res:
        raw = bytes(res["result"]).decode(errors="replace")
        try:
            return True, json.loads(raw)
        except Exception:
            return True, raw
    return False, (res.get("error") if isinstance(res, dict) else None) or r.get("error")


def account(acc):
    j = q("view_account", account_id=acc)
    if "result" in j:
        return j["result"]
    if is_unknown_account(j):
        return None
    raise RpcUnavailable(f"view_account: {json.dumps((j.get('error') or {}).get('name'))}")


def keys(acc):
    """All access keys of an account. The RPC answers TOO_MANY_ACCESS_KEYS for accounts with more than 100 keys
    unless the request is paginated (`limit`, then `after_key` = the previous page's `last_key`); every page is
    read at the block of the first one."""
    out, after, block = [], None, None
    for _ in range(200):
        kw = {"account_id": acc, "limit": 100}
        if after:
            kw["after_key"] = after
        j = q("view_access_key_list", block_id=block, **kw)
        if "result" not in j:
            # every caller has read the account first: "unknown account" here contradicts that read (an endpoint that
            # lags or fails), and an empty key list taken from it would read as "no keys"
            raise RpcUnavailable("view_access_key_list" + (": the account was not found by this read, although it exists"
                                                           if is_unknown_account(j) else ""))
        res = j["result"]
        for k in res.get("keys", []):
            p = k["access_key"]["permission"]
            if p == "FullAccess":
                out.append({"key": k["public_key"], "full": True})
            else:
                fc = p["FunctionCall"]
                out.append({"key": k["public_key"], "full": False, "receiver": fc["receiver_id"],
                            "methods": fc["method_names"], "allowance": fc.get("allowance")})
        after = res.get("last_key")
        block = block or res.get("block_height")
        if not after:
            break
    else:
        # a partial list could miss the one key that matters: no list, no verdict
        raise RpcUnavailable("view_access_key_list: more than 20 000 keys, the list was not read to its end")
    return out


EMPTY = "11111111111111111111111111111111"


def effective_code(a):
    """(hash, how) of the code that actually runs on an account."""
    if a.get("global_contract_account_id"):
        return None, "global_by_account"
    if a.get("global_contract_hash"):
        return a["global_contract_hash"], "global_by_hash"
    if a.get("code_hash") and a["code_hash"] != EMPTY:
        return a["code_hash"], "own"
    return None, "none"


B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def code_hash_of(data):
    """NEAR's code hash of a wasm: base58 of its sha256 (each leading zero byte is a leading "1")."""
    digest = hashlib.sha256(data).digest()
    n = int.from_bytes(digest, "big")
    s = ""
    while n:
        n, r = divmod(n, 58)
        s = B58[r] + s
    return "1" * (len(digest) - len(digest.lstrip(b"\0"))) + s


def wasm_path(acc, a):
    """The wasm that runs on the account, from the local cache or the RPC. The bytes are checked against the code
    hash the account names before they are used or kept: the method list is read from these bytes, and bytes of
    other code would give the verdict of other code."""
    os.makedirs(CODES, exist_ok=True)
    h, how = effective_code(a)
    if how == "none":
        return None, None
    if h:
        p = os.path.join(CODES, h + ".wasm")
        if os.path.exists(p):
            with open(p, "rb") as f:
                if code_hash_of(f.read()) == h:
                    return p, h
            os.remove(p)   # a cached file that is not the code it is named after
    r = q("view_code", account_id=acc).get("result")
    if not r and how == "global_by_hash":
        r = q("view_global_contract_code", code_hash=h).get("result")
    if not r and how == "global_by_account":
        r = q("view_global_contract_code_by_account_id", account_id=a["global_contract_account_id"]).get("result")
    if not r:
        return None, h
    data = base64.b64decode(r["code_base64"])
    got = code_hash_of(data)
    want = h or r.get("hash")
    if want and got != want:
        # the code can change between two reads; either way these bytes are not the code the account named
        raise RpcUnavailable(f"the code returned ({got[:10]}…) is not the code the account names ({want[:10]}…)")
    h = want or got
    p = os.path.join(CODES, h + ".wasm")
    with open(p, "wb") as f:
        f.write(data)
    return p, h


def _leb(b, i):
    """Unsigned LEB128 at b[i:]; returns (value, next index)."""
    r = shift = 0
    while True:
        x = b[i]
        i += 1
        r |= (x & 0x7F) << shift
        if not x & 0x80:
            return r, i
        shift += 7


def _name(b, i):
    n, i = _leb(b, i)
    return b[i:i + n].decode("utf-8", "replace"), i + n


def wasm_tables(p):
    """Exported function names and imported `env` function names of a wasm module (pure Python, no external tool)."""
    b = open(p, "rb").read()
    if b[:4] != b"\0asm":
        raise ValueError(f"{p}: not a wasm module")
    exports, imports = [], []
    i = 8
    while i < len(b):
        sid = b[i]
        size, i = _leb(b, i + 1)
        end = i + size
        if sid == 2:  # import section
            n, j = _leb(b, i)
            for _ in range(n):
                mod, j = _name(b, j)
                field, j = _name(b, j)
                kind = b[j]
                j += 1
                if kind == 0:  # function: type index
                    _, j = _leb(b, j)
                    if mod == "env":
                        imports.append(field)
                elif kind == 1:  # table: reftype + limits
                    j += 1
                    flags = b[j]
                    j += 1
                    _, j = _leb(b, j)
                    if flags & 1:
                        _, j = _leb(b, j)
                elif kind == 2:  # memory: limits
                    flags = b[j]
                    j += 1
                    _, j = _leb(b, j)
                    if flags & 1:
                        _, j = _leb(b, j)
                elif kind == 3:  # global: valtype + mutability
                    j += 2
                else:
                    raise ValueError(f"{p}: unsupported import kind {kind}")
        elif sid == 7:  # export section
            n, j = _leb(b, i)
            for _ in range(n):
                name, j = _name(b, j)
                kind = b[j]
                _, j = _leb(b, j + 1)
                if kind == 0:
                    exports.append(name)
        i = end
    return exports, imports


def _indexer_list(acc):
    base = INDEXER[rpc.NETWORK[0]]
    for path, key in ((f"/v3/accounts/{acc}/contract/deployments", "data"), (f"/v1/account/{acc}/contract/deployments", "deployments")):
        try:
            req = urllib.request.Request(base + path, headers={"User-Agent": "exitproof-readonly"})
            j = json.loads(urllib.request.urlopen(req, timeout=30).read())
        except Exception as e:
            err = str(e)[:120]
            continue
        rows = j.get(key)
        if not isinstance(rows, list):
            err = f"{path}: no list in the answer"
            continue
        return [{"tx": d["transaction_hash"],
                 "ts": int((d.get("block") or {}).get("block_timestamp") or d.get("block_timestamp")) // 10**9,
                 "by": d.get("predecessor_account_id") or d.get("receipt_predecessor_account_id")} for d in rows]
    raise RuntimeError(err)


def deployments(acc, attempts=3):
    """Code deployments of the account as the indexer lists them: the first and the latest (one row when there was
    one deployment), or {"error": …} when the indexer does not answer."""
    err = ""
    for i in range(attempts):
        try:
            return _indexer_list(acc)
        except Exception as e:
            err = str(e)[:120]
            if i + 1 < attempts:
                time.sleep(3 * (i + 1))   # the public indexer limits requests per minute
    return {"error": err}


def accepted_exit(certs):
    """The exit certificates among `certs` that come from an attestor this scanner accepts."""
    return [c for c in (certs or []) if cert_kind(c) == "exit" and c.get("attestor") in ATTESTORS]


def origin(rep):
    """Was the state of this account made by the certified code alone?

    An exit theorem speaks about states the proved code reaches from its own initialisation. A deployment keeps the
    storage of the account, so an account that ran other code before can hold a state the theorem says nothing
    about, under the certified code hash and with no keys left. The evidence taken here: the indexer lists exactly
    one code deployment for the account, or the proof entry names this account and lists exactly the deployments
    the proof report covers. Anything else, an unread history included, is no origin."""
    d = rep.get("deployments")
    if rep.get("code_source", "own") != "own":
        # the history lists deployments of the account's own code; a global contract by hash switches code with an
        # action this reading does not see, so which code wrote the state is not established
        return {"ok": False, "why": "the account runs a global contract, and the deployment history does not show which "
                                    "code wrote its state"}
    if not isinstance(d, list):
        return {"ok": False, "why": "the deployment history of the account was not read, so it is not established that "
                                    "its state was made by this code alone"}
    pinned = (((rep.get("proof") or {}).get("origin") or {}).get(rep["account"])) or {}
    if len(d) == 1:
        # the indexer's list holds the first and the latest deployment, so one row means one deployment
        when = time.strftime("%Y-%m-%d", time.gmtime(d[0]["ts"]))
        by = d[0].get("by")
        who = f", by {by} in the receipt that created the account" if by and by != rep["account"] else ""
        return {"ok": True, "deployments": 1,
                "why": f"one code deployment in the account's history ({when}{who}): its state was made by this code alone [hist]"}
    if pinned and len(d) >= 2:
        # The indexer's list holds the first and the latest deployment only. The deployments before the latest one are
        # in the past and cannot change: the proof records the full list, read once from every deployment receipt of
        # the account (`full_history`). If the latest deployment is still the one recorded, nothing came after it.
        full = pinned.get("full_history") or {}
        names = list(pinned.get("deployments") or [])   # in the order they happened
        listed = {x["tx"] for x in d}
        if not names or sorted(full.get("deployments") or []) != sorted(names):
            return {"ok": False, "why": "the account has had more than one code deployment, and the proof records no full "
                                        "list of them, so it is not established that they are the ones the proof covers"}
        if listed != {names[0], names[-1]}:
            return {"ok": False, "why": f"the indexer lists deployments {', '.join(t[:8] for t in listed)}, not the first and "
                                        f"the latest of the {len(names)} the proof covers: the code changed since"}
        return {"ok": True, "deployments": len(names),
                "why": f"{len(names)} code deployments in all ({full.get('read', 'read from every deployment receipt')}), the "
                       f"ones the proof report covers, and none since: {pinned.get('note', 'see the report')} [hist]"}
    if not d:
        return {"ok": False, "why": "the indexer lists no code deployment for the account, so it is not established "
                                    "that its state was made by this code alone"}
    return {"ok": False, "why": "the indexer lists more than one code deployment for the account (it shows the first and the "
                                "latest): its state may have been written by other code, and the theorem is about states "
                                "this code reaches from its own initialisation"}


def describe_controller(acc, depth=0):
    """What kind of thing is this controlling account, and who controls it."""
    a = account(acc)
    if a is None:
        return {"account": acc, "kind": "missing"}
    ks = keys(acc)
    d = {"account": acc, "full_access_keys": sum(1 for k in ks if k["full"]),
         "code_hash": a.get("code_hash")}
    h, how = effective_code(a)
    d["code"] = how
    if how == "none":
        d["kind"] = "plain account (keys only)"
        return d
    ok, pol = view(acc, "get_policy")
    if ok and isinstance(pol, dict) and "roles" in pol:
        roles = []
        for r in pol["roles"]:
            kind = r.get("kind")
            members = kind.get("Group") if isinstance(kind, dict) else kind
            vp = r.get("vote_policy") or {}
            roles.append({"name": r.get("name"), "members": members,
                          "permissions": r.get("permissions", [])[:12],
                          "vote_policy": vp or pol.get("default_vote_policy")})
        d["kind"] = "sputnik DAO"
        d["roles"] = roles
        d["default_vote_policy"] = pol.get("default_vote_policy")
        # The DAO contract's `update` method accepts new code from its factory, with no proposal, while the DAO's
        # `auto_update` flag is true (public source: sputnik-dao-contract, sputnikdao2/src/upgrade.rs). Such a DAO is
        # guarded no better than its factory account.
        ok, fi = view(acc, "get_factory_info")
        if ok and isinstance(fi, dict) and fi.get("auto_update") and fi.get("factory_id"):
            nk = sum(1 for k in keys(fi["factory_id"]) if k["full"])
            d["factory_auto_update"] = {"factory_full_access_keys": nk}
            d["factory_guard"] = "single-key" if nk == 1 else "multi-key account" if nk > 1 else "contract"
        return d
    ok, mem = view(acc, "get_members")
    if ok and isinstance(mem, list):
        ok2, n = view(acc, "get_num_confirmations")
        d["kind"] = "multisig"
        d["members"] = mem
        d["confirmations"] = n if ok2 else None
        return d
    d["kind"] = "contract"
    if depth == 0:
        p, _ = wasm_path(acc, a)
        if p:
            ex, _ = wasm_tables(p)
            d["exports_sample"] = [e for e in ex if CODE_RE.search(e) or FUNDS_RE.search(e) or OWNER_RE.search(e) or e.startswith(("acl_", "get_", "own_"))][:30]
            d["roles"] = roles_of(acc, ex)
            sub = set(d["roles"].get("super_admins") or [])
            for role, g in (d["roles"].get("grantees") or {}).items():
                sub.update(g or [])
            for v in (d["roles"].get("owners") or {}).values():
                if isinstance(v, str):
                    sub.add(v)
            sub.discard(acc)
            d["controlled_by"] = {c: describe_controller(c, 1) for c in sorted(sub)[:12]}
    return d


CALLBACK_RE = re.compile(r"(^|_)(resolve|callback)|^on_|^_|_private$")


def own_key_is_power(methods):
    """Does a function-call key on the contract's own account, limited to `methods`, let its holder do what an
    ordinary caller cannot? An empty list means every method."""
    if not methods:
        return True
    return any(CODE_RE.search(m) or FUNDS_RE.search(m) or FREEZE_RE.search(m) or OWNER_RE.search(m) or MINT_RE.search(m)
               or CALLBACK_RE.search(m) for m in methods)


def self_governed(acc, exports):
    """A DAO or a multisig decides about its own account: a proposal it passes, or a request its members confirm,
    can deploy code or add a key there. Returns the description of that guard, or None."""
    ex = set(exports)
    dao = {"add_proposal", "act_proposal"} <= ex
    msig = {"add_request", "confirm"} <= ex or "add_request_and_confirm" in ex
    if not (dao or msig):
        return None
    d = describe_controller(acc, depth=1)
    if d.get("kind") in ("sputnik DAO", "multisig"):
        return d
    return {"account": acc, "kind": "sputnik DAO" if dao else "multisig", "classified_by": "method names"}


def roles_of(acc, exports, holders=True):
    """holders=False: the role names are read, their holders are not (one read per role is saved); the stage does
    not depend on who holds a role, only the report of how strongly a power is guarded does."""
    out = {"unread": []}   # views the code exports that did not answer; a stage that depends on one is not given
    ex = set(exports)
    if "acl_role_variants" in ex:
        ok, variants = view(acc, "acl_role_variants")
        out["acl_roles"] = variants if ok else None
        if not (ok and isinstance(variants, list)):
            out["unread"].append("acl_role_variants")
        roles = variants if ok and isinstance(variants, list) else []
        if holders:
            ok, sa = view(acc, "acl_get_super_admins", {"skip": 0, "limit": 50})
            out["super_admins"] = sa if ok else None
        grantees = {}
        for role in roles:
            if holders:
                ok, g = view(acc, "acl_get_grantees", {"role": role, "skip": 0, "limit": 50})
                grantees[role] = g if ok else None
            else:
                grantees[role] = None
        out["grantees"] = grantees
    for m in ("own_get_owner", "get_owner_id", "get_owner", "owner_id", "get_owners", "get_guardians", "get_admins"):
        if m in ex:
            ok, v = view(acc, m)
            if ok:
                out.setdefault("owners", {})[m] = v
    if "get_factory_id" in ex:
        ok, v = view(acc, "get_factory_id")
        if ok and isinstance(v, str):
            out["factory"] = v
    if "pa_all_paused" in ex:
        ok, v = view(acc, "pa_all_paused")
        out["paused_features"] = v if ok else None
    if "up_staged_code_hash" in ex:
        ok, v = view(acc, "up_staged_code_hash")
        out["staged_code_hash"] = v if ok else None
        if not ok:
            out["unread"].append("up_staged_code_hash")
    # a certificate gate in front of the plugin's deploy (gated-upgrade/): the contract says which registry,
    # certificate kind and attestors it accepts
    if {"deploy_certified", "on_certificates", "gate"} <= set(ex):
        ok, v = view(acc, "gate")
        if ok and isinstance(v, dict) and v.get("registry"):
            out["gate"] = {"registry": v.get("registry"), "kind": v.get("kind"), "attestors": len(v.get("attestors") or [])}
        else:
            out["unread"].append("gate")
    if "up_get_delay_status" in ex:
        ok, v = view(acc, "up_get_delay_status")
        if ok and isinstance(v, dict):
            out["upgrade_delay_status"] = v
        else:
            out["unread"].append("up_get_delay_status")
    return out


REGISTRY = os.environ.get("EXITPROOF_REGISTRY", "registry.exitproof.near")


def registry_lookup(code_hash):
    """Valid certificates for this code hash from the on-chain registry (None if the registry cannot be read).
    The registry lives on mainnet and is keyed by code hash, so it is read from mainnet whatever network the
    scanned account is on: the same bytes have the same hash everywhere."""
    try:
        ok, v = view(REGISTRY, "get_valid", {"code_hash": code_hash},
                     eps=os.environ.get("EXITPROOF_REGISTRY_RPC", rpc.DEFAULT_RPC["mainnet"]).split(","))
    except RpcUnavailable:
        return None
    return v if ok and isinstance(v, list) else None


def load_proofs():
    try:
        with open(PROOFS) as f:
            return json.load(f)
    except Exception:
        return {}


def scan(acc, history=True, controllers=True):
    if not ACCOUNT_RE.match(acc or ""):
        return {"account": acc, "error": "not a NEAR account id (2 to 64 characters: lower-case letters, digits, '-', '_', '.')"}
    a = account(acc)
    if a is None:
        net = rpc.NETWORK[0]
        elsewhere = {"mainnet": (".testnet", "testnet"), "testnet": (".near", "mainnet")}[net]
        hint = f"; the name ends in {elsewhere[0]}: try --network {elsewhere[1]}" if acc.endswith(elsewhere[0]) else ""
        return {"account": acc, "error": f"account not found on {net}{hint}"}
    rep = {"account": acc, "balance": a["amount"], "locked": a["locked"], "code_hash": a["code_hash"],
           "storage_usage": a["storage_usage"],
           "global_contract_hash": a.get("global_contract_hash"),
           "global_contract_account_id": a.get("global_contract_account_id")}
    rep["keys"] = keys(acc)
    rep["full_access_keys"] = [k["key"] for k in rep["keys"] if k["full"]]
    eh, how = effective_code(a)
    rep["code_source"] = how
    rep["effective_code_hash"] = eh
    rep["has_code"] = how != "none"
    exports, imports = [], []
    if rep["has_code"]:
        p, eh2 = wasm_path(acc, a)
        rep["effective_code_hash"] = eh2 or eh
        if not p:
            # no method list means no verdict: an empty list would read as "nothing can change the code"
            raise RpcUnavailable("the contract's code could not be read")
        exports, imports = wasm_tables(p)
    rep["exports"] = exports
    # A function-call key on the contract's own account calls the contract as itself: private callbacks and
    # own-account-only methods accept it. A key limited to named methods counts only if one of them is a privileged
    # method or looks like a callback; a key limited to an ordinary public method (a relayer key) gives its holder
    # nothing that any caller does not have, and is only listed.
    own = [k for k in rep["keys"] if not k["full"] and k.get("receiver") == acc]
    rep["own_function_call_keys"] = [k["key"] for k in own if own_key_is_power(k.get("methods") or [])]
    rep["own_limited_keys"] = sorted({m for k in own if not own_key_is_power(k.get("methods") or []) for m in k["methods"]})
    rep["own_limited_keys_count"] = sum(1 for k in own if not own_key_is_power(k.get("methods") or []))
    rep["self_governed"] = self_governed(acc, exports) if rep["has_code"] else None
    rep["n_imports"] = len(imports)
    acting = [e for e in exports if not VIEW_RE.match(e)]
    cls = {"code": [e for e in exports if CODE_RE.search(e) and not NOT_SELF_CODE_RE.search(e) and not MIGRATION_RE.search(e)],
           "migration": [e for e in exports if MIGRATION_RE.search(e)],
           "funds": [e for e in acting if FUNDS_RE.search(e)],
           "freeze": [e for e in acting if FREEZE_RE.search(e)],
           "mint": [e for e in acting if MINT_RE.search(e)],
           "ownership": [e for e in acting if OWNER_RE.search(e)]}
    rep["method_classes"] = cls
    ok, meta = view(acc, "contract_source_metadata") if "contract_source_metadata" in exports else (False, None)
    rep["source_metadata"] = meta if ok else None
    rep["roles"] = roles_of(acc, exports, holders=controllers)
    if rep["roles"].get("upgrade_delay_status"):
        # the exit window is measured on the chain's clock, not on the reader's
        b = rpc.call("block", {"finality": "final"})
        ts = (((b or {}).get("result") or {}).get("header") or {}).get("timestamp")
        if not ts:
            raise RpcUnavailable("the time of the latest block could not be read (the exit window is measured on it)")
        rep["chain_time_ns"] = int(ts)
    rep["holders_described"] = bool(controllers)
    if history:
        rep["deployments"] = deployments(acc)
    ctl = set()
    r = rep["roles"]
    for x in (r.get("super_admins") or []):
        ctl.add(x)
    for role, g in (r.get("grantees") or {}).items():
        for x in (g or []):
            ctl.add(x)
    for m, v in (r.get("owners") or {}).items():
        if isinstance(v, str):
            ctl.add(v)
        elif isinstance(v, list):
            ctl.update(x for x in v if isinstance(x, str))
    if rep["global_contract_account_id"]:
        ctl.add(rep["global_contract_account_id"])
    if r.get("factory"):
        ctl.add(r["factory"])
    ctl.discard(acc)
    rep["controllers"] = {c: describe_controller(c) for c in sorted(ctl)} if controllers else {}
    if rep["self_governed"]:
        rep["controllers"][acc] = rep["self_governed"]
    ch = rep["effective_code_hash"] or a["code_hash"]
    rep["proof"] = load_proofs().get(ch)
    rep["onchain_certificates"] = registry_lookup(ch) if rep["has_code"] else []
    if rep["onchain_certificates"] is None and (rep["proof"] or {}).get("kind", "exit") == "exit" and rep["proof"]:
        # stage 2 needs the certificate on chain; without the registry's answer there is no stage to give
        raise RpcUnavailable("the certificate registry could not be read")
    if accepted_exit(rep["onchain_certificates"]) and not isinstance(rep.get("deployments"), list):
        # stage 2 needs the origin of the account's state: read the history even when the caller skipped it,
        # and give no stage when it cannot be read
        rep["deployments"] = deployments(acc)
        if not isinstance(rep["deployments"], list):
            raise RpcUnavailable("the deployment history could not be read (stage 2 needs it)")
    rep["verdict"] = verdict(rep)
    rep["stage"] = stage(rep)
    if rep["onchain_certificates"] is None and rep["stage"]["level"] == "U" and rep["has_code"]:
        # no code-change path was found, so the registry's answer decides between U and 2: an unread registry is
        # no answer, not "no theorem"
        raise RpcUnavailable("the certificate registry could not be read")
    return rep


def verdict(rep):
    v = {"code_change": [], "funds_control": [], "freeze": [], "exit": None}
    if rep["full_access_keys"]:
        v["code_change"].append({"how": "full-access key on the contract account",
                                 "who": [f"fak:{k}" for k in rep["full_access_keys"]], "src": "chain"})
    if rep.get("global_contract_account_id"):
        v["code_change"].append({"how": "uses a global contract by account id: code follows whatever that account deploys",
                                 "who": [rep["global_contract_account_id"]], "src": "chain"})
    sg = rep.get("self_governed")
    if sg:
        v["code_change"].append({
            "how": {"sputnik DAO": "the contract is a DAO: a proposal it passes can replace its own code or add a key to its account",
                    "multisig": "the contract is a multisig: a request its members confirm can deploy code or add a key on its account"}[sg["kind"]],
            "who": [rep["account"]], "src": "code+view"})
    if rep.get("own_function_call_keys"):
        v["funds_control"].append({
            "how": "function-call key(s) on the contract's own account: the holder calls the contract as itself, "
                   "so private callbacks and own-account-only methods accept the call",
            "who": [f"fak:{k}" for k in rep["own_function_call_keys"]], "src": "chain"})
    r = rep["roles"]
    g = r.get("grantees") or {}
    sa = r.get("super_admins") or []
    owners = sorted({x for vv in (r.get("owners") or {}).values()
                     for x in ([vv] if isinstance(vv, str) else vv if isinstance(vv, list) else []) if isinstance(x, str)})
    cls = rep["method_classes"]
    caps = {"code": "code_change", "funds": "funds_control", "freeze": "freeze"}
    for c, key in caps.items():
        # a role literally named DAO is, by convention of near-plugins contracts, listed on every privileged method
        # the contract has; it gives no pause or fund-moving power when the code has no such method
        roles = [role for role in g if role_class(role) == c or (role == "DAO" and (c == "code" or cls[c]))]
        holders = sorted({x for role in roles for x in (g.get(role) or [])})
        methods = cls[c]
        if not (methods or roles):
            continue
        how = []
        if methods:
            how.append("method(s) " + ", ".join(methods))
        if roles:
            how.append("role(s) " + ", ".join(role if g.get(role) is None else f"{role}[{len(g[role])}]" for role in roles))
        # a super admin can grant itself any role, so it is an effective holder of every ACL-guarded power
        who = sorted(set(holders) | set(sa)) if g else (holders or owners)
        item = {"how": "; ".join(how), "who": who or ["unknown guard"], "src": "code+view" if who else "code",
                "granted_by_super_admins": len(sa)}
        if c == "code" and r.get("factory"):
            item["co_guard"] = {"what": "new code must be supplied by the factory the contract names (get_factory_id)",
                                "who": [r["factory"]]}
        v[key].append(item)
    if sa:
        v["super_admins"] = sa
    v["roles"] = {role: (ms or []) for role, ms in g.items()}
    if rep.get("proof"):
        v["exit"] = rep["proof"]
    v["no_code_change_path_found"] = not v["code_change"]
    return v


MIGRATION_ONLY = {"migrate", "state_migrate", "migrate_state"}
# The methods of the near-plugins upgrade plugin (v0.5.1) that the window bound of upgrade-window/ is about.
PLUGIN_METHODS = {"up_deploy_code", "up_stage_code", "up_init_staging_duration", "up_stage_update_staging_duration",
                  "up_apply_update_staging_duration"}
STAGE_LABEL = {"2": "PROVEN EXIT", "1": "EXIT WINDOW", "0": "KEYHOLDER TRUST", "U": "UNPROVEN"}


def cert_kind(c):
    """Kind of a registry certificate (older records without the field are classified by family)."""
    body = c.get("body", c)
    k = body.get("kind")
    if k:
        return k
    fam = (body.get("family") or "").lower()
    return "token-standard" if fam.startswith("near-contract-standards") else "exit"


def exit_window_seconds(roles, now_ns=None):
    """Seconds until the upgrade plugin could accept a deploy, by the bound proved in upgrade-window/ (`safeUntil`):
    min(now + D, staging timestamp of already staged code, effect time of a pending duration change + its value).
    0 when no staging duration is set."""
    st = roles.get("upgrade_delay_status") or {}

    def num(x):
        return int(x) if x not in (None, "") else None

    d = num(st.get("staging_duration"))
    if not d:
        return 0
    now = now_ns if now_ns is not None else time.time_ns()
    bounds = [now + d]
    # the plugin sets the staging timestamp together with the staged code and clears both together; `safeUntil`
    # takes the timestamp whenever it is set, whatever the staged-code view answered
    if num(st.get("staging_timestamp")) is not None:
        bounds.append(num(st["staging_timestamp"]))
    nd, nts = num(st.get("new_staging_duration")), num(st.get("new_staging_duration_timestamp"))
    if nd is not None and nts is not None:
        bounds.append(max(now, nts) + nd)
    return max(0, (min(bounds) - now) // 10**9)


def stage(rep):
    """Exit stage of a contract.

    2  PROVEN EXIT      no code-change path found AND no access key of any kind AND an exit theorem is registered for
                        this exact code hash by an accepted attestor AND the account's state was made by this code
                        (`origin`: one deployment, or every deployment recorded by the proof and none since)
    1  EXIT WINDOW      code can change only through the upgrade plugin with a non-zero staging delay on the chain's
                        clock, the plugin is established for this code (an upgrade-window certificate or a proof of
                        this repository), every view it rests on answered, and no full-access key, other upgrade
                        method, global contract by account, or pause/move-funds power
    0  KEYHOLDER TRUST  code can change with no delay (or exits can be paused / funds moved by a privileged party), or
                        the plugin and its window are known from names and the contract's own views only
    U  UNPROVEN         no code-change path found by these checks, but no exit theorem covers this account
    """
    v = rep["verdict"]
    cls = rep["method_classes"]
    ex = set(rep["exports"])
    plugin = "up_deploy_code" in ex and "up_stage_code" in ex
    # with the plugin, its own five methods are the path the window bound is about; any other code method,
    # an `up_`-named one included, is a path of its own
    custom = [m for m in cls["code"] if m not in MIGRATION_ONLY and not (plugin and m in PLUGIN_METHODS)]
    gate = rep["roles"].get("gate")
    gated_code = (rep.get("proof") or {}).get("kind") == "gated-upgrade"
    if gate and gated_code:
        # deploy_certified only reaches the plugin's deploy after the registry has answered; it is not a second
        # path. That is a theorem about this repository's gated vault, so it holds for its builds only, not for any
        # contract whose view says it is gated.
        custom = [m for m in custom if m != "deploy_certified"]
    fak = bool(rep["full_access_keys"])
    gba = bool(rep.get("global_contract_account_id"))
    delay_s = exit_window_seconds(rep["roles"], rep.get("chain_time_ns"))
    gate_note = None
    staged_now = rep["roles"].get("staged_code_hash")
    if gate and delay_s == 0 and staged_now and (rep["roles"].get("upgrade_delay_status") or {}).get("staging_duration"):
        # The staged code is past its delay. The gate still asks the registry, but the answer changes the moment an
        # accepted attestor certifies the hash, and then anyone's deploy_certified installs the code at once: no
        # time bound holds in this state, so it is not an exit window.
        try:
            ok_g, ans = view(gate["registry"], "get_valid_kind", {"code_hash": staged_now, "kind": gate["kind"]})
        except RpcUnavailable:
            ok_g, ans = False, None
        if ok_g and ans == []:
            gate_note = (f"certified upgrades only, but code is staged ({str(staged_now)[:12]}…) and its delay has passed: it is "
                         f"deployed as soon as one of {gate['attestors']} accepted attestor(s) certifies its hash — no time bound")
        elif ok_g:
            gate_note = f"the staged code ({str(staged_now)[:12]}…) is certified and past its delay: it can be deployed now"
        else:
            gate_note = "code is staged and past its delay; the gate's registry did not answer"
    certs = rep.get("onchain_certificates") or []
    has_exit = bool(accepted_exit(certs))   # on chain, by an accepted attestor; an entry in proofs.json is not enough
    other_exit = sum(1 for c in certs if cert_kind(c) == "exit") - len(accepted_exit(certs))
    selfkey = bool(rep.get("own_function_call_keys"))
    governed = rep.get("self_governed")
    why = []
    if not rep.get("has_code", True):
        # an account without a contract holds what is sent to it for its keys; there is no code to prove anything about
        if not fak:
            return {"level": "U", "label": STAGE_LABEL["U"], "delay_seconds": None,
                    "why": ["the account has no contract and no full-access key: nothing can be withdrawn from it by anyone"]}
        why.append("the account has no contract: what is sent to it belongs to whoever holds its keys")
    if fak:
        why.append(f"{len(rep['full_access_keys'])} full-access key(s) on the account")
    if governed:
        why.append({"sputnik DAO": "the contract is a DAO: its own vote can replace its code with no delay",
                    "multisig": "the contract is a multisig: a confirmed request can replace its code with no delay"}[governed["kind"]])
    if selfkey:
        why.append(f"{len(rep['own_function_call_keys'])} function-call key(s) on the contract's own account: the holder calls "
                   f"the contract as itself")
    if gba:
        why.append("code follows a global contract referenced by account id")
    if custom:
        why.append("upgrade method(s) without a delay: " + ", ".join(custom[:4]))
    if not (fak or gba or custom or plugin or governed or selfkey):
        nkeys = len(rep.get("keys") or [])
        if has_exit and nkeys:
            # the exit theorems assume nothing leaves the account but what the code pays out; every transaction a
            # key signs, to any receiver, pays its gas from the account's balance
            return {"level": "U", "label": STAGE_LABEL["U"], "delay_seconds": None,
                    "why": ["no code-change path found by these checks",
                            f"an exit theorem is registered for this code hash, but the account has {nkeys} access "
                            f"key(s): each transaction a key signs is paid from the account's balance, an outflow the "
                            f"theorem assumes away"]}
        if has_exit:
            org = origin(rep)
            if org["ok"]:
                out = {"level": "2", "label": STAGE_LABEL["2"], "delay_seconds": None, "origin": org,
                       "why": ["no code-change path found", "exit theorem registered on chain for this code hash by an "
                               "accepted attestor", org["why"]]}
                cond = (rep.get("proof") or {}).get("stage_condition")
                if cond:
                    out["condition"] = cond
                return out
            return {"level": "U", "label": STAGE_LABEL["U"], "delay_seconds": None, "origin": org,
                    "why": ["no code-change path found by these checks",
                            "an exit theorem is registered for this code hash, but " + org["why"]]}
        none = "no exit theorem for this code hash" + (
            f" from an accepted attestor ({other_exit} from others)" if other_exit else "")
        return {"level": "U", "label": STAGE_LABEL["U"], "delay_seconds": None,
                "why": ["no code-change path found by these checks", none]}
    unread = [m for m in (rep["roles"].get("unread") or []) if m != "gate"]
    if plugin and not (fak or gba or custom or governed or selfkey) and unread:
        # the window and the powers that would close it are read from these views; without them there is no window
        why.append("a view the exit window depends on did not answer (" + ", ".join(unread) + "): no window is "
                   "established")
        return {"level": "0", "label": STAGE_LABEL["0"], "delay_seconds": None, "why": why}
    certified = any(cert_kind(c) == "upgrade-window" and c.get("attestor") in ATTESTORS for c in certs)
    proved_here = (rep.get("proof") or {}).get("kind") in ("upgrade-window", "gated-upgrade")
    if plugin and not (fak or gba or custom or governed or selfkey) and delay_s > 0 and not (certified or proved_here):
        # the plugin, its delay and the absence of another path would all rest on names and the contract's own views
        why.append(f"the upgrade plugin is recognised by method names only, and its window ({delay_s} s) by the "
                   f"contract's own view: no upgrade-window certificate and no proof of this repository for this code "
                   f"hash, so no window is established [name]")
        return {"level": "0", "label": STAGE_LABEL["0"], "delay_seconds": delay_s, "why": why}
    if plugin and not (fak or gba or custom or governed or selfkey):
        if delay_s > 0 and not v["freeze"] and not v["funds_control"]:
            basis = ("this code hash has an upgrade-window certificate: the wasm was run against the plugin model"
                     if certified else
                     "this code is a build of a contract proved and tested in this repository with the plugin unchanged "
                     f"({(rep.get('proof') or {}).get('report', 'tools/proofs.json')}); no certificate on chain")
            why1 = [f"no code-change method other than the upgrade plugin's was found by name [name]; through the plugin no "
                    f"deploy can be accepted for the next {delay_s} s (bound proved in upgrade-window/)", basis]
            if gate:
                why1.append(f"upgrades are gated: new code is deployed only if {gate['registry']} holds a certificate of kind "
                            f"{gate['kind']} for its hash from one of {gate['attestors']} accepted attestor(s), as the "
                            f"contract's own view says")
            staged = rep["roles"].get("staged_code_hash")
            if staged:
                why1.insert(1, f"NEW CODE IS STAGED ({str(staged)[:12]}…): withdraw within the window unless you accept it")
            return {"level": "1", "label": STAGE_LABEL["1"], "delay_seconds": delay_s, "plugin_certified": certified,
                    "certified_upgrades_only": bool(gate), "staged_code_hash": staged or None, "why": why1}
        if delay_s > 0:
            why.append(f"upgrade window is {delay_s} s, but exits can be paused or funds moved by a privileged party")
        elif gate_note:
            why.append(gate_note)
        else:
            why.append("upgrade plugin with no exit window: no staging delay is set, or staged code is already deployable")
    return {"level": "0", "label": STAGE_LABEL["0"], "delay_seconds": delay_s or None, "why": why}


def holder_kind(d):
    """Strength class of one controlling account (weakest = acts alone with one key)."""
    if d is None:
        return "unknown"
    k = d.get("kind")
    if k == "sputnik DAO":
        return d.get("factory_guard") or "dao"
    if k == "multisig":
        return "multisig"
    if k == "plain account (keys only)":
        return "single-key" if d.get("full_access_keys", 0) <= 1 else "multi-key account"
    if k == "contract":
        return "contract"
    return "unknown"


ORDER = ["single-key", "multi-key account", "contract", "unknown", "multisig", "dao"]


def summarize(holders, controllers):
    """Aggregate view of who holds a capability: counts by kind and the weakest link.
    Individual account names are deliberately not printed: the depositor needs to know
    how strongly a capability is guarded, not a list of keys to target."""
    kinds = {}
    via_factory = 0
    for h in holders:
        kd = holder_kind(controllers.get(h)) if h in controllers else "unknown"
        kinds[kd] = kinds.get(kd, 0) + 1
        via_factory += bool(h in controllers and (controllers[h] or {}).get("factory_guard"))
    weakest = min(kinds, key=ORDER.index) if kinds else None
    out = {"holders": len(holders), "by_kind": kinds, "weakest": weakest}
    if via_factory:
        out["dao_code_follows_factory"] = via_factory
    return out


def fmt_summary(sm):
    if sm.get("described") is False:
        return "holders not read in this fast answer (ask without --fast for the strength of the guard)"
    if not sm["holders"]:
        return "guard not identified"
    parts = ", ".join(f"{n} {k}" for k, n in sorted(sm["by_kind"].items(), key=lambda kv: ORDER.index(kv[0])))
    alone = {"single-key": "one key can act alone", "multi-key account": "any of several keys of one account",
             "contract": "another contract decides", "multisig": "needs a multisig quorum",
             "dao": "needs a DAO vote", "unknown": "unclassified"}[sm["weakest"]]
    note = ""
    if sm.get("dao_code_follows_factory"):
        note = (f"; {sm['dao_code_follows_factory']} of them a DAO whose own code its factory can replace without a "
                f"vote (auto_update is on), so it is counted by the factory account's keys")
    return f"{sm['holders']} holder(s): {parts}; weakest link — {alone}{note}"


def public_view(rep):
    """Report without individual controller identities."""
    v = rep["verdict"]
    ctl = rep.get("controllers") or {}
    described = rep.get("holders_described", True)
    out = {"account": rep["account"], "stage": rep.get("stage"),
           "code_hash": rep.get("effective_code_hash") or rep["code_hash"],
           "near": (int(rep["balance"]) + int(rep["locked"])) / 1e24,
           "no_code_change_path_found": v["no_code_change_path_found"], "capabilities": {}}
    for cap in ("code_change", "funds_control", "freeze"):
        items = []
        for x in v[cap]:
            who = [x["who"]] if isinstance(x["who"], str) else list(x["who"])
            sm = summarize([w for w in who if not w.startswith("fak:")], ctl)
            nfak = sum(1 for w in who if w.startswith("fak:"))
            if nfak:
                sm["holders"] += nfak
                sm["by_kind"]["single-key"] = sm["by_kind"].get("single-key", 0) + nfak
                sm["weakest"] = "single-key"
            if not described and not nfak:
                # the fast answer: who holds the power was not read, so nothing is said about its strength
                sm = {"holders": None, "by_kind": {}, "weakest": None, "described": False}
            item = {"how": x["how"], "src": x["src"], "guard": sm,
                    "super_admins_can_grant": x.get("granted_by_super_admins", 0)}
            if x.get("co_guard"):
                item["co_guard"] = {"what": x["co_guard"]["what"], "guard": summarize(x["co_guard"]["who"], ctl)}
            items.append(item)
        out["capabilities"][cap] = items
    dep = rep.get("deployments")
    if isinstance(dep, list) and dep:
        out["deployments"] = len(dep)   # rows of the indexer's list: the first and the latest deployment
        if len(dep) > 1:
            out["deployments_note"] = "the indexer lists the first and the latest deployment only; there were at least 2"
        out["last_deploy"] = time.strftime("%Y-%m-%d", time.gmtime(max(d["ts"] for d in dep)))
    meta = rep.get("source_metadata")
    out["source_link"] = meta.get("link") if isinstance(meta, dict) else None
    pr = v.get("exit")
    out["exit_proof"] = pr if pr and pr.get("kind", "exit") == "exit" else None
    # proofs about this code that are not about leaving it; they never raise the stage
    out["other_proofs"] = [pr] if pr and pr.get("kind", "exit") != "exit" else []
    oc = rep.get("onchain_certificates")
    out["onchain_certificates"] = None if oc is None else [
        {"registry": REGISTRY, "kind": cert_kind(c), "attestor": c["attestor"], "attested_at_ns": c["attested_at_ns"],
         "theorems": c["body"]["theorems"], "artifact_sha256": c["body"]["artifact_sha256"],
         "check_command": c["body"]["check_command"]} for c in oc]
    neut = set((out["exit_proof"] or {}).get("neutralized_methods", []))
    if neut:
        for items in out["capabilities"].values():
            for x in items:
                ms = [m.strip() for m in x["how"].replace("method(s) ", "").split(";")[0].split(",")]
                acting = [m for m in ms if not m.startswith(("is_", "get_"))]
                if acting and all(m in neut for m in acting):
                    x["neutralized_by_proof"] = True
    return out


def render(rep):
    if rep.get("error"):
        return f"{rep['account']}: {rep['error']}"
    pv = public_view(rep)
    L = [f"# {pv['account']}  ({pv['near']:,.0f} NEAR on the account; code {pv['code_hash'][:12]}…)"]
    stg = pv.get("stage")
    if stg:
        d = stg.get("delay_seconds") or 0
        span = f"{d // 3600} h" if d >= 3600 else (f"{d // 60} min" if d >= 60 else f"{d} s")
        extra = f" ({span}" + (", certified upgrades only" if stg.get("certified_upgrades_only") else "") + ")" \
            if stg["level"] == "1" and d else ""
        if stg.get("condition"):
            extra = " UNDER A STATED CONDITION"
        L.append(f"EXIT STAGE {stg['level']} — {stg['label']}{extra}: " + "; ".join(stg["why"]))
        if stg.get("condition"):
            L.append(f"  condition: {stg['condition']}")
    L.append("Code can change: " + ("no path found by these checks (keys, global contract, upgrade-like methods, roles) — not a proof" if pv["no_code_change_path_found"] else "YES"))
    titles = {"code_change": None, "funds_control": "Others can move funds held here:", "freeze": "Others can pause/freeze:"}
    for cap, title in titles.items():
        items = pv["capabilities"][cap]
        if title and items:
            L.append(title)
        for x in items:
            extra = f"; {x['super_admins_can_grant']} super admin(s) can grant the role" if x.get("super_admins_can_grant") else ""
            note = " — proved not to block withdrawal [proof]" if x.get("neutralized_by_proof") else ""
            if x.get("co_guard"):
                note += f"; AND {x['co_guard']['what']} — {fmt_summary(x['co_guard']['guard'])} [view]"
            L.append(f"  - via {x['how']} — {fmt_summary(x['guard'])}{extra} [{x['src']}]{note}")
    if rep.get("own_limited_keys_count"):
        L.append(f"Keys on the contract's own account limited to ordinary methods: {rep['own_limited_keys_count']} "
                 f"({', '.join(rep['own_limited_keys'][:6])}) — no stage effect [chain]")
    if pv.get("deployments"):
        L.append(("One code deployment" if pv["deployments"] == 1 else
                  "More than one code deployment (the indexer lists the first and the latest)")
                 + f"; last {pv['last_deploy']} [hist]")
    if pv.get("source_link"):
        L.append(f"Source claimed by the contract: {pv['source_link']} [view, self-reported]")
    oc = pv.get("onchain_certificates")
    if oc:
        for c in oc:
            when = time.strftime("%Y-%m-%d", time.gmtime(c["attested_at_ns"] // 10**9))
            L.append(f"On-chain certificate [chain] ({c['kind']}): {REGISTRY} — attested by {c['attestor']} on {when}; "
                     f"artifact sha256 {c['artifact_sha256'][:16]}…; re-check: {c['check_command']}")
    elif oc is None and rpc.NETWORK[0] != "mainnet":
        L.append(f"On-chain certificate: not looked up ({REGISTRY} is on mainnet; this is a {rpc.NETWORK[0]} account)")
    elif oc is None:
        L.append(f"On-chain certificate: registry {REGISTRY} not reachable")
    else:
        L.append(f"On-chain certificate: none in {REGISTRY}")
    if pv["exit_proof"] or pv.get("other_proofs"):
        p = pv["exit_proof"] or pv["other_proofs"][0]
        kind = p.get("kind", "exit")
        if kind != "exit":  # a proof about this code that is not about leaving it: it never raises the stage
            L.append("Exit proof: none registered for this code hash")
        head = "Exit theorem [proof]" if kind == "exit" else f"Theorem about this code [proof] ({kind})"
        if p.get("attested") is False:
            head += ", in this repository, not attested on chain"
        L.append(f"{head}: {p.get('statement')}")
        L.append(f"  Lean: {p.get('theorem')} ({p.get('axioms', 'axioms not recorded')})")
        for a in p.get("assumptions", []):
            L.append(f"  assumes: {a}")
        if p.get("neutralized_methods"):
            L.append(f"  proved not to block withdrawal: {', '.join(p['neutralized_methods'])}")
        if p.get("binding"):
            L.append(f"  bound to this code by: {p['binding']}")
        if p.get("conformance"):
            L.append(f"  model vs deployed wasm on nearcore runtime: {p['conformance']}")
    else:
        L.append("Exit proof: none registered for this code hash")
    return "\n".join(L)


if __name__ == "__main__":
    js = "--json" in sys.argv
    argv = sys.argv[1:]
    if "--network" in argv:
        i = argv.index("--network")
        if i + 1 >= len(argv) or argv[i + 1] not in ("mainnet", "testnet"):
            sys.exit("--network takes mainnet or testnet")
        rpc.use_network(argv[i + 1])
        del argv[i:i + 2]
    accs = [a for a in argv if not a.startswith("--")]
    if not accs:
        sys.exit("\n\n".join(__doc__.split("\n\n")[:2]))
    failed = False
    for acc in accs:
        try:
            fast = "--fast" in sys.argv
            rep = scan(acc, history="--no-history" not in sys.argv and not fast, controllers=not fast)
        except RpcUnavailable as e:
            print(f"{acc}: the public RPC did not answer ({str(e)[:100]}); no verdict — retry in a minute "
                  f"or set EXITPROOF_RPC to another endpoint", file=sys.stderr)
            sys.exit(2)
        failed = failed or "error" in rep
        if js:
            print(json.dumps(public_view(rep) if "error" not in rep else rep, indent=1, default=str))
        else:
            print(render(rep))
        print()
    sys.exit(1 if failed else 0)   # 1: an account was not found or is not an account id; 2 (above): the chain was not read
