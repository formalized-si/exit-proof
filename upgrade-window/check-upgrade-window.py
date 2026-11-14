#!/usr/bin/env python3
"""check-upgrade-window.py <account> [--json] [--rpc URL[,URL...]]

Reads, from NEAR mainnet (read-only RPC, one block), what the `Upgradable` plugin of near-plugins
exposes about an account's upgrade delay, and prints the exit window it implies:

  * whether the plugin's interface is there (`up_get_delay_status` answers);
  * the staging duration D (or none);
  * staged code, if any: its hash and the earliest time `up_deploy_code` can succeed;
  * a staged update of the duration, if any, and when it can be applied;
  * `safe until`: the earliest block timestamp at which any `up_deploy_code` call can succeed,
    whatever the role holders do (theorems W3_no_deploy_before / W3U_no_deploy_before, README).
    The build of the deployed contract is unknown, so a duration above 2^63 ns is counted as
    no delay: without overflow checks such a duration can be removed at once;
  * what the theorems do not cover: access keys on the account (a full-access key deploys code
    directly) and the number of accounts holding roles (counts only, no account names).

Standard library only. No transaction is sent. A failed RPC call is an error, never an answer.
"""
import base64
import datetime
import json
import os
import sys
import time
import urllib.error
import urllib.request

U64_MAX = 2**64 - 1
DEFAULT_RPC = "https://rpc.mainnet.fastnear.com,https://free.rpc.fastnear.com,https://rpc.mainnet.near.org"
TRANSIENT = ("TOO_MANY_REQUESTS", "TIMEOUT_ERROR", "NO_SYNCED_BLOCKS", "INTERNAL_ERROR", "Too Many Requests",
             "UNKNOWN_BLOCK", "GARBAGE_COLLECTED_BLOCK", "NOT_SYNCED_YET", "UNAVAILABLE_SHARD")


class RpcUnavailable(Exception):
    pass


class Rpc:
    def __init__(self, endpoints):
        self.endpoints = endpoints

    def call(self, method, params, attempts=8):
        body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
        err = None
        for i in range(attempts):
            url = self.endpoints[i % len(self.endpoints)]
            try:
                req = urllib.request.Request(url, body, {"Content-Type": "application/json",
                                                         "User-Agent": "check-upgrade-window-readonly"})
                j = json.loads(urllib.request.urlopen(req, timeout=30).read())
            except (urllib.error.URLError, TimeoutError, OSError, ValueError) as e:
                err = f"{url}: {str(e)[:80]}"
                time.sleep(min(8, 0.5 * 2 ** i))
                continue
            blob = json.dumps(j.get("error", ""))
            if "error" in j and any(t in blob for t in TRANSIENT):
                err = f"{url}: {blob[:120]}"
                time.sleep(min(8, 0.5 * 2 ** i))
                continue
            return j
        raise RpcUnavailable(f"{method}: {err}")

    def query(self, request_type, block_id, **kw):
        p = {"request_type": request_type, "block_id": block_id}
        p.update(kw)
        return self.call("query", p)

    def view(self, account, method, block_id, args=None):
        """('ok', value) | ('no_method', text) | ('no_contract', text) | ('failed', text)."""
        j = self.query("call_function", block_id, account_id=account, method_name=method,
                       args_base64=base64.b64encode(json.dumps(args or {}).encode()).decode())
        res = j.get("result") or {}
        text = json.dumps(j["error"]) if "error" in j else res.get("error")
        if text is not None:
            if "MethodNotFound" in text:
                return ("no_method", text)
            if "CodeDoesNotExist" in text or "NO_CONTRACT_CODE" in text:
                return ("no_contract", text)
            return ("failed", text[:300])
        try:
            return ("ok", json.loads(bytes(res["result"]).decode()))
        except (KeyError, ValueError) as e:
            return ("failed", f"undecodable result: {e}")


def sat(a, b):
    return min(a + b, U64_MAX)


B = 2**63


def eff(d):
    """What a duration is worth on a build without overflow checks: nothing above B."""
    return d if d <= B else 0


def safe_until(status, now):
    """`safeUntilU B` of lean/UpgradeWindow/Unchecked.lean; equal to `safeUntil` of Model.lean
    whenever no duration exceeds B. Valid for both builds while block timestamps are below 2^63."""
    dur, ts = status.get("staging_duration"), status.get("staging_timestamp")
    nd, ndt = status.get("new_staging_duration"), status.get("new_staging_duration_timestamp")
    a = sat(now, eff(dur or 0))
    b = a if ts is None else min(a, ts)
    if nd is not None and ndt is not None:
        return min(b, sat(max(now, ndt), eff(nd)))
    return b


def utc(ns):
    if ns >= 2**62:
        return "never (beyond year 2116)" if ns < U64_MAX else "never (u64::MAX)"
    return datetime.datetime.fromtimestamp(ns / 1e9, datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")


def span(ns):
    if ns >= 2**62:
        return f"{ns} ns (over 146 years)"
    s, rem = divmod(ns, 10**9)
    d, s = divmod(s, 86400)
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    parts = [f"{d}d" if d else "", f"{h}h" if h else "", f"{m}m" if m else "", f"{s}s" if s or not (d or h or m) else ""]
    text = " ".join(p for p in parts if p)
    return f"{text} ({ns} ns)" if rem or ns < 10**9 else text


def read(account, rpc):
    """Everything the report needs, read at one final block."""
    blk = rpc.call("block", {"finality": "final"})
    if "error" in blk:
        raise RpcUnavailable(json.dumps(blk["error"])[:200])
    head = blk["result"]["header"]
    height, now = head["height"], int(head["timestamp_nanosec"])
    out = {"account": account, "block_height": height, "block_hash": head["hash"], "block_timestamp_ns": now,
           "block_time": utc(now)}
    acc = rpc.query("view_account", height, account_id=account)
    if "error" in acc:
        if "UNKNOWN_ACCOUNT" in json.dumps(acc["error"]):
            out["account_exists"] = False
            return out
        raise RpcUnavailable(json.dumps(acc["error"])[:200])
    a = acc["result"]
    out["account_exists"] = True
    out["code_hash"] = a["code_hash"]
    out["global_contract"] = a.get("global_contract_hash") or a.get("global_contract_account_id")
    keys = rpc.query("view_access_key_list", height, account_id=account)
    if "error" in keys:
        raise RpcUnavailable(json.dumps(keys["error"])[:200])
    kl = keys["result"]["keys"]
    out["full_access_keys"] = sum(1 for k in kl if k["access_key"]["permission"] == "FullAccess")
    out["function_call_keys"] = len(kl) - out["full_access_keys"]
    kind, val = rpc.view(account, "up_get_delay_status", height)
    out["plugin"] = kind
    if kind != "ok":
        out["plugin_detail"] = val if kind != "no_method" else "method up_get_delay_status not found"
        return out
    out["delay_status"] = {k: val.get(k) for k in ("staging_duration", "staging_timestamp", "new_staging_duration",
                                                    "new_staging_duration_timestamp")}
    kind, val = rpc.view(account, "up_staged_code_hash", height)
    out["staged_code_hash_view"] = kind
    out["staged_code_hash"] = val if kind == "ok" else None
    if kind != "ok":
        out["staged_code_hash_detail"] = val
    # role holders: counts only
    kind, val = rpc.view(account, "acl_get_permissioned_accounts", height)
    if kind == "ok" and isinstance(val, dict):
        out["acl"] = {"super_admins": len(val.get("super_admins") or []),
                      "roles": {r: {"admins": len(v.get("admins") or []), "grantees": len(v.get("grantees") or [])}
                                for r, v in sorted((val.get("roles") or {}).items())}}
    else:
        out["acl"] = None
    return out


def assess(r):
    """Adds the derived fields: window, alarms, verdict."""
    if not r.get("account_exists") or r.get("plugin") != "ok":
        r["verdict"] = "NO_PLUGIN" if r.get("account_exists") else "NO_ACCOUNT"
        return r
    st, now = r["delay_status"], r["block_timestamp_ns"]
    dur = st["staging_duration"]
    su = safe_until(st, now)
    r["safe_until_ns"] = su
    r["window_now_ns"] = max(0, su - now)
    notes = []
    staged = r.get("staged_code_hash")
    if st["staging_timestamp"] is not None or staged:
        ts = st["staging_timestamp"]
        r["staged"] = {"hash": staged, "earliest_deploy_ns": ts,
                       "deployable_now": ts is not None and ts <= now and staged is not None,
                       "same_as_deployed_code": staged is not None and staged == r["code_hash"]}
    else:
        r["staged"] = None
    nd, ndt = st["new_staging_duration"], st["new_staging_duration_timestamp"]
    if nd is not None and ndt is not None:
        r["pending_duration"] = {"new_duration_ns": nd, "applicable_from_ns": ndt, "applicable_now": ndt <= now,
                                 "already_in_force": dur == nd,
                                 "direction": "same" if dur == nd else ("shorter" if dur is not None and nd < dur else "longer")}
    else:
        r["pending_duration"] = None
    if dur is None:
        verdict = "NO_WINDOW"
        notes.append("staging duration is not set: code can be staged and its deployment accepted at the same "
                     "block timestamp (theorem W4_no_window)")
    elif dur == 0:
        verdict = "NO_WINDOW"
        notes.append("staging duration is 0")
    elif dur > B:
        verdict = "WINDOW_ONLY_IF_BUILT_WITH_OVERFLOW_CHECKS"
        notes.append("staging duration is above 2^63 ns: if the contract is built without overflow checks, "
                     "`now + duration` wraps in up_stage_update_staging_duration and the delay can be removed "
                     "at once (theorem W3_unchecked_shortcut); counted as no delay here")
    else:
        verdict = "WINDOW"
    if r["staged"] and r["staged"]["deployable_now"]:
        notes.append("staged code is deployable now" + (" (it equals the code deployed now)"
                     if r["staged"]["same_as_deployed_code"] else ""))
        if verdict == "WINDOW":
            verdict = "WINDOW_CLOSED_FOR_STAGED_CODE"
    elif r["staged"] and verdict == "WINDOW":
        verdict = "WINDOW_RUNNING"
        notes.append("code is staged: the window for it is running")
    p = r["pending_duration"]
    if p and p["direction"] == "shorter" and verdict.startswith("WINDOW"):
        notes.append("a shorter staging duration is staged")
        if verdict == "WINDOW":
            verdict = "WINDOW_RUNNING"
    if p and not p["already_in_force"] and p["new_duration_ns"] > B:
        notes.append("the staged duration update is above 2^63 ns: in a build without overflow checks the "
                     "delay can be removed at once after it is applied (theorem W3_unchecked_shortcut); "
                     "counted as an update to no delay here")
        if verdict == "WINDOW":
            verdict = "WINDOW_RUNNING"
    if r["full_access_keys"]:
        notes.append(f"{r['full_access_keys']} full-access key(s) on the account: code can be deployed directly, "
                     "outside the plugin (not covered by the theorems)")
        verdict += "+FULL_ACCESS_KEYS"
    r["verdict"], r["notes"] = verdict, notes
    return r


def render(r):
    L = [f"account          {r['account']}",
         f"read at          block {r['block_height']} ({r['block_time']})"]
    if not r.get("account_exists"):
        return "\n".join(L + ["account          does not exist"])
    L.append(f"code hash        {r['code_hash']}" + (f" (global contract {r['global_contract']})" if r.get("global_contract") else ""))
    L.append(f"access keys      {r['full_access_keys']} full-access, {r['function_call_keys']} function-call")
    if r["plugin"] != "ok":
        L.append(f"Upgradable       not detected ({r.get('plugin_detail')})")
        L.append("verdict          NO_PLUGIN: this checker says nothing about how the code of this account can change")
        return "\n".join(L)
    st = r["delay_status"]
    L.append("Upgradable       interface detected (up_get_delay_status answers; the deployed wasm is not compared to v0.5.1)")
    dur = st["staging_duration"]
    L.append(f"staging duration {'none (never initialised)' if dur is None else span(dur)}")
    s = r["staged"]
    if s is None:
        L.append("staged code      none")
    else:
        when = "unknown (no staging timestamp)" if s["earliest_deploy_ns"] is None else utc(s["earliest_deploy_ns"])
        L.append(f"staged code      {s['hash']}" + (" = the deployed code" if s["same_as_deployed_code"] else ""))
        L.append(f"                 earliest deploy: {when}" + (" — deployable now" if s["deployable_now"] else ""))
    p = r["pending_duration"]
    if p is None:
        L.append("duration update  none staged")
    elif p["already_in_force"]:
        L.append(f"duration update  none pending (the last staged value, {span(p['new_duration_ns'])}, is in force)")
    else:
        L.append(f"duration update  staged: {span(p['new_duration_ns'])} ({p['direction']}), applicable from "
                 f"{utc(p['applicable_from_ns'])}" + (" — applicable now" if p["applicable_now"] else ""))
    if r["window_now_ns"] == 0:
        L.append("safe until       already passed: an up_deploy_code call can succeed at the current block timestamp")
        L.append("exit window now  none")
    else:
        L.append(f"safe until       {utc(r['safe_until_ns'])}: no up_deploy_code call can succeed earlier (W3)")
        L.append(f"exit window now  {span(r['window_now_ns'])}")
    acl = r.get("acl")
    if acl:
        roles = ", ".join(f"{k}: {v['grantees']} grantee(s), {v['admins']} admin(s)" for k, v in acl["roles"].items())
        L.append(f"role holders     {acl['super_admins']} super-admin(s); {roles or 'no roles'}")
    else:
        L.append("role holders     acl_get_permissioned_accounts did not answer")
    L.append(f"verdict          {r['verdict']}")
    for n in r["notes"]:
        L.append(f"  - {n}")
    L.append("not covered      code-change paths outside the plugin (full-access keys above; custom upgrade or "
             "migration methods of the contract), pausing of exit methods: check them with the scanner; "
             "a deploy batch created in the block or two before this reading does not show in the views")
    return "\n".join(L)


def main():
    argv = sys.argv[1:]
    eps = os.environ.get("NEAR_RPC", DEFAULT_RPC)
    if "--rpc" in argv:
        i = argv.index("--rpc")
        eps = argv[i + 1]
        del argv[i:i + 2]
    args = [a for a in argv if not a.startswith("--")]
    if len(args) != 1:
        print(__doc__)
        sys.exit(2)
    try:
        r = assess(read(args[0], Rpc(eps.split(","))))
    except RpcUnavailable as e:
        print(f"RPC unavailable, no answer: {e}", file=sys.stderr)
        sys.exit(3)
    print(json.dumps(r, indent=1) if "--json" in argv else render(r))


if __name__ == "__main__":
    main()
