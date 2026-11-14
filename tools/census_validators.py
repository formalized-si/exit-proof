"""Census of current validators: stake grouped by the code that runs each pool.

usage: census_validators.py <out.json>
Reads RPC `validators` (current epoch), then `view_account` and `view_access_key_list` of every pool.
A pool whose account could not be read after retries is kept with code_hash = null and reported, never guessed.
"""
import collections
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rpc import RpcUnavailable, call, q  # noqa: E402


def read_pool(acc):
    a = q("view_account", account_id=acc)["result"]
    ks = q("view_access_key_list", account_id=acc)["result"]["keys"]
    return {"code_hash": a.get("code_hash"),
            "global": a.get("global_contract_hash") or a.get("global_contract_account_id"),
            "fak": sum(1 for k in ks if k["access_key"]["permission"] == "FullAccess"), "keys": len(ks)}


if __name__ == "__main__":
    out = sys.argv[1]
    v = call("validators", [None])["result"]
    rows = [{"pool": x["account_id"], "stake": int(x["stake"]), "code_hash": None, "global": None, "fak": None}
            for x in v["current_validators"]]
    for attempt in range(4):
        todo = [r for r in rows if r["code_hash"] is None]
        if not todo:
            break
        for r in todo:
            try:
                r.update(read_pool(r["pool"]))
            except (RpcUnavailable, KeyError):
                pass
        time.sleep(5 * attempt)
    json.dump({"epoch_start_height": v.get("epoch_start_height"),
               "fetched": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "rows": rows}, open(out, "w"), indent=1)
    tot = sum(r["stake"] for r in rows)
    by = collections.defaultdict(lambda: [0, 0, 0])
    for r in rows:
        k = r["global"] or r["code_hash"] or "UNREAD"
        by[k][0] += 1
        by[k][1] += r["stake"]
        by[k][2] += 1 if r["fak"] else 0
    print("validators", len(rows), "total stake NEAR", round(tot / 1e24))
    for k, (n, s, f) in sorted(by.items(), key=lambda kv: -kv[1][1]):
        print(str(k)[:12], "pools", n, "stake_NEAR", round(s / 1e24), "share %.1f%%" % (100 * s / tot), "pools_with_full_access_key", f)
