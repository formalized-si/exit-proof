"""Live check of the exit theorem's precondition for every validator pool that runs the proved code.

At ONE pinned final block, for each pool whose code hash is the proved staking pool:
  S1 solvency      account balance (liquid + locked) >= total_staked_balance + sum of delegators' unstaked balances
  S2 share books   sum of delegators' staked balances (each rounded down by the contract) <= total_staked_balance
  K  no keys       the pool account has no access keys (its code cannot be replaced by a key)
S1 is the `solvency` invariant the exit theorem relies on; S2 follows from the model invariant on shares.
Reads only view methods the contract exports (get_accounts pages, get_total_staked_balance) and account state.

usage: pools_live.py <validators-census.json> <out.json> [--limit N] [--resume]
  --resume  re-read only the pools that failed, at the block of the previous run (needs INTERNAL_OUT of that run)
Output: per pool only the boolean results and the delegator count; network totals. Per-pool balances are not written.
"""
import base64
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rpc import RpcUnavailable, call, q  # noqa: E402

PROVED = "J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY"


def view(acc, method, args, block):
    err = ""
    for attempt in range(6):
        r = q("call_function", block_id=block, account_id=acc, method_name=method,
              args_base64=base64.b64encode(json.dumps(args).encode()).decode())
        res = r.get("result", {})
        if isinstance(res, dict) and "result" in res:
            return json.loads(bytes(res["result"]).decode())
        err = json.dumps(r.get("error") or res)[:200]
        if "GasLimit" in err or "gas" in err.lower() or "MethodNotFound" in err:
            break  # not transient: let the caller shrink the page or give up
        time.sleep(1 + attempt)
    raise RuntimeError(f"{acc}.{method}: {err}")


def check_pool(acc, block):
    a = q("view_account", block_id=block, account_id=acc)["result"]
    if a["code_hash"] != PROVED:
        return {"pool": acc, "skipped": "code hash changed"}
    keys = q("view_access_key_list", block_id=block, account_id=acc)["result"]["keys"]
    total_staked = int(view(acc, "get_total_staked_balance", {}, block))
    n = int(view(acc, "get_number_of_accounts", {}, block))
    sum_unstaked = sum_staked = seen = 0
    page = 150
    i = 0
    while i < n:
        try:
            accs = view(acc, "get_accounts", {"from_index": i, "limit": page}, block)
        except RuntimeError as e:
            if page > 10 and ("GasLimit" in str(e) or "gas" in str(e).lower() or "Exceeded" in str(e)):
                page //= 2
                continue
            raise
        if not accs:
            break
        for x in accs:
            sum_unstaked += int(x["unstaked_balance"])
            sum_staked += int(x["staked_balance"])
        seen += len(accs)
        i += len(accs)
    bal = int(a["amount"]) + int(a["locked"])
    return {"pool": acc, "delegators": seen, "accounts_reported": n,
            "S1_solvent": bal >= total_staked + sum_unstaked,
            "S2_shares_consistent": sum_staked <= total_staked,
            "K_no_keys": len(keys) == 0,
            "_total_staked": total_staked, "_sum_unstaked": sum_unstaked, "_balance": bal}


if __name__ == "__main__":
    census, out = sys.argv[1], sys.argv[2]
    limit = int(sys.argv[sys.argv.index("--limit") + 1]) if "--limit" in sys.argv else None
    pools = [r["pool"] for r in json.load(open(census))["rows"] if r["code_hash"] == PROVED]
    if limit:
        pools = pools[:limit]
    done = {}
    if "--resume" in sys.argv:
        prev = json.load(open(os.environ["INTERNAL_OUT"]))
        done = {r["pool"]: r for r in prev["pools"] if "S1_solvent" in r}
        block = prev["summary"]["block_height"]
        blk = call("block", {"block_id": block})["result"]["header"]
        pools_all, pools = pools, [x for x in pools if x not in done]
        print("resume at block", block, "pools left", len(pools), flush=True)
    else:
        blk = call("block", {"finality": "final"})["result"]["header"]
        block = blk["height"]
        pools_all = pools
    t0 = time.time()

    def one(acc):
        err = ""
        for attempt in range(3):
            try:
                return check_pool(acc, block)
            except (RpcUnavailable, RuntimeError, KeyError) as e:
                err = str(e)[:160]
                time.sleep(3)
        return {"pool": acc, "error": err}

    from concurrent.futures import ThreadPoolExecutor
    rows = []
    with ThreadPoolExecutor(max_workers=int(os.environ.get("JOBS", "4"))) as ex:
        for k, r in enumerate(ex.map(one, pools)):
            rows.append(r)
            if k % 10 == 0 or "--resume" in sys.argv:
                print(k, len(pools), r["pool"], "error" in r and r["error"][:60] or "ok", f"{time.time() - t0:.0f}s", flush=True)
    byname = {r["pool"]: r for r in rows}
    rows = [done.get(x) or byname[x] for x in pools_all]
    ok = [r for r in rows if "S1_solvent" in r]
    summary = {
        "block_height": block, "block_hash": blk["hash"], "block_time_ns": blk["timestamp"],
        "pools_checked": len(ok), "pools_failed_to_read": len(rows) - len(ok),
        "S1_solvent": sum(r["S1_solvent"] for r in ok), "S2_shares_consistent": sum(r["S2_shares_consistent"] for r in ok),
        "K_no_keys": sum(r["K_no_keys"] for r in ok),
        "delegator_accounts": sum(r["delegators"] for r in ok),
        "total_staked_NEAR": round(sum(r["_total_staked"] for r in ok) / 1e24),
        "delegators_unstaked_NEAR": round(sum(r["_sum_unstaked"] for r in ok) / 1e24),
        "pools_balance_NEAR": round(sum(r["_balance"] for r in ok) / 1e24),
    }
    public = [{k: v for k, v in r.items() if not k.startswith("_")} for r in rows]
    json.dump({"summary": summary, "pools": public}, open(out, "w"), indent=1)
    if os.environ.get("INTERNAL_OUT"):  # per-pool balances, kept out of the published evidence
        json.dump({"summary": summary, "pools": rows}, open(os.environ["INTERNAL_OUT"], "w"), indent=1)
    print(json.dumps(summary, indent=1))
