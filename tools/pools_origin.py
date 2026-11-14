"""Origin of the state of every pool that runs the proved staking pool code: how many code deployments its account
has had, and who made them.

The exit theorem is about states the pool code reaches from its own initialisation. A deployment keeps the storage
of an account, so the scanner gives stage 2 only to an account whose deployment history lists one deployment
(tools/exitproof.py, function `origin`). This script reads that history for all pools of evidence/pools-live.json,
so that the share of stake reported at stage 2 rests on the same rule.

usage: pools_origin.py [<out.json>] [--pause seconds]      default out: evidence/pools-origin.json; resumes a partial file
Read-only: one request per pool to the public deployment-history API (NearBlocks), spaced by --pause (default 11 s,
the free rate of that API). The answer of an indexer is evidence of the level "read", not a proof.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    argv = sys.argv[1:]
    pause = 11.0
    if "--pause" in argv:
        i = argv.index("--pause")
        pause = float(argv[i + 1])
        del argv[i:i + 2]
    out = argv[0] if argv else os.path.join(HERE, "..", "evidence", "pools-origin.json")
    pools = [p["pool"] for p in json.load(open(os.path.join(HERE, "..", "evidence", "pools-live.json")))["pools"]]
    try:
        rows = {r["pool"]: r for r in json.load(open(out))["pools"] if r.get("deployments") is not None}
    except (OSError, ValueError, KeyError):
        rows = {}
    for k, pool in enumerate(pools):
        if pool in rows:
            continue
        d = exitproof.deployments(pool)
        if isinstance(d, list):
            rows[pool] = {"pool": pool, "deployments": len(d), "by": sorted({x.get("by") or "?" for x in d}),
                          "first": time.strftime("%Y-%m-%d", time.gmtime(min(x["ts"] for x in d))) if d else None}
        else:
            rows[pool] = {"pool": pool, "deployments": None, "error": d.get("error")}
        done = [rows[p] for p in pools if p in rows]
        one = [r for r in done if r["deployments"] == 1]
        summary = {"read_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "pools": len(pools), "read": len(done),
                   "one_deployment": len(one),
                   "one_deployment_made_by_another_account": sum(1 for r in one if r["by"] != [r["pool"]]),
                   "made_by": sorted({b for r in one for b in r["by"] if b != r["pool"]}),
                   "more_than_one_deployment": sum(1 for r in done if (r["deployments"] or 0) > 1),
                   "no_deployment_listed": sum(1 for r in done if r["deployments"] == 0),
                   "not_read": sum(1 for r in done if r["deployments"] is None),
                   "source": "NearBlocks API, contract/deployments of each pool account"}
        json.dump({"summary": summary, "pools": done}, open(out, "w"), indent=1)
        print(f"{k + 1}/{len(pools)} {pool}: {rows[pool].get('deployments')}", file=sys.stderr, flush=True)
        time.sleep(pause)
    print(json.dumps(json.load(open(out))["summary"], indent=1))


if __name__ == "__main__":
    main()
