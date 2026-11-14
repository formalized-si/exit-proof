"""Every code deployment of an account, read once, for a proof that names the deployments it covers.

usage: deploy_history.py <account> [--network mainnet|testnet] > evidence/<account>-deployments.json

The scanner's indexer list holds the first and the latest deployment of an account only. A proof entry in
`tools/proofs.json` that names more than one deployment (`origin.<account>.deployments`) needs the full list, recorded
once as `full_history`: deployments before the latest one are in the past and cannot change, and the scanner checks
at every scan that the latest one is still the latest. This script reads the full list from the indexer's receipts of
the account that carry a DEPLOY_CONTRACT action (successful receipts to the account only), and the short list beside
it. Read-only; exit status 0 on a complete read, 2 if the indexer did not answer or the list did not end.
"""
import json
import os
import sys
import time
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402
import rpc  # noqa: E402

RECEIPTS = "/v1/account/{}/receipts?action=DEPLOY_CONTRACT&per_page=25&order=asc"


def get(url, attempts=5):
    for i in range(attempts):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "exitproof-readonly"})
            return json.loads(urllib.request.urlopen(req, timeout=30).read())
        except Exception as e:
            err = str(e)[:120]
            time.sleep(6 * (i + 1))   # the public indexer limits requests per minute
    raise RuntimeError(err)


def full_list(acc, pages=40):
    out, cursor = [], None
    for _ in range(pages):
        j = get(exitproof.INDEXER[rpc.NETWORK[0]] + RECEIPTS.format(acc) + (f"&cursor={cursor}" if cursor else ""))
        for r in j.get("txns") or []:
            if r.get("receiver_account_id") != acc or not (r.get("receipt_outcome") or {}).get("status"):
                continue
            if any(x.get("action") == "DEPLOY_CONTRACT" for x in r.get("actions") or []):
                out.append({"tx": r["transaction_hash"], "receipt": r["receipt_id"],
                            "block": (r.get("receipt_block") or {}).get("block_height"),
                            "ts": int(r["block_timestamp"]) // 10**9, "by": r.get("predecessor_account_id")})
        cursor = j.get("cursor")
        if not cursor:
            return out
        time.sleep(4)
    raise RuntimeError(f"more than {pages} pages of deployment receipts")


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if "--network" in sys.argv:
        rpc.use_network(sys.argv[sys.argv.index("--network") + 1])
        args = [a for a in args if a != sys.argv[sys.argv.index("--network") + 1]]
    if len(args) != 1:
        sys.exit(__doc__.strip().splitlines()[2])
    acc = args[0]
    try:
        full = full_list(acc)
        short = exitproof.deployments(acc)
        if not isinstance(short, list):
            raise RuntimeError(short["error"])
    except RuntimeError as e:
        print(f"the indexer did not answer: {e}", file=sys.stderr)
        sys.exit(2)
    print(json.dumps({"account": acc, "network": rpc.NETWORK[0],
                      "read_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                      "method": "every successful receipt to the account with a DEPLOY_CONTRACT action, from the indexer's "
                                "receipt list (NearBlocks " + RECEIPTS.split("?")[0].format(acc) + "); the short list of "
                                "tools/exitproof.py beside it",
                      "deployments": full, "count": len(full), "indexer_short_list": short}, indent=1))
