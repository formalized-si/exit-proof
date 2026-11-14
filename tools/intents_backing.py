"""Live state of the NEAR Intents ledger against the tokens it holds, with the conformance verdict of each token.

usage: intents_backing.py [--out evidence/intents-live-backing.json] [--block <height>]
       intents_backing.py --table [evidence/intents-live-backing.json]     print the summary table of a saved reading

For every fungible token id the ledger of intents.near lists (view mt_tokens), at one pinned block:
  owed  = mt_supply of the id, what the ledger says its accounts hold;
  held  = ft_balance_of(intents.near) at the token, what the contract really holds;
and the verdict of the token's code from evidence/token-census.json.
The proof in intents-proof/ says owed <= held for a token that behaves as the standard, starting from an empty
ledger. This script is the reading of the live contract next to that statement: where owed > held, the token is
outside the proof's assumption or the state predates the proved code. Read-only; public RPC.

Verdicts that are not from the census: NO CODE (the account has no contract: the id is in the ledger, nothing can
be held there), CODE FOLLOWS ANOTHER ACCOUNT (a global contract referenced by account id: that account can replace
the token's code at any time, so no verdict about the code is given), NOT CHECKED (code not in the census).
"""
import base64
import collections
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402
import rpc  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
CENSUS = os.path.join(HERE, "..", "evidence", "token-census.json")
INTENTS = "intents.near"


def view_at(block, acc, method, args):
    r = rpc.q("call_function", block_id=block, account_id=acc, method_name=method,
              args_base64=base64.b64encode(json.dumps(args).encode()).decode())
    res = r.get("result", {})
    if isinstance(res, dict) and "result" in res:
        try:
            return json.loads(bytes(res["result"]).decode())
        except ValueError:
            return None
    return None


def code_and_verdict(t, census):
    try:
        a = exitproof.account(t)
        code, how = exitproof.effective_code(a) if a else (None, "none")
    except exitproof.RpcUnavailable:
        return "unread", "NOT CHECKED"
    if how == "global_by_account":
        return None, "CODE FOLLOWS ANOTHER ACCOUNT"
    if code is None:
        return None, "NO CODE"
    return code, (census.get(code) or {}).get("verdict") or "NOT CHECKED"


def summarize(rows, block, n_ids):
    rel = collections.Counter(r["relation"] for r in rows)
    by = collections.defaultdict(collections.Counter)
    for r in rows:
        by[r["verdict"]][r["relation"]] += 1
    std = [r for r in rows if r["verdict"].startswith("STANDARD")]
    deficits = [{"token": r["token"], "verdict": r["verdict"], "owed": r["owed"], "held": r["held"]}
                for r in rows if r["relation"] == "DEFICIT"]
    return {"block": block, "ledger_token_ids": n_ids, "fungible_tokens": len(rows), "relation": dict(rel),
            "standard_verdict": {"tokens": len(std), "deficits": sum(1 for r in std if r["relation"] == "DEFICIT")},
            "by_verdict": {v: dict(c) for v, c in by.items()}, "deficits": deficits}


def table(path):
    s = json.load(open(path))["summary"]
    cols = ["equal", "surplus", "DEFICIT", "unread"]
    print(f"block {s['block']}: {s['fungible_tokens']} fungible tokens in the ledger")
    print("| Verdict of the token's code | ledger = held | held > ledger | ledger > held | not readable |")
    print("|---|---|---|---|---|")
    order = ["STANDARD", "STANDARD + EXTENSIONS", "DEVIATES", "UNDER REVIEW", "NOT RUN", "NOT CHECKED",
             "CODE FOLLOWS ANOTHER ACCOUNT", "NO CODE"]
    for v in order + sorted(set(s["by_verdict"]) - set(order)):
        c = s["by_verdict"].get(v)
        if c:
            print(f"| {v} | " + " | ".join(str(c.get(k, 0)) for k in cols) + " |")
    print("| all | " + " | ".join(str(s["relation"].get(k, 0)) for k in cols) + " |")


def main():
    argv = sys.argv[1:]
    out = argv[argv.index("--out") + 1] if "--out" in argv else os.path.join(HERE, "..", "evidence", "intents-live-backing.json")
    if "--block" in argv:
        block = int(argv[argv.index("--block") + 1])
    else:
        block = rpc.call("block", {"finality": "final"})["result"]["header"]["height"]
    census = json.load(open(CENSUS))["families"]
    ids, i = [], 0
    while True:
        page = view_at(block, INTENTS, "mt_tokens", {"from_index": str(i), "limit": 500})
        if not page:
            break
        ids += [t["token_id"] if isinstance(t, dict) else t for t in page]
        i += len(page)
        if len(page) < 500:
            break
    ft = sorted({x.split(":", 1)[1] for x in ids if x.startswith("nep141:")})
    rows = []
    for k, t in enumerate(ft):
        owed = view_at(block, INTENTS, "mt_supply", {"token_id": f"nep141:{t}"})
        held = view_at(block, t, "ft_balance_of", {"account_id": INTENTS})
        code, verdict = code_and_verdict(t, census)
        row = {"token": t, "code_hash": code, "verdict": verdict, "owed": owed, "held": held}
        if owed is not None and held is not None:
            o, h = int(owed), int(held)
            row["relation"] = "equal" if o == h else ("surplus" if h > o else "DEFICIT")
        else:
            row["relation"] = "unread"
        rows.append(row)
        if k % 50 == 0:
            print(f"{k}/{len(ft)}", file=sys.stderr, flush=True)
    summary = summarize(rows, block, len(ids))
    json.dump({"summary": summary, "tokens": rows}, open(out, "w"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    if "--table" in sys.argv:
        i = sys.argv.index("--table")
        table(sys.argv[i + 1] if len(sys.argv) > i + 1 else os.path.join(HERE, "..", "evidence", "intents-live-backing.json"))
        sys.exit(0)
    try:
        main()
    except exitproof.RpcUnavailable as e:
        sys.exit(f"the public RPC did not answer ({e}); retry in a minute")
