"""Exit plan for a delegator of a pool that runs the proved staking pool code (dry run: nothing is signed).

usage: exit_plan.py <pool account> <delegator account> [--json]

Reads the delegator's balances from the pool's own view method and the current epoch, and prints the calls that
take all of the delegator's money out, with the time each becomes possible and the theorem that covers the step.
Refuses to print a plan unless the pool is at exit stage 2 by the scanner's rules: the proved code, no access keys,
an exit certificate from an accepted attestor, and a state made by that code alone.

exit status: 0 a plan, 1 no plan (the reason is printed), 2 the chain could not be read
"""
import base64
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402
from rpc import RpcUnavailable, call, q  # noqa: E402

PROVED = "J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY"
UNLOCK_EPOCHS = 4  # NUM_EPOCHS_TO_UNLOCK in the contract


def view(acc, method, args=None):
    r = q("call_function", account_id=acc, method_name=method,
          args_base64=base64.b64encode(json.dumps(args or {}).encode()).decode())
    res = r.get("result", {})
    if isinstance(res, dict) and "result" in res:
        return json.loads(bytes(res["result"]).decode())
    raise RuntimeError(f"{acc}.{method}: {json.dumps(r.get('error') or res)[:160]}")


def epoch_clock():
    """(blocks left in the current epoch, epoch length in blocks, seconds per block measured over the last blocks)."""
    v = call("validators", [None])["result"]
    head = call("block", {"finality": "final"})["result"]["header"]
    cfg = call("EXPERIMENTAL_protocol_config", {"finality": "final"})["result"]
    length = int(cfg["epoch_length"])
    back = call("block", {"block_id": head["height"] - 2000})["result"]["header"]
    spb = (int(head["timestamp"]) - int(back["timestamp"])) / 1e9 / (head["height"] - back["height"])
    left = max(0, int(v["epoch_start_height"]) + length - head["height"])
    return left, length, spb, head["height"]


def plan(pool, who):
    for x in (pool, who):
        if not exitproof.ACCOUNT_RE.match(x or ""):
            return {"error": f"{x!r} is not a NEAR account id"}
    a = exitproof.account(pool)   # None only for an account that does not exist; any other failure is no answer
    if a is None:
        return {"error": f"{pool}: account not found"}
    if a["code_hash"] != PROVED:
        return {"error": f"{pool} does not run the proved staking pool code (code hash {a['code_hash'][:12]}…): no plan"}
    keys = exitproof.keys(pool)   # paginated: an account with more than 100 keys is read in full or not at all
    if keys:
        return {"error": f"{pool} has {len(keys)} access key(s): its code could be replaced; no plan"}
    # the same rule as the scanner: the proved code hash alone is not enough (certificate, origin of the state)
    stg = exitproof.scan(pool, history=False, controllers=False).get("stage") or {}
    if stg.get("level") != "2":
        return {"error": f"{pool} runs the proved pool code, but its exit stage is {stg.get('level')}: "
                         f"{'; '.join(stg.get('why') or [])}: no plan"}
    if exitproof.account(who) is None:
        return {"error": f"{who}: account not found"}
    acc = view(pool, "get_account", {"account_id": who})
    staked, unstaked = int(acc["staked_balance"]), int(acc["unstaked_balance"])
    left, length, spb, height = epoch_clock()
    steps = []
    wait_blocks = 0
    if staked > 0:
        steps.append({"call": f"{pool}.unstake_all()", "signer": who, "when": "now",
                      "effect": f"unstaked balance becomes at least {(staked + unstaked) / 1e24:.6f} NEAR",
                      "covered_by": "StakingPool.unstake_all_ok"})
        wait_blocks = left + (UNLOCK_EPOCHS - 1) * length
    elif unstaked > 0 and not acc["can_withdraw"]:
        wait_blocks = left + (UNLOCK_EPOCHS - 1) * length  # upper bound: the unlock epoch is not exposed by a view
    if staked > 0 or unstaked > 0:
        when = "now" if wait_blocks == 0 else (
            f"after {UNLOCK_EPOCHS} epoch changes" if staked > 0 else f"within {UNLOCK_EPOCHS} epoch changes")
        eta = None if wait_blocks == 0 else time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime(time.time() + wait_blocks * spb))
        steps.append({"call": f"{pool}.withdraw_all()", "signer": who, "when": when, "not_before_estimate": eta,
                      "effect": f"the pool transfers at least {(staked + unstaked) / 1e24:.6f} NEAR to {who}",
                      "covered_by": "StakingPool.withdraw_all_ok (needs the protocol to have returned the stake)"})
    # a delegator that is itself a contract (a lockup, for instance) signs nothing: its owner makes it call the pool
    d = q("view_account", account_id=who).get("result") or {}
    by_contract = d.get("code_hash") not in (None, "11111111111111111111111111111111") or bool(d.get("global_contract_hash"))
    return {"pool": pool, "delegator": who, "block_height": height,
            "delegator_is_contract": by_contract,
            "who_calls": ("the delegator is a contract: these calls are made by that contract, when the account that "
                          "controls it tells it to" if by_contract else "the delegator signs these calls itself"),
            # exact amounts in yoctoNEAR as strings; the *_NEAR fields are rounded for reading
            "staked_yocto": str(staked), "unstaked_yocto": str(unstaked),
            "staked_NEAR": staked / 1e24, "unstaked_NEAR": unstaked / 1e24,
            # with nothing in the pool there is nothing to withdraw, whatever the pool's view says
            "has_balance_in_pool": staked + unstaked > 0,
            "can_withdraw_now": bool(acc["can_withdraw"]) and unstaked > 0,
            "guarantee": "StakingPool.exit_guarantee for code hash " + PROVED,
            "nobody_else_can_reduce_it": "StakingPool.others_call, owner_methods",
            "steps": steps}


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if "--example" in sys.argv and len(args) == 1:
        # the first delegator the pool itself lists (its view method get_accounts)
        try:
            accs = view(args[0], "get_accounts", {"from_index": 0, "limit": 1})
        except Exception:
            accs = None
        if not accs:
            sys.exit("the pool did not answer get_accounts; give a delegator account explicitly")
        args.append(accs[0]["account_id"])
    if len(args) != 2:
        sys.exit("usage: exit_plan.py <pool account> <delegator account> [--json]\n"
                 "       exit_plan.py <pool account> --example    (takes the first delegator the pool lists)\n"
                 "Dry run: prints the calls that withdraw everything; signs nothing.")
    try:
        p = plan(args[0], args[1])
    except (RpcUnavailable, RuntimeError, OSError) as e:
        print(f"the chain could not be read ({str(e)[:120]}); no plan — retry in a minute or set EXITPROOF_RPC",
              file=sys.stderr)
        sys.exit(2)
    if "--json" in sys.argv:
        print(json.dumps(p, indent=1))
    elif "error" in p:
        print("no exit plan:", p["error"])
    else:
        print(f"exit plan for {p['delegator']} at {p['pool']} (block {p['block_height']})")
        print(f"  staked {p['staked_NEAR']:.6f} NEAR, unstaked {p['unstaked_NEAR']:.6f} NEAR")
        if not p["steps"]:
            print("  nothing to withdraw")
        for i, s in enumerate(p["steps"], 1):
            eta = f" (not before ~{s['not_before_estimate']})" if s.get("not_before_estimate") else ""
            print(f"  {i}. {s['call']} — {s['when']}{eta}: {s['effect']} [{s['covered_by']}]")
        print(f"  guarantee: {p['guarantee']}; others cannot reduce it: {p['nobody_else_can_reduce_it']}")
    sys.exit(1 if "error" in p else 0)
