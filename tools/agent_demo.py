"""A staking agent that checks the exit guarantee before it deposits (dry run: it never signs or sends).

usage: agent_demo.py <pool account> <amount NEAR> [--min-stage 2|1] [--min-window <hours>] [--attestors a.near,b.near]

Policy (a rule over evidence, not a heuristic): deposit only if the contract's exit stage is at least --min-stage
(default 2). Certificates count only if their attestor is on the agent's allowlist (default: exitproof.near) — the
registry records claims, and the agent decides whose claims it accepts:
  stage 2  no code-change path AND an on-chain "exit" certificate for the exact code hash, re-checkable by the
           command the certificate names;
  stage 1  code can change only after a visible staging delay (and exits cannot be paused by a privileged party);
           the delay left must be at least --min-window hours (default 24): a window of minutes is no window.
The agent stakes into staking pools only: the transaction it prints is the pool's deposit_and_stake, so a contract
without that method is refused. Exit status: 0 PROCEED, 2 REFUSE, 3 the chain could not be read.
If the policy holds, the agent prints the transaction it would sign (deposit_and_stake); otherwise it refuses and
says why. The same check is exposed to any MCP-capable agent as the `exit_check` tool (tools/mcp_server.py).
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402


def decide(pool, amount, min_stage, attestors=("exitproof.near",), min_window_h=24):
    if min_stage not in (1, 2):
        raise ValueError("min_stage must be 1 or 2")
    exitproof.ATTESTORS = tuple(attestors)   # the scanner's stage 2 counts certificates of the same attestors
    rep = exitproof.scan(pool, history=False)
    if "error" in rep:
        return False, [f"cannot read {pool}: {rep['error']}"], None
    pv = exitproof.public_view(rep)
    stg = pv["stage"]
    rank = {"2": 2, "1": 1, "0": 0, "U": 0}[stg["level"]]
    all_exit = [c for c in (pv.get("onchain_certificates") or []) if c["kind"] == "exit"]
    certs = [c for c in all_exit if c["attestor"] in attestors]
    reasons = []
    if rank < min_stage:
        reasons.append(f"exit stage {stg['level']} ({stg['label']}) is below the required stage {min_stage}")
        reasons += stg["why"]
        for x in pv["capabilities"]["code_change"]:
            reasons.append(f"code can change via {x['how']} ({exitproof.fmt_summary(x['guard'])})")
    if stg["level"] == "1" and min_stage <= 1 and (stg.get("delay_seconds") or 0) < min_window_h * 3600:
        reasons.append(f"the exit window left is {(stg.get('delay_seconds') or 0) / 3600:.1f} h, below the required {min_window_h} h")
    if stg["level"] == "1" and min_stage <= 1 and not stg.get("plugin_certified"):
        # without a certificate for this code the plugin and its delay are read from method names and the contract's
        # own views: a rule over evidence does not stake on that
        reasons.append("the exit window rests on method names and the contract's own views: this code hash has no "
                       "upgrade-window certificate from an accepted attestor")
    if "deposit_and_stake" not in (rep.get("exports") or []):
        reasons.append("the contract has no deposit_and_stake method: it is not a staking pool this agent can stake into")
    if min_stage >= 2 and not certs:
        extra = f" from an accepted attestor ({len(all_exit)} from others)" if all_exit else ""
        reasons.append(f"no on-chain exit certificate{extra} for code {pv['code_hash'][:12]}… in {exitproof.REGISTRY}")
    ok = not reasons
    tx = None
    if ok:
        tx = {"signer": "<your account>", "receiver": pool, "actions": [
            {"FunctionCall": {"method_name": "deposit_and_stake", "args": {}, "gas": 50_000_000_000_000,
                              "deposit": f"{amount} NEAR"}}]}
    return ok, reasons, {"tx": tx, "certificates": certs, "code_hash": pv["code_hash"], "stage": stg}


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1].startswith("-"):
        sys.exit("usage: agent_demo.py <pool account> <amount in NEAR> [--min-stage N] [--attestors a.near,b.near]\n"
                 "Dry run: prints the decision and the transaction it would sign; signs nothing.")
    pool, amount = sys.argv[1], sys.argv[2]
    try:
        if not float(amount) > 0:
            raise ValueError
    except ValueError:
        sys.exit(f"the amount must be a positive number of NEAR, got {amount!r}")
    min_stage = 2
    min_window_h = 24.0
    if "--min-window" in sys.argv:
        min_window_h = float(sys.argv[sys.argv.index("--min-window") + 1])
    if "--min-stage" in sys.argv:
        arg = sys.argv[sys.argv.index("--min-stage") + 1]
        if arg not in ("1", "2"):
            # stage 0 and U are "no exit known": a policy that accepts them is no policy
            sys.exit(f"--min-stage must be 1 or 2, got {arg!r}")
        min_stage = int(arg)
    attestors = ("exitproof.near",)
    if "--attestors" in sys.argv:
        attestors = tuple(sys.argv[sys.argv.index("--attestors") + 1].split(","))
    try:
        ok, reasons, info = decide(pool, amount, min_stage, attestors, min_window_h)
    except exitproof.RpcUnavailable as e:
        print(f"decision: REFUSE — the chain could not be read ({e}); nothing is known, so nothing is signed")
        sys.exit(3)
    print(f"intent: stake {amount} NEAR with {pool} (policy: exit stage >= {min_stage})")
    if ok:
        print(f"stage: {info['stage']['level']} — {info['stage']['label']}")
        for c in info["certificates"]:
            print(f"evidence: on-chain certificate by {c['attestor']} — {', '.join(c['theorems'][:2])} …; "
                  f"artifact {c['artifact_sha256'][:16]}…; re-check `{c['check_command']}`")
        print("decision: PROCEED (dry run, nothing signed). Transaction the agent would sign:")
        print(json.dumps(info["tx"], indent=1))
    else:
        print("decision: REFUSE")
        for r in reasons:
            print("  - " + r)
        sys.exit(2)
