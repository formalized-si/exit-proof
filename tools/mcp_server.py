"""Minimal MCP (stdio, JSON-RPC 2.0) server exposing Exit Proof to AI agents. No dependencies; read-only RPC.

Tools
  exit_check(account_id)            exit stage of a NEAR contract with the evidence behind it: can the code change,
                                    who can move or freeze funds (strength of the guard, not key-holder identities),
                                    and on-chain certificates for the exact deployed code hash.
  exit_plan(pool_id, account_id)    for a delegator of a pool that runs the proved staking pool code: the calls that
                                    take all of its money out, when each becomes possible, and the covering theorem.
  token_check(token_id)             does a fungible token behave as the proved NEP-141 standard: the verdict for its
                                    code hash from runs of the deployed code, what is switched on now (a transfer
                                    tax), its methods beyond the standard, and whether its code can change.

Every answer carries `structuredContent` with a `status`: "ok", "not_found" (the account does not exist),
"unreadable" (the chain or the registry could not be read: nothing is known, treat it as unknown, never as a pass),
"bad_argument" or "error". `exit_check` and `token_check` take an optional `network` ("mainnet", the default, or
"testnet"). `exit_check` also takes `detail`: "stage" answers with the stage and its reasons from a few reads
(4 to 20), "full" (the default) also reads who holds each power (up to 100 reads). In `exit_check`, `exit_proof` is set only for a proof about leaving the contract; proofs of other
kinds are in `other_proofs` and never raise the stage. In `token_check`, `behaves_as_standard_now` is true, false or
null (unknown, with `unknown_because`).

An answer is kept for EXITPROOF_MCP_TTL seconds (default 60; 0 switches it off), so a repeated question inside one
task is answered without the network. Errors are never kept.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exit_plan  # noqa: E402
import exitproof  # noqa: E402
import rpc  # noqa: E402
import token_check  # noqa: E402

PROTOCOL = "2025-06-18"
STATUS = {"type": "string", "enum": ["ok", "not_found", "unreadable", "bad_argument", "error"]}
NETWORK = {"type": "string", "enum": ["mainnet", "testnet"], "description": "default mainnet"}
TOOLS = [
    {"name": "exit_check",
     "description": ("Before depositing into a NEAR contract: its exit stage (2 proven exit, 1 exit window, 0 keyholder "
                     "trust, U unproven), who can change its code or move/freeze funds held in it and how strongly "
                     "that power is guarded, and the on-chain certificates for the exact deployed code hash. "
                     "status other than ok means nothing is known."),
     "inputSchema": {"type": "object", "properties": {
         "account_id": {"type": "string"}, "network": NETWORK,
         "detail": {"type": "string", "enum": ["full", "stage"],
                    "description": "stage: the stage and its reasons with a few reads; who holds each power is not "
                                   "read. full (default): also how strongly each power is guarded (up to 100 reads)"}},
                     "required": ["account_id"]},
     "outputSchema": {"type": "object", "required": ["status"], "properties": {
         "status": STATUS, "error": {"type": "string"}, "account": {"type": "string"}, "code_hash": {"type": ["string", "null"]},
         "detail": {"type": "string", "enum": ["full", "stage"]},
         "stage": {"type": "object", "properties": {
             "level": {"type": "string", "enum": ["2", "1", "0", "U"]}, "label": {"type": "string"},
             "delay_seconds": {"type": ["integer", "null"], "description": "stage 1: seconds for which no deploy can be accepted"},
             "why": {"type": "array", "items": {"type": "string"}},
             "origin": {"type": "object", "description": "set when an exit theorem is registered for the code: whether the "
                        "account's deployment history shows that its state was made by this code alone (`ok`, `why`)"},
             "condition": {"type": "string", "description": "stage 2 only, when present: a condition on the live state "
                           "under which the theorem holds and which is not fully checked"}}},
         "no_code_change_path_found": {"type": "boolean"},
         "exit_proof": {"type": ["object", "null"], "description": "a proof about leaving this code; null otherwise"},
         "other_proofs": {"type": "array", "description": "proofs about this code that are not exit proofs"},
         "onchain_certificates": {"type": ["array", "null"], "description": "null: the registry was not read"},
         "capabilities": {"type": "object"}}}},
    {"name": "exit_plan",
     "description": ("For a delegator of a NEAR staking pool that runs the proved pool code: the exact calls that "
                     "withdraw everything, the earliest time of each, and the theorem that covers each step."),
     "inputSchema": {"type": "object",
                     "properties": {"pool_id": {"type": "string"}, "account_id": {"type": "string"}},
                     "required": ["pool_id", "account_id"]},
     "outputSchema": {"type": "object", "required": ["status"], "properties": {"status": STATUS, "error": {"type": "string"}}}},
    {"name": "token_check",
     "description": ("Before accepting, pricing or crediting a NEAR fungible token: does it behave as the proved NEP-141 "
                     "standard? Returns the verdict for the token's code hash (from runs of the deployed code with "
                     "monitors of the proved properties), whether a transfer tax or fee is on now, the methods it has "
                     "beyond the standard, and whether its code can change. behaves_as_standard_now is true, false or "
                     "null: null means unknown and must not be read as a pass."),
     "inputSchema": {"type": "object", "properties": {"token_id": {"type": "string"}, "network": NETWORK},
                     "required": ["token_id"]},
     "outputSchema": {"type": "object", "required": ["status"], "properties": {
         "status": STATUS, "error": {"type": "string"}, "account": {"type": "string"}, "code_hash": {"type": ["string", "null"]},
         "is_token": {"type": "boolean"}, "verdict": {"type": "string"},
         "core_standard_on_runs": {"type": ["boolean", "null"]},
         "behaves_as_standard_now": {"type": ["boolean", "null"]}, "unknown_because": {"type": "string"},
         "switches": {"type": "array"}, "code_follows_another_account": {"type": "boolean"},
         "intents_ledger": {"type": "object"}, "code_can_change": {"type": "object"}}}},
]


def reply(i, result=None, error=None):
    msg = {"jsonrpc": "2.0", "id": i}
    if error:
        msg["error"] = error
    else:
        msg["result"] = result
    sys.stdout.write(json.dumps(msg) + "\n")
    sys.stdout.flush()


def text(i, body, structured=None, is_error=False):
    res = {"content": [{"type": "text", "text": body}], "isError": is_error}
    if structured is not None:
        res["structuredContent"] = structured
    reply(i, res)


ACCOUNT_RE = __import__("re").compile(r"^(([a-z\d]+[-_])*[a-z\d]+\.)*([a-z\d]+[-_])*[a-z\d]+$")


def fail(i, status, message):
    text(i, message, {"status": status, "error": message}, is_error=True)


def bad_account(i, args, key):
    """An argument that cannot be a NEAR account id is refused at once, without a network call."""
    v = args.get(key)
    if not isinstance(v, str) or not (2 <= len(v) <= 64) or not ACCOUNT_RE.match(v):
        fail(i, "bad_argument", f"argument `{key}` must be a NEAR account id (2-64 characters, lowercase)")
        return True
    return False


def on_network(net, read):
    """Runs read() with the RPC client pointed at `net`, then puts the client back."""
    was = rpc.NETWORK[0]
    if net == was:
        return read()
    rpc.use_network(net)
    try:
        return read()
    finally:
        rpc.use_network(was)


TTL = float(os.environ.get("EXITPROOF_MCP_TTL", "60"))
_kept = {}


def remember(key, read):
    """read() at most once per TTL for the same question; a result with an error is not kept."""
    hit = _kept.get(key)
    if hit and time.time() - hit[0] < TTL:
        return hit[1]
    r = read()
    if TTL > 0 and "error" not in r:
        _kept[key] = (time.time(), r)
    return r


def call_tool(i, name, args):
    need = {"exit_check": ["account_id"], "exit_plan": ["pool_id", "account_id"], "token_check": ["token_id"]}.get(name, [])
    for key in need:
        if bad_account(i, args, key):
            return None
    net = args.get("network", rpc.NETWORK[0])
    if net not in ("mainnet", "testnet"):
        return fail(i, "bad_argument", "argument `network` must be mainnet or testnet")
    if name == "exit_check":
        acc = str(args.get("account_id", ""))
        detail = args.get("detail", "full")
        if detail not in ("full", "stage"):
            return fail(i, "bad_argument", "argument `detail` must be full or stage")
        full = detail == "full"
        rep = remember(("exit_check", net, acc, detail),
                       lambda: on_network(net, lambda: exitproof.scan(acc, history=full, controllers=full)))
        if "error" in rep:
            return fail(i, "not_found" if rep["error"].startswith("account not found") else "error",
                        rep["error"].replace("try --network", "use the argument network:"))
        return text(i, on_network(net, lambda: exitproof.render(rep)),
                    dict(exitproof.public_view(rep), status="ok", detail=detail))
    if name == "exit_plan":
        p = on_network(net, lambda: exit_plan.plan(str(args.get("pool_id", "")), str(args.get("account_id", ""))))
        if "error" in p:
            status = "not_found" if "account not found" in p["error"] else "error"
            return text(i, "no exit plan: " + p["error"], dict(p, status=status), is_error=True)
        return text(i, json.dumps(p, indent=1), dict(p, status="ok"))
    if name == "token_check":
        tok = str(args.get("token_id", ""))
        r = remember(("token_check", net, tok), lambda: on_network(net, lambda: token_check.check(tok)))
        if "error" in r:
            return fail(i, "not_found" if r["error"].startswith("account not found") else "error", r["error"])
        return text(i, token_check.render(r), dict(r, status="ok"))
    return reply(i, error={"code": -32602, "message": "unknown tool"})


def handle(req):
    m, i = req.get("method"), req.get("id")
    if m == "initialize":
        return reply(i, {"protocolVersion": PROTOCOL, "capabilities": {"tools": {}},
                         "serverInfo": {"name": "exit-proof", "version": "0.5.0"}})
    if m == "ping":
        return reply(i, {})
    if m == "tools/list":
        return reply(i, {"tools": TOOLS})
    if m == "tools/call":
        p = req.get("params") or {}
        try:
            return call_tool(i, p.get("name"), p.get("arguments") or {})
        except exitproof.RpcUnavailable as e:
            return fail(i, "unreadable", f"the chain could not be read ({str(e)[:200]}); nothing is known about this "
                                         f"account — treat it as unknown and ask again")
        except Exception as e:  # always answer: a silent failure would hang the client
            return fail(i, "error", f"exit-proof error: {type(e).__name__}: {str(e)[:300]}")
    if i is not None:
        return reply(i, error={"code": -32601, "message": "method not found"})


if __name__ == "__main__":
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except ValueError:
            reply(None, error={"code": -32700, "message": "parse error"})
            continue
        try:
            handle(req)
        except Exception as e:
            if req.get("id") is not None:
                reply(req["id"], error={"code": -32603, "message": f"internal error: {str(e)[:200]}"})
