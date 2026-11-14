"""Read-only NEAR mainnet JSON-RPC client with retries.

Transient failures (rate limits, timeouts, network errors) are retried with backoff across
several public endpoints. A transient failure that survives all retries raises RpcUnavailable,
so callers never mistake "the RPC did not answer" for "the account does not exist".
"""
import json
import os
import time
import urllib.error
import urllib.request

DEFAULT_RPC = {
    "mainnet": "https://rpc.mainnet.fastnear.com,https://free.rpc.fastnear.com,https://rpc.mainnet.near.org",
    "testnet": "https://rpc.testnet.fastnear.com,https://test.rpc.fastnear.com,https://rpc.testnet.near.org",
}
NETWORK = [os.environ.get("EXITPROOF_NETWORK", "mainnet")]
EPS = os.environ.get("EXITPROOF_RPC", DEFAULT_RPC[NETWORK[0]]).split(",")


def use_network(name):
    """Switch every later call to another network (mainnet | testnet)."""
    NETWORK[0] = name
    EPS[:] = os.environ.get("EXITPROOF_RPC", DEFAULT_RPC[name]).split(",")
TRANSIENT = ("TOO_MANY_REQUESTS", "TIMEOUT_ERROR", "NO_SYNCED_BLOCKS", "INTERNAL_ERROR", "Too Many Requests",
             "-429", "Rate limit", "rate limit", "DEPRECATED")
PACE = float(os.environ.get("EXITPROOF_PACE", "0.15"))
_last = [0.0]
_good = {}  # endpoint list -> index of the endpoint that answered last; the next call starts there


class RpcUnavailable(Exception):
    pass


def _post(url, body, timeout=10):
    req = urllib.request.Request(url, body, {"Content-Type": "application/json", "User-Agent": "exitproof-readonly"})
    return json.loads(urllib.request.urlopen(req, timeout=timeout).read())


def call(method, params, attempts=10, eps=None):
    """eps: endpoints to use instead of those of the current network.

    A call starts at the endpoint that answered last. An endpoint that says "too many requests" is answered by
    waiting, each time twice as long, before the next endpoint is asked: asking again at once only prolongs the
    refusals. An endpoint that does not answer at all is left after 10 s and the next one is asked at once."""
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
    err = None
    eps = eps or EPS
    slow = 40 if isinstance(params, dict) and params.get("request_type") == "view_code" else 10
    refused = 0
    for i in range(attempts):
        wait = PACE - (time.time() - _last[0])
        if wait > 0:
            time.sleep(wait)
        _last[0] = time.time()
        k = (_good.get(tuple(eps), 0) + i) % len(eps)
        url = eps[k]
        try:
            j = _post(url, body, slow)
        except (urllib.error.URLError, TimeoutError, OSError, ValueError) as e:
            err = f"{url}: {str(e)[:80]}"
            if any(t in str(e) for t in TRANSIENT):
                time.sleep(min(8, 0.5 * 2 ** refused))
                refused += 1
            continue
        blob = json.dumps(j.get("error", ""))
        if "error" in j and any(t in blob for t in TRANSIENT):
            err = f"{url}: {blob[:80]}"
            time.sleep(min(8, 0.5 * 2 ** refused))
            refused += 1
            continue
        _good[tuple(eps)] = k
        return j
    raise RpcUnavailable(f"{method}: {err}")


def q(req, block_id=None, **kw):
    """query at the latest final block, or at a pinned block height when block_id is given."""
    p = {"request_type": req}
    if block_id is None:
        p["finality"] = "final"
    else:
        p["block_id"] = block_id
    eps = kw.pop("eps", None)
    p.update(kw)
    return call("query", p, eps=eps)


def is_unknown_account(j):
    return "UNKNOWN_ACCOUNT" in json.dumps(j.get("error", ""))
