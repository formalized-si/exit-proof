"""Watch: what changed since the last look at a set of contracts (read-only).

usage: watch.py <account> [<account> ...] [--file accounts.txt] [--state watch-state.json] [--network testnet]

For every account the tool reads a short fingerprint — code hash, exit stage, number of full-access keys, the
upgrade plugin's delay and staged code, the certificates registered for the code hash, and for a token whether a
transfer tax is on — compares it with the fingerprint saved by the previous run and prints one line per change:

  CODE CHANGED      the certificates of the old code no longer apply; the proof has to be re-run on the new code
  STAGE             the exit stage moved (for example 1 -> 0 when an upgrade delay was removed)
  UPGRADE STAGED    new code is announced; the line says until when a deploy cannot be accepted
  KEYS              a full-access key appeared or disappeared
  DELAY             the upgrade delay changed
  CERTIFICATES      a certificate was added or revoked for the current code
  TAX               a token switched its transfer tax on or off
  ACCOUNT GONE      the account no longer exists (or appeared again)

The first run only records the state. Exit status: 0 no change, 1 at least one change, 3 an RPC did not answer
(nothing is recorded for that account). Meant for a scheduler: run it every few minutes and forward the lines.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402
import rpc  # noqa: E402
import token_check  # noqa: E402


def fingerprint(acc):
    rep = exitproof.scan(acc, history=False, controllers=False)
    if "error" in rep:
        return {"error": rep["error"]}
    st = rep.get("stage") or {}
    roles = rep.get("roles") or {}
    delay = (roles.get("upgrade_delay_status") or {}).get("staging_duration")
    fp = {
        "code_hash": rep.get("effective_code_hash") or rep.get("code_hash"),
        "stage": st.get("level"),
        "full_access_keys": len(rep.get("full_access_keys") or []),
        "upgrade_delay_ns": int(delay) if delay not in (None, "") else None,
        "staged_code_hash": roles.get("staged_code_hash") or None,
        "window_seconds": st.get("delay_seconds"),
        # None: the registry did not answer on this run; that is not a change of certificates
        "certificates": (None if rep.get("onchain_certificates") is None
                         else sorted({exitproof.cert_kind(c) for c in rep["onchain_certificates"]})),
    }
    exports = rep.get("exports") or []
    if "get_tax" in exports:
        t = token_check.tax_now(acc, exports) or {}
        fp["tax_on"] = bool(t.get("on")) if t.get("readable") else None
    return fp


def changes(acc, old, new):
    out = []
    if old.get("code_hash") != new.get("code_hash"):
        had = ", ".join(old.get("certificates") or []) or "none"
        out.append(f"CODE CHANGED     {acc}: {str(old.get('code_hash'))[:12]}… -> {str(new.get('code_hash'))[:12]}…; "
                   f"certificates of the old code: {had}; of the new code: {', '.join(new.get('certificates') or []) or 'none'}")
    if old.get("stage") != new.get("stage"):
        out.append(f"STAGE            {acc}: {old.get('stage')} -> {new.get('stage')}")
    if new.get("staged_code_hash") and old.get("staged_code_hash") != new.get("staged_code_hash"):
        w = new.get("window_seconds")
        until = time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime(time.time() + w)) if w else "now"
        out.append(f"UPGRADE STAGED   {acc}: code {str(new['staged_code_hash'])[:12]}…; no deploy can be accepted before {until}")
    if old.get("staged_code_hash") and not new.get("staged_code_hash") and old.get("code_hash") == new.get("code_hash"):
        out.append(f"UPGRADE STAGED   {acc}: the staged code was withdrawn")
    if old.get("full_access_keys") != new.get("full_access_keys"):
        out.append(f"KEYS             {acc}: full-access keys {old.get('full_access_keys')} -> {new.get('full_access_keys')}")
    if old.get("upgrade_delay_ns") != new.get("upgrade_delay_ns"):
        out.append(f"DELAY            {acc}: upgrade delay {old.get('upgrade_delay_ns')} -> {new.get('upgrade_delay_ns')} ns")
    if (old.get("code_hash") == new.get("code_hash") and old.get("certificates") is not None
            and new.get("certificates") is not None and old.get("certificates") != new.get("certificates")):
        out.append(f"CERTIFICATES     {acc}: {old.get('certificates')} -> {new.get('certificates')}")
    if "tax_on" in new and old.get("tax_on") != new.get("tax_on") and old.get("tax_on") is not None and new.get("tax_on") is not None:
        out.append(f"TAX              {acc}: transfer tax {'on' if old.get('tax_on') else 'off'} -> {'on' if new.get('tax_on') else 'off'}")
    return out


if __name__ == "__main__":
    argv = sys.argv[1:]
    state_path, accs = "watch-state.json", []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--state":
            state_path = argv[i + 1]; i += 2
        elif a == "--file":
            accs += [x.strip() for x in open(argv[i + 1]) if x.strip() and not x.startswith("#")]; i += 2
        elif a == "--network":
            rpc.use_network(argv[i + 1]); i += 2
        elif a.startswith("--"):
            sys.exit(__doc__)
        else:
            accs.append(a); i += 1
    if not accs:
        sys.exit(__doc__)
    state = json.load(open(state_path)) if os.path.exists(state_path) else {}
    key = lambda acc: f"{rpc.NETWORK[0]}:{acc}"  # noqa: E731
    events, unanswered = [], 0
    for acc in accs:
        try:
            new = fingerprint(acc)
        except exitproof.RpcUnavailable:
            print(f"NO ANSWER        {acc}: the public RPC did not answer; state kept")
            unanswered += 1
            continue
        old = state.get(key(acc))
        if old is None:
            print(f"RECORDED         {acc}: stage {new.get('stage')}, code {str(new.get('code_hash'))[:12]}…"
                  + (f", certificates {', '.join(new['certificates'])}" if new.get("certificates") else ""))
        elif "error" in new and "error" not in old:
            events.append(f"ACCOUNT GONE     {acc}: {new['error']}; it was at stage {old.get('stage')} with code "
                          f"{str(old.get('code_hash'))[:12]}…")
        elif "error" in old and "error" not in new:
            events.append(f"ACCOUNT GONE     {acc}: the account exists again, stage {new.get('stage')}, code "
                          f"{str(new.get('code_hash'))[:12]}…")
        elif "error" not in new and "error" not in old:
            if new.get("certificates") is None:
                new["certificates"] = old.get("certificates")   # keep the last reading of the registry
            if "tax_on" in new and new["tax_on"] is None:
                new["tax_on"] = old.get("tax_on")               # and of the tax: a switch after an unread run is a change
            events += changes(acc, old, new)
        state[key(acc)] = new
    json.dump(state, open(state_path, "w"), indent=1)
    for e in events:
        print(e)
    if not events:
        print(f"no change in {len(accs) - unanswered} account(s)")
    sys.exit(1 if events else (3 if unanswered else 0))
