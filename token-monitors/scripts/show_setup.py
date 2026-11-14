#!/usr/bin/env python3
"""show_setup.py SETUP.json: prints what `ftmon try` did, for a person writing a config.
Exit status: 0 the token is set up and a run can start, 2 otherwise."""
import json
import sys

s = json.load(open(sys.argv[1]))
for c in s.get("calls", []):
    args = c.get("args", "")
    label = "ok" if c["ok"] else ("failed (allowed: may_fail)" if c.get("may_fail") else "FAILED")
    print("%-6s %s -> %s.%s(%s)%s" % (label, c["caller"], c["receiver"], c["method"],
                                       args if len(args) <= 160 else args[:157] + "...",
                                       "" if c.get("deposit", "0") == "0" else " deposit " + c["deposit"]))
    if not c["ok"]:
        print("       failure: %s" % c.get("failure"))
    for r in c.get("receipts", []):
        if not r["ok"]:
            print("       a receipt of this call failed: %s -> %s %s: %s" % (r["pred"], r["recv"], r.get("method") or "(no method)", r["status"]))
if s.get("stage") == "world":
    obs = s["observation"]
    print("ft_total_supply after the set-up: %s" % obs["supply"])
    held = {a: b for a, b in obs["bal"].items() if b not in (None, "0")}
    print("balances after the set-up: " + (", ".join(f"{a} {b}" for a, b in sorted(held.items())) or "none"))
    print("storage_balance_bounds: %s" % json.dumps(s.get("storage_balance_bounds")))
if s.get("ok"):
    w = s["world"]
    print("funder (hands out tokens to the other accounts): %s (%s)" % (w["funder"], w["funder_from"]))
    print("SET-UP OK: a certificate run can start")
    sys.exit(0)
print("SET-UP FAILED: %s" % s.get("error"))
sys.exit(2)
