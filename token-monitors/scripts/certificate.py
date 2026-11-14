#!/usr/bin/env python3
"""Writes the certificate of one run and decides the verdict.

usage: certificate.py --wasm TOKEN.wasm --config CONFIG.json --setup SETUP.json [--monitors MONITORS.json]
                      --traces N --seed S --out CERTIFICATE.json

SETUP.json is the output of `ftmon try`, MONITORS.json the output of monitors/monitors.py (absent
when the set-up failed and no trace was run).

Verdict and exit status:
  PASS          0   every monitor made checks, every kind of step the checks depend on happened,
                    and no check was a violation
  FAIL          1   at least one violation
  INCONCLUSIVE  2   no violation, but the token could not be set up, or a monitor made no check,
                    or a kind of step the checks depend on never happened; the reasons are listed
"""
import argparse
import datetime
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kitlib  # noqa: E402

sys.path.insert(0, os.path.join(kitlib.KIT_ROOT, "monitors"))
import monitors as monitors_mod  # noqa: E402

FORMAT = "nep141-monitors-certificate/1"


def result_digest(cert):
    """One hash for what a re-run must reproduce: inputs, kit, traces, counts and verdict."""
    core = {
        "wasm_sha256": cert["wasm"]["sha256"],
        "config_sha256": cert["config_sha256"],
        "kit_bundle_sha256": cert["kit"]["bundle_sha256"],
        "traces": cert["run"]["traces_requested"],
        "seed": cert["run"]["seed"],
        "trace_digest": cert["run"].get("trace_digest"),
        "monitors": {n: [m["checks"], m["violations"]] for n, m in cert["monitors"].items()},
        "verdict": cert["verdict"],
    }
    return kitlib.sha256_bytes(kitlib.canonical_json(core))


def main():
    ap = argparse.ArgumentParser()
    for a in ("--wasm", "--config", "--setup", "--out"):
        ap.add_argument(a, required=True)
    ap.add_argument("--monitors")
    ap.add_argument("--traces", type=int, required=True)
    ap.add_argument("--seed", type=int, required=True)
    a = ap.parse_args()

    wasm = open(a.wasm, "rb").read()
    cfg = json.load(open(a.config))
    setup = json.load(open(a.setup))
    mon = json.load(open(a.monitors)) if a.monitors and os.path.exists(a.monitors) else None
    token = cfg.get("token_account", kitlib.DEFAULT_TOKEN)
    resolve = cfg.get("resolve_method", "ft_resolve_transfer")
    try:
        exports = kitlib.wasm_exports(wasm)
    except (ValueError, IndexError) as e:
        exports = None
        export_error = str(e)

    reasons, inconclusive = [], []
    if not setup.get("ok"):
        what = "the init or a setup call failed" if setup.get("stage") == "calls" else "the set-up left a world the monitors cannot judge"
        inconclusive.append(f"set-up: {what}: {setup.get('error')}")
    if mon is None:
        if setup.get("ok"):
            inconclusive.append("no trace was run")
        monitors = {n: {"property": p, "statement": s, "checks": 0, "violations": 0} for n, p, s in monitors_mod.MONITORS}
    else:
        monitors = {}
        for n, m in mon["monitors"].items():
            e = {"property": m["property"], "statement": m["statement"], "checks": m["checks"], "violations": m["violations"]}
            if m["violations"]:
                e["violations_by_step"] = m["violations_by_step"]
                e["examples"] = m["examples"]
                ex = m["examples"][0]
                reasons.append(f"{n}: {m['violations']} violation(s) in {m['checks']} checks; first example: trace {ex['trace']}, "
                               f"round {ex['round']}, {ex['step']}: {ex['detail']}")
            monitors[n] = e
        for x in mon["inconclusive"]:
            if "monitor" in x:
                inconclusive.append(f"{x['monitor']} made no check: {x['reason']}")
            elif "monitors" in x:
                inconclusive.append(f"{', '.join(x['monitors'])}: {x['reason']}")
            else:
                inconclusive.append(x["reason"])
        if mon["traces"] != a.traces:
            inconclusive.append(f"{mon['traces']} traces were judged, {a.traces} were requested")
    violations = sum(m["violations"] for m in monitors.values())
    if violations:
        verdict = "FAIL"
    elif inconclusive:
        verdict = "INCONCLUSIVE"
        reasons = list(inconclusive)
    else:
        verdict = "PASS"

    # --- what the run exercised, and what it did not ---
    in_setup = {}
    for c in setup.get("calls", []):
        for r in c.get("receipts", []):  # the call itself and every receipt it caused on the token
            if r.get("recv") == token and r.get("method"):
                in_setup.setdefault(r["method"], []).append(bool(r.get("ok")))
    in_traces = (mon or {}).get("methods", {})
    not_checked = [
        "NEAR-side storage accounting of NEP-145: the deposits the token keeps, the refunds it pays, the storage "
        "minimum, and that the token stays able to pay its refunds (property P5, except the balance side of "
        "storage_unregister)",
        "gas: the gas the token gives to ft_on_transfer and to its settlement callback, and behaviour at gas limits",
        "events (NEP-297 logs), error texts and the contents of ft_metadata",
        "the deployed contract: its state, access keys, owner rights and upgrade path; the run is about the code "
        "initialized with the config's arguments in a simulator",
        f"inputs outside the {a.traces} random traces of this run: the verdict is agreement on these traces, not a proof for all inputs",
    ]
    exp = None
    if exports is None:
        not_checked.append(f"the list of exported methods could not be read from the wasm ({export_error})")
    else:
        standard = set(kitlib.NEP141 + kitlib.NEP145 + kitlib.NEP148 + [resolve])
        init_method = (cfg.get("init") or {}).get("method")
        never = [m for m in exports if m not in in_traces and m not in in_setup]
        setup_only = [m for m in exports if m not in in_traces and m in in_setup]
        never_ok = [m for m in exports if m in in_traces and in_traces[m]["successful"] == 0 and not any(in_setup.get(m, []))]
        exp = {
            "count": len(exports),
            "standard_missing": sorted(standard - set(exports)),
            "outside_the_standards": [m for m in exports if m not in standard and m != init_method],
            "never_called": never,
            "called_only_by_the_setup": setup_only,
            "called_but_never_successful": never_ok,
        }
        if never:
            not_checked.append("exported methods that no call of this run reached (their effect on balances is unknown): " + ", ".join(never))
        if setup_only:
            not_checked.append("exported methods called only by the set-up, never inside a trace: " + ", ".join(setup_only))
        if never_ok:
            not_checked.append("exported methods that were called but never succeeded: " + ", ".join(never_ok))
        if exp["standard_missing"]:
            not_checked.append("standard methods the wasm does not export: " + ", ".join(exp["standard_missing"]))
    if mon is not None:
        succeeded = {k.rsplit(" ", 1)[0] for k, v in mon["operations"].items() if k.endswith(" ok") and v}
        never_op = [o for o in ("ft_transfer", "ft_transfer_call", "storage_deposit", "storage_withdraw", "storage_unregister")
                    if o not in succeeded]
        if never_op:
            not_checked.append("kinds of generated operations that never succeeded: " + ", ".join(never_op))
        if mon["counts"].get("balance_views_without_a_number"):
            not_checked.append("ft_balance_of of a valid account id did not return a number in a string %d time(s); such a "
                               "balance counts as 0" % mon["counts"]["balance_views_without_a_number"])

    counts = (mon or {}).get("counts", {})
    cert = {
        "format": FORMAT,
        "verdict": verdict,
        "reasons": reasons,
        "wasm": {"file": os.path.basename(a.wasm), "bytes": len(wasm), "sha256": kitlib.sha256_bytes(wasm),
                 "near_code_hash": kitlib.near_code_hash(wasm)},
        "config": cfg,
        "config_sha256": kitlib.config_sha256(cfg),
        "run": {
            "traces_requested": a.traces,
            "traces": counts.get("traces", 0),
            "seed": a.seed,
            "rounds": sum(v for k, v in counts.items() if k.startswith("rounds_")),
            "blocks": counts.get("blocks", 0),
            "token_receipts": counts.get("token_receipts", 0),
            "token_receipts_successful": counts.get("token_receipts_ok", 0),
            "trace_digest": (mon or {}).get("trace_digest"),
        },
        "setup": {
            "ok": bool(setup.get("ok")),
            "token_account": token,
            "calls": [{"caller": c.get("caller"), "receiver": c.get("receiver"), "method": c.get("method"),
                       "ok": c.get("ok"), "failure": c.get("failure")} for c in setup.get("calls", [])],
            "supply": (setup.get("world") or {}).get("supply"),
            "holders": (setup.get("world") or {}).get("holders"),
            "funder": (setup.get("world") or {}).get("funder"),
            "funder_from": (setup.get("world") or {}).get("funder_from"),
            "watched_accounts": (setup.get("world") or {}).get("watched_accounts"),
            "error": setup.get("error"),
        },
        "monitors": monitors,
        "checks_total": sum(m["checks"] for m in monitors.values()),
        "violations_total": violations,
        "coverage": (mon or {}).get("coverage", {}),
        "operations": (mon or {}).get("operations", {}),
        "exports": exp,
        "not_checked": not_checked,
        "kit": kitlib.kit_info(),
        "created_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
    if verdict == "FAIL" and inconclusive:
        cert["also_inconclusive"] = inconclusive
    cert["result_digest"] = result_digest(cert)
    with open(a.out, "w") as f:
        json.dump(cert, f, indent=1)
        f.write("\n")
    print(f"{verdict}  {os.path.basename(a.wasm)}  code hash {cert['wasm']['near_code_hash']}  traces {cert['run']['traces']}  "
          f"token receipts {cert['run']['token_receipts']}  checks {cert['checks_total']}  violations {violations}")
    for r in reasons[:12]:
        print("  - " + r)
    if len(reasons) > 12:
        print(f"  ... {len(reasons) - 12} more in the certificate")
    print(f"certificate: {a.out}")
    return {"PASS": 0, "FAIL": 1, "INCONCLUSIVE": 2}[verdict]


if __name__ == "__main__":
    sys.exit(main())
