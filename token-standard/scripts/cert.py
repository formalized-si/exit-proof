#!/usr/bin/env python3
"""Assemble certificate.json from the probe, the conformance comparison and properties.json.

usage: cert.py --wasm W --init-method M --init-args A --traces N --seed S --probe P.json
               [--conformance C.json] --properties PROPS.json --lean LEAN_DIR --out CERT.json
PASS requires: the probe deployed and initialized the token and located its accounts map; the
four foreign settlement calls failed and changed nothing; the initial state satisfies InitOK;
every trace matched the Lean model exactly and no property monitor fired; properties.json
matches the Lean sources the model was built from.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import properties as props_mod  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    for a in ("--wasm", "--init-method", "--init-args", "--traces", "--seed", "--probe", "--conformance",
              "--properties", "--lean", "--out"):
        ap.add_argument(a)
    a = ap.parse_args()
    wasm = open(a.wasm, "rb").read()
    probe = json.load(open(a.probe))
    conf = json.load(open(a.conformance)) if a.conformance and os.path.exists(a.conformance) else None
    pinned = json.load(open(a.properties))
    cur = props_mod.build(a.lean)
    props_ok = all(t0["statement_sha256"] == t1["statement_sha256"]
                   for p0, p1 in zip(pinned["properties"], cur["properties"])
                   for t0, t1 in zip(p0["theorems"], p1["theorems"])) and \
        pinned["lean_files_sha256"] == cur["lean_files_sha256"]
    reasons = []
    failed = set()
    if not props_ok:
        reasons.append("properties.json does not match the Lean sources")
    checks = probe.get("checks", {})
    if not probe.get("ok"):
        reasons.append(f"probe: {probe.get('error')}")
    else:
        for k in ("resolve_by_user", "resolve_by_contract", "resolve_by_token_key"):
            if checks.get(k) in (None, "ok"):
                reasons.append(f"check {k}: the foreign ft_resolve_transfer call did not fail")
                failed.add("P3")
        cb = checks.get("resolve_as_foreign_callback") or {}
        if cb.get("status") in (None, "ok"):
            reasons.append("check resolve_as_foreign_callback: another contract's callback ran ft_resolve_transfer")
            failed.add("P3")
        if not checks.get("balances_unchanged", False):
            reasons.append("check: foreign ft_resolve_transfer calls changed balances")
            failed.update({"P3", "P4"})
    if conf is None:
        if probe.get("ok"):
            reasons.append("no conformance result")
    else:
        if conf["verdict"] != "EXACT":
            reasons.append(f"conformance: {conf['mismatches']} divergences from the Lean model, "
                           f"monitor violations {conf['monitor_violations']}")
            failed.update(conf.get("failed_properties", []))
        if conf.get("init_ok_failures"):
            reasons.append("initial state does not satisfy InitOK")
    result = "PASS" if not reasons else "FAIL"
    cov = {}
    for p in pinned["properties"]:
        cov[p["id"]] = {"title": p["title"], "text": p["text"],
                        "theorems": [{"name": t["name"], "statement_sha256": t["statement_sha256"]} for t in p["theorems"]],
                        "status": "FAIL" if p["id"] in failed else ("PASS" if result == "PASS" else "not established")}
    try:  # run inside the Lean project, so that elan picks the toolchain pinned by lean-toolchain
        lean_ver = subprocess.run(["lean", "--version"], cwd=a.lean, capture_output=True, text=True,
                                  timeout=120).stdout.strip()
    except Exception:  # noqa: BLE001
        lean_ver = ""
    lean_ver = lean_ver or pinned.get("lean_toolchain")
    cert = {
        "certificate_version": 1,
        "result": result,
        "wasm": {"path": os.path.basename(a.wasm), "size": len(wasm), "sha256": hashlib.sha256(wasm).hexdigest(),
                 "sha256_base58": probe.get("wasm_sha256_base58"), "sim_code_hash": probe.get("sim_code_hash")},
        "standard": pinned["standard"],
        "model": {"lean": lean_ver, "lean_files_sha256": pinned["lean_files_sha256"],
                  "properties_json_sha256": hashlib.sha256(open(a.properties, "rb").read()).hexdigest(),
                  "properties_match_sources": props_ok},
        "init": {"method": a.init_method, "args": a.init_args, "state": probe.get("init_state")},
        "deployment_parameters": {"token_account": probe.get("token"), "accounts_map_prefix_hex": probe.get("prefix_hex"),
                                  "storage_byte_cost": probe.get("storage_byte_cost"),
                                  "token_reported_storage_min": probe.get("reported_storage_min")},
        "properties": cov,
        "failed_properties": sorted(failed),
        "reasons": reasons,
        "deterministic_checks": checks,
        "traces": {"requested": int(a.traces), "seed": int(a.seed),
                   "counts": conf["counts"] if conf else None,
                   "settlement_branches": conf.get("settlement_branches") if conf else None,
                   "receiver_behaviours": conf.get("receiver_behaviours") if conf else None,
                   "ft_on_transfer_outcomes": conf.get("ft_on_transfer_outcomes") if conf else None,
                   "interleaving": conf.get("interleaving") if conf else None,
                   "receipts_by_method": conf.get("receipts_by_method") if conf else None},
        "divergences": conf["mismatches"] if conf else None,
        "divergences_by_property": conf.get("mismatches_by_property") if conf else None,
        "diverging_traces": conf.get("diverging_traces") if conf else None,
        "diverging_traces_by_first_property": conf.get("diverging_traces_by_first_property") if conf else None,
        "monitor_violations": conf.get("monitor_violations") if conf else None,
        "monitor_examples": conf.get("monitor_examples") if conf else None,
        "first_divergence": conf.get("first_divergence") if conf else None,
        "what_pass_means": ("On every generated trace the token's receipts, return values, NEAR transfers, calls "
                            "(incl. the settlement callback's gas), NEP-141 events and state after every block are "
                            "exactly those of the Lean model of near-contract-standards 5.29.0, on which P1-P5 are "
                            "proved. This is a test of equivalence on these traces, not a proof for all inputs."),
    }
    with open(a.out, "w") as f:
        json.dump(cert, f, indent=1)
        f.write("\n")
    t = (conf or {}).get("counts", {})
    print(f"{result}  {cert['wasm']['sha256']}  traces={t.get('traces', 0)} receipts={t.get('receipts', 0)} "
          f"blocks={t.get('blocks', 0)}  failed={cert['failed_properties']}")
    d = cert["first_divergence"]
    if d:
        keep = {k: d.get(k) for k in ("trace", "h", "kind", "property", "method", "pred", "args", "detail")}
        print("first divergence:", json.dumps(keep)[:900])
    for r in reasons:
        print("reason:", r)
    print("certificate:", os.path.relpath(a.out))
    return 0 if result == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
