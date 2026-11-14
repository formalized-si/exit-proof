#!/usr/bin/env python3
"""The kit's self-check (run it through ../check.sh).

usage: selfcheck.py [--traces N]

1. builds the trace generator and the reference token with its mutants (reference/build.py);
2. certifies the reference token: must be PASS;
3. certifies every mutant of reference/mutants.json with the same config: a mutant marked FAIL
   must fail with every monitor listed for it, at least one of them a monitor of the property the
   mutation breaks; a mutant marked OUTSIDE must stay silent and is reported as outside the
   monitors with the reason; the control must be PASS;
4. certifies every example of examples/examples.json: each must be PASS;
5. runs the guard cases of tests/guards/expected.json: none may end in PASS;
6. passes the configs of tests/setup/expected.json to try-config.sh: together they use every key
   of the config format;
7. verifies the reference certificate, and checks that an altered certificate is rejected.

Writes $TOKEN_MONITORS_BUILD/check/summary.json and summary.md and every certificate next to them.
Exit status: 0 iff all of the above holds.
"""
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kitlib  # noqa: E402

ROOT = kitlib.KIT_ROOT
BUILD = os.environ["TOKEN_MONITORS_BUILD"]
OUT = os.path.join(BUILD, "check")
problems = []


def say(text):
    print(text, flush=True)


def certify(name, wasm, config, extra=()):
    d = os.path.join(OUT, name)
    os.makedirs(d, exist_ok=True)
    cert = os.path.join(d, "certificate.json")
    if os.path.exists(cert):
        os.remove(cert)
    t0 = time.time()
    r = subprocess.run([os.path.join(ROOT, "certify.sh"), wasm, config, "--out", cert, *extra], capture_output=True, text=True)
    open(os.path.join(d, "output.txt"), "w").write(r.stdout + r.stderr)
    c = json.load(open(cert)) if os.path.exists(cert) else None
    return {"name": name, "exit": r.returncode, "seconds": round(time.time() - t0, 1), "certificate": c,
            "verdict": c["verdict"] if c else None,
            "fired": {n: m["violations"] for n, m in c["monitors"].items() if m["violations"]} if c else {},
            "output": (r.stdout + r.stderr).strip()}


def brief(r):
    c = r["certificate"]
    return {"name": r["name"], "exit": r["exit"], "verdict": r["verdict"], "seconds": r["seconds"], "fired": r["fired"],
            "wasm_sha256": c["wasm"]["sha256"] if c else None, "near_code_hash": c["wasm"]["near_code_hash"] if c else None,
            "traces": c["run"]["traces"] if c else None, "token_receipts": c["run"]["token_receipts"] if c else None,
            "checks": c["checks_total"] if c else None, "reasons": c["reasons"] if c else None}


def main():
    traces = "1000"
    if "--traces" in sys.argv:
        traces = sys.argv[sys.argv.index("--traces") + 1]
    os.makedirs(OUT, exist_ok=True)
    t_start = time.time()
    summary = {"kit": kitlib.kit_info(), "traces_per_run": int(traces)}

    say("== 1. build: trace generator, reference token, mutants")
    if subprocess.run([os.path.join(ROOT, "scripts", "build.sh")]).returncode != 0:
        say("FAIL: the trace generator did not build"); return 1
    ref_dir = os.path.join(BUILD, "reference")
    env = dict(os.environ)
    env.setdefault("TOKEN_TARGET_DIR", os.path.join(BUILD, "token-target"))
    if subprocess.run([sys.executable, "-I", "-B", os.path.join(ROOT, "reference", "build.py"), ref_dir], env=env).returncode != 0:
        say("FAIL: the reference token or a mutant did not build"); return 1
    builds = {b["id"]: b for b in json.load(open(os.path.join(ref_dir, "build.json")))}
    pinned = open(os.path.join(ROOT, "reference", "REFERENCE_WASM_SHA256")).read().split()[0]
    same = builds["reference"]["sha256"] == pinned
    say("reference wasm sha256 %s: %s" % (builds["reference"]["sha256"],
        "the same bytes as the pinned build" if same else
        "differs from the pinned build %s (another cargo-near or compiler version); the check goes on with this build" % pinned))
    summary["reference_wasm"] = {"sha256": builds["reference"]["sha256"], "pinned_sha256": pinned, "same_bytes_as_pinned": same}
    wasm = lambda i: os.path.join(ref_dir, "wasm", i + ".wasm")  # noqa: E731
    ref_cfg = os.path.join(ROOT, "examples", "reference.json")

    say("== 2. the reference token")
    r = certify("reference", wasm("reference"), ref_cfg, ["--traces", traces])
    say(r["output"])
    if r["exit"] != 0 or r["verdict"] != "PASS":
        problems.append("the reference token is not PASS")
    summary["reference"] = brief(r)
    ref_cert_path = os.path.join(OUT, "reference", "certificate.json")

    say("== 3. the mutants of the reference token")
    spec = json.load(open(os.path.join(ROOT, "reference", "mutants.json")))
    rows = []
    for m in spec["mutants"]:
        r = certify(m["id"], wasm(m["id"]), ref_cfg, ["--traces", traces])
        row = brief(r)
        row.update({"what": m["what"], "breaks": m["breaks"], "expect": m["expect"]})
        props = {r["certificate"]["monitors"][n]["property"] for n in r["fired"]} if r["certificate"] else set()
        if m["expect"] == "PASS":
            good = r["exit"] == 0 and r["verdict"] == "PASS"
            row["result"] = "control: PASS" if good else "NOT AS EXPECTED"
        elif m["expect"] == "FAIL":
            missing = [n for n in m["must_fire"] if n not in r["fired"]]
            good = r["exit"] == 1 and r["verdict"] == "FAIL" and not missing and m["breaks"] in props
            row["result"] = "caught" if good else "NOT AS EXPECTED"
            row["must_fire"] = m["must_fire"]
        else:
            good = r["exit"] == 0 and r["verdict"] == "PASS"
            row["result"] = "outside the monitors" if good else "NOT AS EXPECTED"
            row["why_outside"] = m["why_outside"]
        if not good:
            problems.append(f"mutant {m['id']}: expected {m['expect']}, got exit {r['exit']} verdict {r['verdict']} fired {sorted(r['fired'])}")
        say("%-30s %-22s exit %s  %s" % (m["id"], row["result"], r["exit"],
                                         ", ".join(f"{n} ({v})" for n, v in r["fired"].items()) or "no monitor fired"))
        rows.append(row)
    summary["mutants"] = rows
    real = [x for x in rows if x["expect"] != "PASS"]
    summary["mutants_caught"] = sum(1 for x in real if x["result"] == "caught")
    summary["mutants_outside"] = sum(1 for x in real if x["result"] == "outside the monitors")
    summary["mutants_total"] = len(real)

    say("== 4. the example configs")
    ex_rows = []
    man = json.load(open(os.path.join(ROOT, "examples", "examples.json")))
    for e in man["examples"]:
        src = e["wasm"]
        if "built" in src:
            w = wasm(src["built"])
        else:
            w = os.path.join(BUILD, "mainnet-wasm", src["sha256"][:16] + ".wasm")
            if not (os.path.exists(w) and kitlib.sha256_file(w) == src["sha256"]):
                os.makedirs(os.path.dirname(w), exist_ok=True)
                f = subprocess.run([sys.executable, "-I", "-B", os.path.join(ROOT, "scripts", "fetch_code.py"), src["mainnet_account"], w,
                                    "--sha256", src["sha256"]], capture_output=True, text=True)
                say((f.stdout + f.stderr).strip())
                if f.returncode != 0:
                    problems.append(f"example {e['name']}: the wasm could not be fetched")
                    ex_rows.append({"name": e["name"], "exit": None, "verdict": None, "error": "the wasm could not be fetched"})
                    continue
        r = certify("example-" + e["name"], w, os.path.join(ROOT, "examples", e["config"]), ["--traces", traces])
        say(r["output"].splitlines()[0] if r["output"] else "no output")
        if r["exit"] != 0 or r["verdict"] != "PASS":
            problems.append(f"example {e['name']} is not PASS")
        row = brief(r)
        row["name"] = e["name"]
        row["config"] = e["config"]
        row["source"] = src.get("mainnet_account") or ("built here: " + src["built"])
        ex_rows.append(row)
    summary["examples"] = ex_rows

    say("== 5. the guard cases (none may end in PASS)")
    g_rows = []
    gdir = os.path.join(ROOT, "tests", "guards")
    for g in json.load(open(os.path.join(gdir, "expected.json")))["guards"]:
        r = certify("guard-" + g["name"], wasm(g["wasm"]), os.path.join(gdir, g["config"]), g["args"])
        reasons = " | ".join(r["certificate"]["reasons"]) if r["certificate"] else ""
        good = r["exit"] == g["exit"] and r["verdict"] == g["verdict"] and r["exit"] != 0
        if g["reason_contains"]:
            good = good and g["reason_contains"] in reasons
        if g["exit"] == 3:
            good = good and r["certificate"] is None
        if not good:
            problems.append(f"guard {g['name']}: expected exit {g['exit']} {g['verdict']}, got exit {r['exit']} {r['verdict']}: {reasons[:200]}")
        say("%-18s exit %s %-13s %s" % (g["name"], r["exit"], r["verdict"] or "no certificate", "as expected" if good else "NOT AS EXPECTED"))
        g_rows.append({"name": g["name"], "exit": r["exit"], "verdict": r["verdict"], "as_expected": good, "why": g["why"],
                       "reasons": r["certificate"]["reasons"] if r["certificate"] else [(r["output"].splitlines() or ["no output"])[-1].strip(" -")]})
    summary["guards"] = g_rows

    say("== 6. config fields (tests/setup)")
    s_rows = []
    sdir = os.path.join(ROOT, "tests", "setup")
    for t in json.load(open(os.path.join(sdir, "expected.json")))["cases"]:
        cfg = os.path.join(sdir, t["config"])
        r = subprocess.run([os.path.join(ROOT, "try-config.sh"), wasm(t["wasm"]), cfg], capture_output=True, text=True)
        good = r.returncode == t["exit"] and t["output_contains"] in (r.stdout + r.stderr)
        row = {"name": t["name"], "covers": t["covers"], "try_exit": r.returncode, "certified": None}
        if good and t.get("certify_traces"):
            c = certify("setup-" + t["name"], wasm(t["wasm"]), cfg, ["--traces", str(t["certify_traces"])])
            good = c["exit"] == 0 and c["verdict"] == "PASS"
            row["certified"] = "%s on %s traces" % (c["verdict"], t["certify_traces"])
        row["as_expected"] = good
        if not good:
            problems.append(f"set-up case {t['name']}: try-config exit {r.returncode}, expected {t['exit']}; {row['certified'] or ''}")
        say("%-18s try-config exit %s %s %s" % (t["name"], r.returncode, row["certified"] or "", "as expected" if good else "NOT AS EXPECTED"))
        s_rows.append(row)
    summary["setup_cases"] = s_rows

    say("== 7. certificate verification")
    v_rows = []
    if os.path.exists(ref_cert_path):
        v = subprocess.run([os.path.join(ROOT, "verify-certificate.sh"), ref_cert_path, wasm("reference")], capture_output=True, text=True)
        good = v.returncode == 0
        v_rows.append({"case": "the reference certificate against the reference wasm", "exit": v.returncode, "as_expected": good})
        c = json.load(open(ref_cert_path))
        c["monitors"]["P3.foreign_resolve_fails"]["checks"] += 1
        alt = os.path.join(OUT, "reference", "altered-certificate.json")
        json.dump(c, open(alt, "w"))
        v2 = subprocess.run([os.path.join(ROOT, "verify-certificate.sh"), alt, wasm("reference")], capture_output=True, text=True)
        v_rows.append({"case": "the same certificate with one count changed", "exit": v2.returncode, "as_expected": v2.returncode == 1})
        v3 = subprocess.run([os.path.join(ROOT, "verify-certificate.sh"), ref_cert_path, wasm("M0_control")], capture_output=True, text=True)
        v_rows.append({"case": "the reference certificate against another wasm", "exit": v3.returncode, "as_expected": v3.returncode == 1})
    else:
        v_rows.append({"case": "no reference certificate", "exit": None, "as_expected": False})
    for x in v_rows:
        say("%-52s exit %s %s" % (x["case"], x["exit"], "as expected" if x["as_expected"] else "NOT AS EXPECTED"))
        if not x["as_expected"]:
            problems.append("certificate verification: " + x["case"])
    summary["verification"] = v_rows

    summary["problems"] = problems
    summary["ok"] = not problems
    summary["seconds"] = round(time.time() - t_start)
    json.dump(summary, open(os.path.join(OUT, "summary.json"), "w"), indent=1)
    L = ["# Self-check of the kit", "",
         f"Kit {summary['kit']['version']}, bundle `{summary['kit']['bundle_sha256']}`; {traces} traces per run; "
         f"{summary['kit']['simulator']}, {summary['kit']['runtime']}.", "",
         "## Reference token and mutants", "",
         "| Build | Change | Breaks | Result | Monitors that fired (violations) | Traces / token receipts |", "|---|---|---|---|---|---|"]
    rr = summary["reference"]
    L.append(f"| reference | near-sdk-rs fungible-token example, near-contract-standards 5.29.0 | - | {rr['verdict']} | "
             f"none | {rr['traces']} / {rr['token_receipts']} |")
    for x in rows:
        fired = ", ".join(f"`{n}` ({v})" for n, v in x["fired"].items()) or "none"
        res = x["result"] + (": " + x["why_outside"] if x.get("why_outside") else "")
        L.append(f"| {x['name']} | {x['what']} | {x['breaks'] or '-'} | {res} | {fired} | {x['traces']} / {x['token_receipts']} |")
    L += ["", f"Mutants caught: {summary['mutants_caught']} of {summary['mutants_total']}; outside the monitors: "
              f"{summary['mutants_outside']}.", "", "## Examples", "",
          "| Example | Wasm | Code hash | Verdict | Traces / token receipts | Checks |", "|---|---|---|---|---|---|"]
    for x in ex_rows:
        L.append(f"| {x['name']} | {x.get('source', '')} | `{x.get('near_code_hash')}` | {x.get('verdict') or x.get('error')} | "
                 f"{x.get('traces')} / {x.get('token_receipts')} | {x.get('checks')} |")
    L += ["", "## Guard cases", "", "| Case | Exit | Verdict | As expected | First reason |", "|---|---|---|---|---|"]
    for x in g_rows:
        L.append(f"| {x['name']} | {x['exit']} | {x['verdict'] or 'no certificate'} | {'yes' if x['as_expected'] else 'NO'} | "
                 f"{' '.join((x['reasons'][0] if x['reasons'] else '').split())[:200]} |")
    L += ["", "## Config fields", "", "| Case | Covers | try-config exit | Certificate | As expected |", "|---|---|---|---|---|"]
    for x in s_rows:
        L.append(f"| {x['name']} | {x['covers']} | {x['try_exit']} | {x['certified'] or '-'} | {'yes' if x['as_expected'] else 'NO'} |")
    L += ["", "## Certificate verification", ""] + [f"- {x['case']}: exit {x['exit']}, {'as expected' if x['as_expected'] else 'NOT as expected'}" for x in v_rows]
    L += ["", "Result: " + ("everything as expected." if not problems else "NOT as expected: " + "; ".join(problems)), ""]
    open(os.path.join(OUT, "summary.md"), "w").write("\n".join(L))
    say("")
    say("mutants caught: %d of %d; outside the monitors: %d" % (summary["mutants_caught"], summary["mutants_total"], summary["mutants_outside"]))
    say("summary: %s" % os.path.join(OUT, "summary.md"))
    if problems:
        say("RESULT: FAIL")
        for p in problems:
            say("  - " + p)
        return 1
    say("RESULT: PASS (%d s)" % summary["seconds"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
