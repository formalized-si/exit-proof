"""Numbers check: every number the documents quote from a run is the number in the evidence file of that run.

usage: numbers_check.py            prints one line per fact; exit status 0 only if every fact is found

The documents (README.md, CLAIMS.md, intents-proof/README.md, gated-upgrade/README.md) quote results of runs:
receipts replayed, states explored, tokens by verdict. The runs are repeated and the documents are edited by hand,
so the two drift apart. This script reads each evidence file, derives the numbers a document has to show, and
looks for them in the documents named for that fact:
  * a number is matched as a whole number (not inside a longer number or a decimal), whatever thousands separator
    the document uses;
  * the numbers of one fact must stand together: in one paragraph, one table row or one line of a JSON file — a
    number that happens to occur somewhere else in the document does not count;
  * for the claims quoted most often, every sentence of that form in the documents must carry the current numbers
    (`every`), so a stale copy of a claim is found and not only a missing new one.

What it does not do: it does not read the meaning of a sentence, and a number quoted in a form it has no rule for
is not checked. That an evidence file is the output of its run is what the check.sh of each directory is for;
that it is the output of the present sources is the provenance check at the end.
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_docs = {}
facts = []   # (ok, what, detail)


def doc(path):
    """Text of a document with thousands separators removed from numbers."""
    if path not in _docs:
        t = open(os.path.join(ROOT, path), encoding="utf-8").read()
        _docs[path] = re.sub(r"(?<=\d)[   ,](?=\d{3}(?!\d))", "", t)
    return _docs[path]


def load(path):
    return json.load(open(os.path.join(ROOT, path)))


def units(path):
    """A document cut into the pieces inside which the numbers of one fact must stand together: paragraphs, the
    rows of a table, the lines of a JSON file."""
    t = doc(path)
    if path.endswith(".json"):
        return t.split("\n")
    out = []
    for par in re.split(r"\n[ \t]*\n", t):
        lines = [x for x in par.split("\n") if x.strip()]
        out += lines if lines and all(x.lstrip().startswith("|") for x in lines) else [par]
    return out


def has(n, text):
    """`n` stands in `text` as a whole number: not inside a longer number, not the integer part of a decimal."""
    return re.search(rf"(?<![\d.]){re.escape(str(n))}(?!\d|\.\d)", text) is not None


def need(what, source, numbers, docs, near=None):
    """All of `numbers` must stand together in one unit of each of `docs`; with `near`, in a unit that has these words."""
    for d in docs:
        us = [u for u in units(d) if near is None or near in re.sub(r"\s+", " ", u)]
        best = max(us, key=lambda u: sum(has(n, u) for n in numbers), default="")
        missing = [n for n in numbers if not has(n, best)]
        where = f" near the words {near!r}" if near else ""
        facts.append((not missing, f"{what} [{source}] in {d}",
                      f"not found together{where}: {missing} (the closest place has {len(numbers) - len(missing)} of {len(numbers)})" if missing else ""))


def every(what, source, pattern, allowed, docs):
    """Every place in `docs` that matches `pattern` must carry one of the `allowed` tuples of numbers."""
    for d in docs:
        got = [tuple(int(x) for x in m.groups()) for m in re.finditer(pattern, re.sub(r"\s+", " ", doc(d)))]
        bad = sorted({g for g in got if g not in allowed})
        facts.append((not bad, f"{what}: every mention ({len(got)}) [{source}] in {d}", f"stale or wrong: {bad}" if bad else ""))


def need_text(what, source, texts, docs):
    for d in docs:
        flat = re.sub(r"\s+", " ", doc(d))
        missing = [t for t in texts if re.sub(r"\s+", " ", t) not in flat]
        facts.append((not missing, f"{what} [{source}] in {d}", f"not found: {missing}" if missing else ""))


def main():
    IP = "intents-proof/README.md"
    # --- replay of the deployed wasm through the Lean model
    src = "intents-proof/evidence/conformance.json"
    c = load(src)["replay"]
    std = c["standard_token"]
    need("replay, standard token: receipts, agree", src, [std["contract_steps"], std["agree"]], [IP])
    need("replay, mock tokens: receipts", src, [c["fee_mock"]["contract_steps"], c["reply_mock"]["contract_steps"]], [IP])
    need("replay, wNEAR receipts and compared", src, [std["wnear"], std["wnear_agree"]], [IP])
    w = std.get("world")
    if w:   # token and contract replayed together through the step function of the two-contract world
        need("world-level replay: receipts on the token and on the contract, agree", src,
             [w["token_receipts"], w["contract_receipts"], w["agree"]], [IP])
        facts.append((w["disagree"] == 0 and w["agree"] > 0, f"world-level replay has no disagreement [{src}]", ""))
    total = sum(v["contract_steps"] for v in c.values())
    need("replay, total receipts", src, [total], ["README.md", "CLAIMS.md", "tools/proofs.json", "docs/DEMO.md"])
    gate_steps = load("intents-proof/evidence/upgrade_4PMYYWqio2Q3.json")["replay"]["contract_steps"]
    every("receipts replayed", src, r"(?<!\d)(\d+) receipts(?: of the deployed wasm)? replayed", {(total,), (gate_steps,)},
          ["README.md", "CLAIMS.md", "tools/proofs.json", "docs/DEMO.md", IP])
    facts.append((all(v["disagree"] == 0 for v in c.values()), f"replay has no disagreement [{src}]", ""))
    # --- one-line changes of the model
    src = "intents-proof/evidence/model_mutants.json"
    mm = [m for m in load(src) if m.get("result") != "PASS"]
    det = sum(1 for m in mm if m.get("result") == "DETECTED")
    facts.append((all(m.get("result") in ("DETECTED", "EQUIVALENT") for m in mm), f"every model change is detected or listed as equivalent [{src}]",
                  str([m["id"] for m in mm if m.get("result") not in ("DETECTED", "EQUIVALENT")])))
    need_text("model changes noticed", src, [f"{det} are noticed"] if len(mm) != det else [f"all {det} are noticed"], [IP])
    need("model changes: total and noticed", src, [len(mm), det], ["README.md", "CLAIMS.md", "tools/proofs.json"])
    docs4 = ["README.md", "CLAIMS.md", "tools/proofs.json", IP]
    every("model changes noticed of all", src, r"(?<!\d)(\d+) of (\d+) one-line changes of the model", {(det, len(mm))}, docs4)
    every("model changes in all", src, r"(?<!\d)(?<!of )(\d+) one-line changes of the model", {(len(mm),)}, docs4)
    # --- source variants through the upgrade check
    src = "intents-proof/evidence/source_mutants.json"
    sm = [m for m in load(src) if m["id"] != "S0_control"]
    rej = sum(1 for m in sm if m.get("result") == "REJECTED")
    need_text("source variants rejected", src, [f"{rej} of {len(sm)} rejected"], [IP])
    s7 = next(m for m in sm if m["id"].startswith("S7"))
    need("source variant with the role check removed: times the monitor fired, receipts that disagree", src,
         [s7["monitors_fired"]["unauthorized_ran"], s7["replay_disagree"]], [IP])
    # --- the upgrade check on the newest commit of the contract
    src = "intents-proof/evidence/upgrade_4PMYYWqio2Q3.json"
    u = load(src)
    need("upgrade check on the newest commit: traces, receipts replayed", src, [u["traces"], u["replay"]["contract_steps"]], [IP, "CLAIMS.md"])
    need_text("upgrade check on the newest commit: verdict", src, [u["verdict"]], [IP, "CLAIMS.md"])
    facts.append((u["replay"]["disagree"] == 0 and not u["monitors_fired"], f"upgrade check on the newest commit: the run agrees [{src}]", ""))
    # --- monitors on the traces
    src = "intents-proof/evidence/monitors_summary.json"
    ms = load(src)
    need("monitors: receipts, backing checks, equalities at rest", src,
         [ms["receipts"], ms["backing_inequalities_checked_after_receipts"], ms["quiescent_equalities_checked"]], [IP])
    g = ms.get("guarded_calls_by_accounts_without_the_permission")
    if g is not None:
        need("monitors: guarded calls without the permission", src, [g], [IP, "README.md", "CLAIMS.md"])
    private = sum(ms["private_callback_attempts"].values())
    need("monitors: calls of private callbacks by other accounts", src, [private], [IP])
    need("monitors, as the harness README quotes them: receipts, backing checks, equalities at rest, guarded calls, "
         "calls with the auth flag off, private callbacks, paused entry points, spends by locked accounts", src,
         [ms["receipts"], ms["backing_inequalities_checked_after_receipts"], ms["quiescent_equalities_checked"], g,
          ms["calls_by_accounts_with_auth_by_predecessor_off"], private, ms["calls_to_paused_entry_points"],
          ms["spends_by_locked_accounts"]] + sorted(ms["violations"].values()), ["intents-proof/harness/README.md"])
    mk = load("intents-proof/evidence/monitors_summary_mock.json")
    need_text("monitors on the fee-keeping mock: traces with the backing monitor fired", "intents-proof/evidence/monitors_summary_mock.json",
              [f"{mk['traces_with_violations']} of {mk['traces']} traces"], [IP, "intents-proof/harness/README.md"])
    # --- TLC
    src = "intents-proof/evidence/tla_run.txt"
    t = open(os.path.join(ROOT, src)).read()
    states = re.findall(r"^(Standard|Large)[^\n]*?(\d+) distinct states found", t, re.M)
    cex = dict(re.findall(r"^(FeeToken|RefundFailedCall): Backing violated, as expected; counterexample of (\d+) states", t, re.M))
    facts.append((len(states) == 2 and len(cex) == 2, f"TLC summary has both scopes and both variants [{src}]", t[:200] if len(states) != 2 else ""))
    for k, n in states:
        need(f"TLC: distinct states, {k}", src, [n], [IP], near="distinct states")
    need("TLC: distinct states of the large scope", src, [n for k, n in states if k == "Large"], ["CLAIMS.md"])
    need_text("TLC: counterexample lengths", src,
              [f"shortest counterexample of {cex.get('FeeToken')} states", f"shortest counterexample of {cex.get('RefundFailedCall')} states"], [IP])
    # --- kernel re-check and number of statements
    src = "intents-proof/evidence/kernel_check.txt"
    decl = re.search(r"Checked (\d+) declarations", open(os.path.join(ROOT, src)).read()).group(1)
    need("second kernel: declarations", src, [decl], [IP, "README.md"], near="declarations")
    every("second kernel: declarations", src, r"(?<!\d)(\d+) declarations", {(int(decl),)}, [IP, "README.md", "CLAIMS.md"])
    src = "intents-proof/evidence/axioms.txt"
    n = sum(1 for line in open(os.path.join(ROOT, src)) if line.strip())
    need_text("Lean statements", src, [f"{n} statements"], ["README.md", "CLAIMS.md", IP])
    every("Lean statements", src, r"(?<!\d)(\d+) statements", {(n,)}, ["README.md", "CLAIMS.md", IP])
    # --- the live ledger of NEAR Intents
    src = "evidence/intents-live-backing.json"
    s = load(src)["summary"]
    cols = ["equal", "surplus", "DEFICIT", "unread"]
    rows = [f"| {v} | " + " | ".join(str(k.get(c, 0)) for c in cols) + " |" for v, k in s["by_verdict"].items()]
    rows.append(f"| all {s['fungible_tokens']} | " + " | ".join(str(s["relation"].get(c, 0)) for c in cols) + " |")
    need_text("live ledger: table rows", src, rows, [IP])
    need("live ledger: block", src, [s["block"]], [IP], near="block")
    need("live ledger: tokens with a standard verdict", src, [s["standard_verdict"]["tokens"]], [IP, "README.md"],
         near="standard verdict")
    every("live ledger: tokens with a standard verdict", src,
          r"(?<!\d)(\d+) tokens (?:whose code has|with) a standard verdict", {(s["standard_verdict"]["tokens"],)},
          [IP, "README.md", "docs/DEMO.md"])
    # --- token census
    src = "evidence/token-census.json"
    fam = load(src)["families"]
    by = {}
    for f in fam.values():
        by[f["verdict"]] = by.get(f["verdict"], 0) + (f.get("held_by_intents") or 0)
    stdn = by.get("STANDARD", 0) + by.get("STANDARD + EXTENSIONS", 0)
    ext = sum((f.get("held_by_intents") or 0) for f in fam.values() if f["verdict"] == "STANDARD + EXTENSIONS" and f.get("extension_effect"))
    run = stdn + by.get("DEVIATES", 0) + by.get("UNDER REVIEW", 0)
    need("token census: code hashes, tokens with a verdict, standard, deviating, under review, with a transfer-changing extension",
         src, [len(fam), run, stdn, by.get("DEVIATES", 0), by.get("UNDER REVIEW", 0), ext], ["README.md"])
    need("token census: code hashes", src, [len(fam)], ["CLAIMS.md", "README.md", "docs/ROADMAP.md"], near="code hashes")
    need("token census: standard, deviating, under review", src, [stdn, by.get("DEVIATES", 0), by.get("UNDER REVIEW", 0)],
         ["CLAIMS.md"])
    need("token census: with a transfer-changing extension, of the standard ones", src, [ext, stdn], ["CLAIMS.md"])
    need("token census: standard, deviating, with a transfer-changing extension", src, [run, stdn, by.get("DEVIATES", 0), ext], [IP])
    # --- token certification kit
    src = "token-monitors/reference/mutants.json"
    mu = [m for m in load(src)["mutants"] if m.get("expect") != "PASS"]
    caught = sum(1 for m in mu if m.get("expect") == "FAIL")
    need_text("token kit: mutants caught", src, [f"{caught} of {len(mu)} one-line mutants"], ["README.md", "CLAIMS.md"])
    certs = [load(os.path.join("evidence/token-certificates", f)) for f in sorted(os.listdir(os.path.join(ROOT, "evidence/token-certificates")))]
    facts.append((len(certs) >= 4 and all(c["verdict"] == "PASS" and c["violations_total"] == 0 for c in certs),
                  f"token certificates: {len(certs)} files, all PASS with no violation [evidence/token-certificates/]", ""))
    need("token kit: monitors", "evidence/token-certificates/", [len(certs[0]["monitors"])], ["README.md", "CLAIMS.md"])
    # --- gated upgrades
    src = "gated-upgrade/evidence/scenarios.json"
    g = load(src)
    need_text("gated upgrades: scenarios and checks", src, [f"{g['scenarios_total']} scenarios", f"{g['checks_total']} checks"], ["README.md", "CLAIMS.md"])
    src = "gated-upgrade/evidence/traces.json"
    g = load(src)
    need("gated upgrades: traces and receipts", src, [g["traces"], g["receipts"]], ["README.md"])
    facts.append((g["violations"] == 0, f"gated upgrades: no violation on the traces [{src}]", ""))
    # --- staking pools
    src = "evidence/pools-live.json"
    p = load(src)["summary"]
    need("pools on live state: pools checked, delegator accounts, block", src, [p["pools_checked"], p["delegator_accounts"], p["block_height"]], ["README.md"])
    facts.append((p["S1_solvent"] == p["pools_checked"] == p["K_no_keys"] and p["pools_failed_to_read"] == 0,
                  f"every pool read satisfies the precondition [{src}]", ""))
    src = "evidence/pools-origin.json"
    o = load(src)["summary"]
    facts.append((o["read"] == o["pools"] == o["one_deployment"] == o["one_deployment_made_by_another_account"] == p["pools_checked"]
                  and o["made_by"] == ["poolv1.near"],
                  f"every pool of the proved code has one code deployment, made by the factory [{src}]", str(o)))
    need_text("pools: origin", src, [f"Each of the {o['one_deployment']} has had exactly one code deployment"], ["README.md"])
    src = "evidence/stake-by-stage.json"
    share = load(src)["share_by_stage"]
    need_text("stake by stage", src, [f"{share['2']}% of NEAR is at stage 2" if isinstance(share, dict) else ""], ["README.md"])
    # --- the headline numbers of the README: the validators, the large contracts, the proof directories
    sb = load(src)
    top = [c for c in sb["by_code"] if c["stage"] == "2"][0]
    vrows = load("evidence/validators-census.json")["rows"]
    need_text("validators of the epoch, pools and stake of the proved code", "evidence/validators-census.json, " + src,
              [f"{len(vrows)} validators of one epoch", f"run by {top['pools']} validators ({top['stake_NEAR'] / 1e6:.1f}M NEAR)"],
              ["README.md"])
    need_text("pools on live state: stake", "evidence/pools-live.json", [f"{p['total_staked_NEAR'] / 1e6:.1f}M NEAR"], ["README.md"])
    cc = load("evidence/contracts-census.json")
    lv = [str((r.get("stage") or {}).get("level") if isinstance(r.get("stage"), dict) else r.get("stage")) for r in cc]
    single = sum(1 for r, l in zip(cc, lv) if l == "0" and any((x.get("guard") or {}).get("weakest") == "single-key"
                                                                 for x in (r.get("capabilities") or {}).get("code_change", [])))
    need("large contracts: scanned, at stage 0, by a single key, at stage 2, unproven", "evidence/contracts-census.json",
         [len(lv), lv.count("0"), single, lv.count("2"), lv.count("U")], ["README.md"], near="Large contracts.")
    ps = load("pool-proof/out/summary.json")
    need_text("pool: traces of the replay", "pool-proof/out/summary.json", [f"agree on {ps['traces']} random traces"], ["README.md"])
    pm = load("pool-mutants/evidence/results.json")["mutants"]
    noticed = sum(1 for m in pm if m["id"] != "P0" and m["traces_that_differ"] > 0)
    facts.append((pm[0]["traces_that_differ"] == 0 and noticed == len(pm) - 1,
                  "pool replay: the control agrees and every model change is noticed [pool-mutants/evidence/results.json]", ""))
    need_text("pool: model changes noticed", "pool-mutants/evidence/results.json", [f"{noticed} of {len(pm) - 1} one-line changes"],
              ["README.md"])
    wc = load("wnear-proof/evidence/conformance.json")["counts"]
    need_text("wNEAR: traces", "wnear-proof/evidence/conformance.json", [f"{wc['traces']} traces"], ["README.md"])
    u1, u2 = load("upgrade-window/evidence/conformance.json"), load("upgrade-window/evidence/conformance_seed777.json")
    um = [m for m in load("upgrade-window/evidence/mutants.json") if not m["id"].startswith("M0")]
    caught = sum(1 for m in um if m["result"] != "PASS")
    need_text("upgrade window: traces and mutants", "upgrade-window/evidence/", [f"{u1['traces'] + u2['traces']} traces, {caught} of {len(um)} mutants"],
              ["README.md"])
    tla = open(os.path.join(ROOT, "intents-proof/evidence/tla_run.txt")).read()
    states = int(re.search(r"Large .*?(\d+) distinct states", tla).group(1))
    need_text("TLA+: states of the large run", "intents-proof/evidence/tla_run.txt", [f"{round(states / 1e6)} million states"], ["README.md"])
    # --- the pictures: the pages they are rendered from hold the numbers as text (docs/assets/src/build.sh renders them)
    HERO, STAGES = "docs/assets/src/hero.html", "docs/assets/src/stages.html"
    need_text("pictures: share of stake at stage 2", src, [f"{share['2']}%"], [HERO, STAGES])
    need("picture, hero: receipts replayed", "intents-proof/evidence/conformance.json", [total], [HERO])
    need_text("pictures: large contracts by stage", "evidence/contracts-census.json",
              [f"{lv.count('2')} at stage 2 · {lv.count('0')} at stage 0", f"{lv.count('U')} unproven", f"{len(lv)} LARGE CONTRACTS"], [STAGES])
    need_text("picture, hero: large contracts at stage 0", "evidence/contracts-census.json",
              [f"Large contracts at stage 0, of {len(lv)}", f">{lv.count('0')}</strong>"], [HERO])
    # --- provenance: the evidence files behind the numbers of intents-proof/ were made from its present sources
    import importlib.util
    spec = importlib.util.spec_from_file_location("source_hash", os.path.join(ROOT, "intents-proof", "scripts", "source_hash.py"))
    sh = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(sh)
    now, rec = sh.source_hash(), sh.load()["files"]
    for f in ("axioms.txt", "check_run.txt", "check_run_4000.txt", "clean_check_run.txt", "conformance.json", "kernel_check.txt",
              "model_mutants.json", "monitors_summary.json", "monitors_summary_mock.json", "source_mutants.json",
              "upgrade_4PMYYWqio2Q3.json"):
        got = (rec.get(f) or {}).get("sources")
        facts.append((got == now, f"made from the present sources of intents-proof/ [intents-proof/evidence/{f}]",
                      "" if got == now else f"recorded as {str(got)[:12]}, the sources are {now[:12]} (scripts/source_hash.py)"))
    return facts


if __name__ == "__main__":
    res = main()
    bad = [f for f in res if not f[0]]
    for ok, what, detail in res:
        print(("ok   " if ok else "FAIL ") + what + (f" — {detail}" if detail and not ok else ""))
    print(f"{len(res) - len(bad)}/{len(res)} facts agree")
    sys.exit(0 if not bad else 1)
