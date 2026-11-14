#!/usr/bin/env python3
"""Compare the staking-pool model (Lean `poolmodel` output) with the sim traces.

Usage: python3 -I compare.py traces.jsonl model.jsonl results.json
       python3 -I compare.py traces.jsonl - results.json      (sim-only: env checks)

A trace is EXACT iff at every observation (init + every step) the model and the
sim agree on: ok flag, raw contract state, per-account views, total staked view,
number of accounts. Error texts are checked separately (model text must be a
substring of the sim text when both fail).

The run's verdict (results.json "verdict", last line of the output) is EXACT iff
every trace is EXACT, every error text matches and no environment check is
violated; the exit status is 0 for EXACT and 1 otherwise. In sim-only mode the
verdict is ENV-OK / ENV-VIOLATION (environment checks only).
"""
import json
import re
import sys
from collections import Counter, defaultdict


def load(path):
    out = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                o = json.loads(line)
                out[o["id"]] = o
    return out


def observations(tr):
    """[(label, step-or-None, obs)] for init and each step."""
    obs = [("init", tr["init"], tr["init"]["sim"])]
    for i, st in enumerate(tr["steps"]):
        label = st["method"] if st["kind"] == "call" else "env:" + st["what"]
        obs.append((f"{i}:{label}", st, st["sim"]))
    return obs


def total(env):
    return int(env["amount"]) + int(env["locked"])


def view_num(v):
    """Views return U128 as JSON strings and counts as numbers."""
    if isinstance(v, str):
        return v
    if isinstance(v, (int, float)):
        return str(int(v))
    return json.dumps(v, sort_keys=True)


def norm_err(e):
    if e is None:
        return None
    e = re.sub(r"\d{2,}", "N", e)
    e = re.sub(r"ed25519:\w+|secp256k1:\w+", "KEY", e)
    return e[:160]


def dict_diff(a, b, path=""):
    """Paths where two JSON values differ (first 12)."""
    out = []
    if isinstance(a, dict) and isinstance(b, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a:
                out.append(f"{path}/{k}: missing in sim, model={json.dumps(b[k])[:200]}")
            elif k not in b:
                out.append(f"{path}/{k}: missing in model, sim={json.dumps(a[k])[:200]}")
            else:
                out += dict_diff(a[k], b[k], f"{path}/{k}")
    elif a != b:
        out.append(f"{path}: sim={json.dumps(a)[:200]} model={json.dumps(b)[:200]}")
    return out[:12]


def compare_obs(sim, mod):
    """Differences between a sim observation and a model result (list of strings)."""
    d = []
    if bool(sim["ok"]) != bool(mod["ok"]):
        d.append(f"ok: sim={sim['ok']} ({sim.get('err')}) model={mod['ok']} ({mod.get('err')})")
    if sim["state"] != mod["state"]:
        d += ["state" + x for x in dict_diff(sim["state"], mod["state"])]
    if sim["views"] != mod["views"]:
        d += ["views" + x for x in dict_diff(sim["views"], mod["views"])]
    if view_num(sim["total_staked_view"]) != view_num(mod["total_staked_view"]):
        d.append(f"total_staked_view: sim={sim['total_staked_view']} model={mod['total_staked_view']}")
    if view_num(sim["num_accounts"]) != view_num(mod["num_accounts"]):
        d.append(f"num_accounts: sim={sim['num_accounts']} model={mod['num_accounts']}")
    return d


def env_checks(tr, mres, acc, upto=None):
    """(a) conservation, (b) PUA, (c) sim-fail/model-ok liquidity cases."""
    obs = observations(tr)
    # per-epoch max of total_staked_balance, plus the value carried into each epoch
    m = {}
    last_s = None
    last_epoch = None

    m_obs = {}

    def note(epoch, s):
        nonlocal last_s, last_epoch
        if last_epoch is not None and epoch > last_epoch:
            # epochs between keep the last value
            for j in range(last_epoch + 1, epoch + 1):
                m[j] = max(m.get(j, 0), last_s)
                m_obs[j] = max(m_obs.get(j, 0), last_s)
        m[epoch] = max(m.get(epoch, 0), s)
        m_obs[epoch] = max(m_obs.get(epoch, 0), s)
        last_s, last_epoch = s, epoch

    init = obs[0][2]
    note(init["env"]["epoch"], int(init["state"]["total_staked_balance"]))
    prev = init
    faulted = False
    for idx in range(1, len(obs)):
        label, st, o = obs[idx]
        # Fault steps (outside the protocol model) and everything after one in
        # the same trace are not env-checked: counted separately.
        if st.get("fault") or faulted:
            acc["fault_steps" if st.get("fault") else "post_fault_steps"] += 1
            faulted = True
            if st["kind"] == "call":
                acc["calls"] += 1
            note(o["env"]["epoch"], int(o["state"]["total_staked_balance"]))
            prev = o
            continue
        if st["kind"] == "call":
            acc["calls"] += 1
            k = st["epoch"]
            dep = int(st["deposit"])
            a_pre = int(st["balance"]) - dep
            l_pre = int(st["locked"])
            if a_pre + l_pre != total(prev["env"]):
                acc["env_pre_mismatch"] += 1
            # (b) PUA, before the call
            for j in range(last_epoch + 1, k + 1) if last_epoch is not None and k > last_epoch else []:
                m[j] = max(m.get(j, 0), last_s)
                m_obs[j] = max(m_obs.get(j, 0), last_s)
            win = max(m.get(j, 0) for j in range(k - 3, k + 1))
            ltb = int(prev["state"]["last_total_balance"])
            r = a_pre + l_pre - ltb
            acc["pua_checked"] += 1
            if r < 0:
                acc["negative_R"] += 1
            if l_pre > win + max(r, 0):
                acc["pua_violations"] += 1
                if len(acc["pua_examples"]) < 10:
                    acc["pua_examples"].append({"trace": tr["id"], "step": label, "epoch": k,
                                                "locked": str(l_pre), "window_max": str(win),
                                                "R": str(r)})
            # The call's own ping (first call of a new epoch) distributes R into
            # total_staked_balance before the method body runs; the pool's books
            # held S + R at that moment, so it counts in m_k (the theorem's m0).
            if o["ok"] and int(prev["state"]["last_epoch_height"]) != k:
                post_ping = int(prev["state"]["total_staked_balance"]) + max(r, 0)
                m[k] = max(m.get(k, 0), post_ping)
            # strict variant: window over observed states only (no post-ping S)
            win_obs = max(m_obs.get(j, 0) for j in range(k - 3, k + 1))
            if l_pre > win_obs + max(r, 0):
                acc["pua_obs_only_violations"] += 1
            # (b2) the Lean model's own PUA (World.PUA, evaluated by poolmodel on the simulator
            # balances before the call, with the ghost window World.hist)
            if mres is not None and (upto is None or idx <= upto) and "pua" in mres[idx]:
                pu = mres[idx]["pua"]
                acc["lean_pua_checked"] += 1
                if not pu["ok"]:
                    acc["lean_pua_violations"] += 1
                    if len(acc["lean_pua_examples"]) < 10:
                        acc["lean_pua_examples"].append({"trace": tr["id"], "step": label, **pu})
                if not pu.get("cons", True):
                    acc["lean_cons_violations"] += 1
            # (a) conservation over the call
            # transfer from the sim's own books (withdraw only changes the
            # predecessor's unstaked balance), so the check never depends on
            # the model; the model's transfer is cross-checked separately.
            transfer = 0
            if o["ok"] and st["method"] in ("withdraw", "withdraw_all"):
                p = st["pred"]
                before = int(prev["state"]["accounts"].get(p, {}).get("unstaked", "0"))
                after = int(o["state"]["accounts"].get(p, {}).get("unstaked", "0"))
                transfer = before - after
            in_sync = upto is None or idx <= upto
            if mres is not None and in_sync and o["ok"] and mres[idx]["ok"]:
                if int(mres[idx].get("transfer", "0") or 0) != transfer:
                    acc["transfer_mismatch"] += 1
            expect = (dep - transfer) if o["ok"] else 0
            delta = total(o["env"]) - (a_pre + l_pre)
            if delta != expect:
                acc["conservation_violations"] += 1
                if len(acc["conservation_examples"]) < 10:
                    acc["conservation_examples"].append({"trace": tr["id"], "step": label,
                                                         "delta": str(delta), "expected": str(expect),
                                                         "ok": o["ok"], "err": o.get("err")})
            # (c) liquidity / env-caused failures
            if mres is not None and in_sync and (not o["ok"]) and mres[idx]["ok"]:
                if len(acc["sim_fail_model_ok"]) < 30:
                    acc["sim_fail_model_ok"].append({"trace": tr["id"], "step": label,
                                                     "sim_err": o.get("err")})
            if st.get("crossed"):
                acc["crossed"] += 1
        else:
            d = total(o["env"]) - total(prev["env"])
            acc["env_income"][st["what"]] += d
            if d < 0:
                acc["env_negative_delta"] += 1
        note(o["env"]["epoch"], int(o["state"]["total_staked_balance"]))
        prev = o


def main():
    traces_path, model_path, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
    traces = load(traces_path)
    model = load(model_path) if model_path != "-" else None

    acc = {"calls": 0, "pua_checked": 0, "pua_violations": 0, "pua_obs_only_violations": 0, "pua_examples": [],
           "negative_R": 0, "transfer_mismatch": 0, "conservation_violations": 0, "conservation_examples": [],
           "sim_fail_model_ok": [], "crossed": 0, "env_pre_mismatch": 0,
           "env_income": Counter(), "env_negative_delta": 0,
           "fault_steps": 0, "post_fault_steps": 0,
           "lean_pua_checked": 0, "lean_pua_violations": 0, "lean_pua_examples": [], "lean_cons_violations": 0}
    ops = Counter()
    okfail = defaultdict(Counter)
    errs = Counter()
    errtext_mismatch = []
    errtext_ok = 0
    exact, mismatch, missing = 0, 0, 0
    details = []
    steps = 0
    mismatch_kinds = Counter()
    mismatch_causes = Counter()

    fam = defaultdict(Counter)
    fault_outcomes = Counter()
    for tid in sorted(traces):
        tr = traces[tid]
        upto = None
        family = tr.get("family", "normal")
        fam[family]["traces"] += 1
        fam[family]["steps"] += len(tr["steps"])
        fam[family]["calls"] += sum(1 for x in tr["steps"] if x["kind"] == "call")
        fam[family]["fault_steps"] += sum(1 for x in tr["steps"] if x.get("fault"))
        obs = observations(tr)
        steps += len(tr["steps"])
        for label, st, o in obs[1:]:
            if st["kind"] == "call":
                ops[st["method"]] += 1
                okfail[st["method"]]["ok" if o["ok"] else "fail"] += 1
                if not o["ok"]:
                    errs[norm_err(o.get("err"))] += 1
            else:
                ops["env:" + st["what"]] += 1
        mres = None
        if model is not None:
            mt = model.get(tid)
            if mt is None or len(mt.get("results", [])) != len(obs):
                missing += 1
                details.append({"trace": tid, "error": "model output missing or wrong length"})
                env_checks(tr, None, acc)
                continue
            mres = mt["results"]
            first = None
            for idx, (label, st, o) in enumerate(obs):
                d = compare_obs(o, mres[idx])
                if st is not None and st.get("fault"):
                    fault_outcomes[(st.get("fault_kind", st.get("what", "")), st["kind"],
                                    "sim ok" if o["ok"] else "sim FAIL " + str(norm_err(o.get("err"))),
                                    "model ok" if mres[idx]["ok"] else
                                    "model FAIL " + str(norm_err(mres[idx].get("err"))))] += 1
                if first is None and not o["ok"] and not mres[idx]["ok"]:
                    me, se = mres[idx].get("err") or "", o.get("err") or ""
                    if me and me in se:
                        errtext_ok += 1
                        fam[family]["errtext_ok"] += 1
                    else:
                        fam[family]["errtext_mismatch"] += 1
                        errtext_mismatch.append({"trace": tid, "step": label, "sim": se[:300],
                                                 "model": me[:300]})
                if d and first is None:
                    first = (idx, label, d)
            upto = None if first is None else first[0]
            if first is None:
                exact += 1
                fam[family]["exact"] += 1
            else:
                mismatch += 1
                fam[family]["mismatch"] += 1
                idx, label, d = first
                for x in d:
                    mismatch_kinds[x.split(":")[0]] += 1
                so, mo = obs[idx][2], mres[idx]
                if bool(so["ok"]) != bool(mo["ok"]):
                    cause = f"ok differs: sim={so['ok']} [{norm_err(so.get('err'))}] model={mo['ok']} [{norm_err(mo.get('err'))}]"
                else:
                    cause = "same ok, differs at " + d[0].split(":")[0]
                mismatch_causes[(label.split(":", 1)[1], cause)] += 1
                st = obs[idx][1]
                details.append({"trace": tid, "step": label, "diff": d,
                                "call": {k: st.get(k) for k in ("pred", "method", "args", "deposit",
                                                                 "epoch", "balance", "locked")}
                                if st is not None and st.get("kind") == "call" else None,
                                "sim_ok": obs[idx][2]["ok"], "sim_err": obs[idx][2].get("err"),
                                "model_ok": mres[idx]["ok"], "model_err": mres[idx].get("err")})
        env_checks(tr, mres, acc, upto if mres is not None else None)

    res = {
        "traces": len(traces), "steps": steps, "calls": acc["calls"],
        "model_compared": model is not None,
        "exact_traces": exact, "mismatch_traces": mismatch, "model_missing": missing,
        "errtext_match": errtext_ok, "errtext_mismatch_count": len(errtext_mismatch),
        "errtext_mismatch_examples": errtext_mismatch[:40],
        "families": {k: dict(v) for k, v in sorted(fam.items())},
        "fault_step_outcomes": [{"kind": k[0], "step": k[1], "sim": k[2], "model": k[3], "count": v}
                                for k, v in fault_outcomes.most_common()],
        "mismatch_kinds": dict(mismatch_kinds),
        "first_mismatch_causes": [{"method": k[0], "cause": k[1], "traces": v}
                                  for k, v in mismatch_causes.most_common()],
        "mismatch_details": details[:200],
        "op_histogram": dict(ops),
        "ok_fail_per_method": {k: dict(v) for k, v in sorted(okfail.items())},
        "error_histogram": dict(errs.most_common(80)),
        "env": {
            "conservation_violations": acc["conservation_violations"],
            "conservation_examples": acc["conservation_examples"],
            "model_vs_sim_transfer_mismatch": acc["transfer_mismatch"],
            "pua_checked": acc["pua_checked"], "pua_violations": acc["pua_violations"],
            "pua_examples": acc["pua_examples"], "negative_R": acc["negative_R"],
            "pua_obs_only_violations": acc["pua_obs_only_violations"],
            "lean_pua_checked": acc["lean_pua_checked"], "lean_pua_violations": acc["lean_pua_violations"],
            "lean_pua_examples": acc["lean_pua_examples"], "lean_cons_violations": acc["lean_cons_violations"],
            "env_income_by_step_kind": {k: str(v) for k, v in acc["env_income"].items()},
            "env_negative_delta": acc["env_negative_delta"],
            "pre_call_env_mismatch": acc["env_pre_mismatch"],
            "calls_crossing_epoch": acc["crossed"],
            "fault_steps_not_env_checked": acc["fault_steps"],
            "post_fault_steps_not_env_checked": acc["post_fault_steps"],
            "sim_fail_model_ok": acc["sim_fail_model_ok"],
        },
    }
    e = res["env"]
    problems = []
    if not traces:
        problems.append("no traces")
    if model is not None:
        for name, n in (("traces that differ from the model", mismatch),
                        ("traces without model output", missing),
                        ("error texts that differ", len(errtext_mismatch)),
                        ("model/sim transfer amounts that differ", e["model_vs_sim_transfer_mismatch"]),
                        ("calls failing in the sim but not in the model", len(e["sim_fail_model_ok"])),
                        ("World.PUA violations on sim balances", e["lean_pua_violations"]),
                        ("World.cons violations on sim balances", e["lean_cons_violations"])):
            if n:
                problems.append(f"{name}: {n}")
    for name, n in (("balance conservation violations", e["conservation_violations"]),
                    ("PUA violations", e["pua_violations"]),
                    ("pre-call balance mismatches", e["pre_call_env_mismatch"]),
                    ("calls crossing an epoch boundary", e["calls_crossing_epoch"])):
        if n:
            problems.append(f"{name}: {n}")
    if model is not None:
        res["verdict"] = "EXACT" if not problems else "MISMATCH"
    else:
        res["verdict"] = "ENV-OK" if not problems else "ENV-VIOLATION"
    res["problems"] = problems
    with open(out_path, "w") as f:
        json.dump(res, f, indent=1)

    print(f"traces {res['traces']}  steps {steps}  calls {acc['calls']}")
    for k, v in res["families"].items():
        print(f"  family {k:9s} traces {v.get('traces',0):5d} steps {v.get('steps',0):6d} "
              f"calls {v.get('calls',0):6d} fault-steps {v.get('fault_steps',0):4d} | "
              f"EXACT {v.get('exact',0)} MISMATCH {v.get('mismatch',0)} "
              f"errtext ok {v.get('errtext_ok',0)} / mismatch {v.get('errtext_mismatch',0)}")
    for c in res["fault_step_outcomes"][:12]:
        print(f"  fault {c['kind']:8s} {c['step']:4s} x{c['count']:<4d} {c['sim'][:70]} || {c['model'][:70]}")
    if model is not None:
        print(f"EXACT {exact}  MISMATCH {mismatch}  missing {missing}  "
              f"errtext ok {errtext_ok} / mismatch {len(errtext_mismatch)}")
        for c in res["first_mismatch_causes"][:15]:
            print(f"  {c['traces']:5d} traces  first mismatch at {c['method']}: {c['cause']}")
        for d in details[:5]:
            print("  mismatch:", json.dumps(d)[:600])
    print("ok/fail per method:")
    for k, v in sorted(okfail.items()):
        print(f"  {k:28s} ok {v['ok']:6d}  fail {v['fail']:6d}")
    print(f"env: conservation violations {e['conservation_violations']}, "
          f"PUA checked {e['pua_checked']} violations {e['pua_violations']} "
          f"(observed-states-only window: {e['pua_obs_only_violations']}), "
          f"negative R {e['negative_R']}, crossed {e['calls_crossing_epoch']}, "
          f"sim-fail/model-ok {len(e['sim_fail_model_ok'])}, "
          f"not env-checked: fault steps {e['fault_steps_not_env_checked']}, "
          f"after a fault {e['post_fault_steps_not_env_checked']}")
    print(f"lean World.PUA on sim balances: checked {e['lean_pua_checked']} violations {e['lean_pua_violations']}, "
          f"World.cons (ltb <= liquid+locked) violations {e['lean_cons_violations']}")
    print("top errors:")
    for k, v in errs.most_common(25):
        print(f"  {v:6d}  {k}")
    print("VERDICT", res["verdict"], "; ".join(problems))
    return 0 if not problems else 1


if __name__ == "__main__":
    sys.exit(main())
