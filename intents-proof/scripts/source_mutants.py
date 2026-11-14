"""Sensitivity of the upgrade gate: one-line changes of the contract's Rust source (the deployed commit) are built
and passed through scripts/verify_upgrade.sh. The unchanged source must give CARRIES OVER; every change must be rejected: DIVERGES when the run sees it,
NEEDS REVIEW when only the static part does.

usage: source_mutants.py <clone of near/intents> <work dir> <result.json> [traces]
Needs docker (the image the contract names) and a built kit (./check.sh).
"""
import json, os, shutil, subprocess, sys

SRC, WORK, OUT = (os.path.abspath(a) for a in sys.argv[1:4])
N = sys.argv[4] if len(sys.argv) > 4 else "200"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COMMIT = "16d04f6ec4401263f8914638710260da50bb46b0"
IMG = "sourcescan/cargo-near:0.22.0-rust-1.97.1@sha256:7467038bdddc86484b73b416eeadce926ff59013e128e53dec5a19e1cb4b2234"
W = "contracts/defuse/src/contract/tokens/nep141/withdraw.rs"
D = "contracts/defuse/src/contract/tokens/nep141/deposit.rs"
F = "contracts/defuse/src/contract/tokens/nep245/force.rs"
NL = chr(10)
MUTANTS = [
    ("S0_control", "no change", None, None, None),
    ("S1_unparsable_reply_means_used", "an unparsable reply of ft_transfer_call is taken as everything delivered", W,
     "Ok(Err(_deserialize_err)) => 0,", "Ok(Err(_deserialize_err)) => amount.0,"),
    ("S2_failed_call_refunded", "a failed ft_transfer_call is refunded in full", W,
     "Err(_) => amount.0,", "Err(_) => 0,"),
    ("S3_failed_transfer_kept", "a failed plain transfer is taken as delivered", W,
     "amount.0" + NL + "            } else {" + NL + "                0", "amount.0" + NL + "            } else {" + NL + "                amount.0"),
    ("S4_refund_whole_amount", "the withdrawal callback always credits back the whole amount", W,
     "let refund = amount.0.saturating_sub(used);", "let refund = amount.0;"),
    ("S5_deposit_one_more", "a deposit credits one unit more than it is told", D,
     "self.deposit(receiver_id, [(token_id, amount.0)], Some(\"deposit\"))", "self.deposit(receiver_id, [(token_id, amount.0 + 1)], Some(\"deposit\"))"),
    # three changes that a run of random traces cannot see; an independent reviewer of this kit proposed them
    ("S6_new_entry_point", "a new public method credits the ledger with no token arriving", D,
     "    #[private]" + NL + "    #[allow(clippy::needless_pass_by_value)]" + NL + "    pub fn ft_resolve_deposit(",
     "    pub fn extra_credit(&mut self, account_id: AccountId, token: AccountId, amount: U128) {" + NL
     + "        self.deposit(account_id, [(TokenId::Nep141(Nep141TokenId::new(token)), amount.0)], Some(\"deposit\"))" + NL
     + "            .unwrap_or_else(|err| err.panic());" + NL + "    }" + NL + NL
     + "    #[private]" + NL + "    #[allow(clippy::needless_pass_by_value)]" + NL + "    pub fn ft_resolve_deposit("),
    # mt_force_transfer delegates to mt_force_batch_transfer, which carries the attribute too: removing it from
    # the first method alone changes no behaviour (run of 2026-11-13: 200 traces, 29 calls of mt_force_transfer by
    # accounts without the role, all rejected). The check is gone only when both attributes are.
    ("S7_role_check_removed", "the role check of the forced internal transfer is gone (both methods)", F,
     [("    #[access_control_any(roles(Role::DAO, Role::UnrestrictedWithdrawer))]" + NL + "    #[payable]" + NL + "    fn mt_force_transfer(",
       "    #[payable]" + NL + "    fn mt_force_transfer("),
      ("    #[access_control_any(roles(Role::DAO, Role::UnrestrictedWithdrawer))]" + NL + "    #[payable]" + NL + "    fn mt_force_batch_transfer(",
       "    #[payable]" + NL + "    fn mt_force_batch_transfer(")], None),
    ("S8_one_amount_doubled", "a deposit of one particular amount is credited twice over", D,
     "self.deposit(receiver_id, [(token_id, amount.0)], Some(\"deposit\"))",
     "self.deposit(receiver_id, [(token_id, if amount.0 == 1_234_567_891_234 { amount.0 * 2 } else { amount.0 })], Some(\"deposit\"))"),
]
os.makedirs(WORK, exist_ok=True)
res = []
for mid, what, path, old, new in MUTANTS:
    d = os.path.join(WORK, "src")
    shutil.rmtree(d, ignore_errors=True)
    subprocess.run(["git", "clone", "-q", "--shared", SRC, d], check=True)
    subprocess.run(["git", "checkout", "-q", "-f", COMMIT], cwd=d, check=True)
    rec = {"id": mid, "change": what, "file": path}
    if path:
        p = os.path.join(d, path); s = open(p).read()
        pairs = old if isinstance(old, list) else [(old, new)]
        if any(s.count(o) != 1 for o, _ in pairs):
            rec["result"] = f"NOT APPLIED ({[s.count(o) for o, _ in pairs]} matches)"; res.append(rec); print(rec, flush=True); continue
        for o, n in pairs:
            s = s.replace(o, n)
        open(p, "w").write(s)
    b = subprocess.run(["docker", "run", "--rm", "-u", f"{os.getuid()}:{os.getgid()}", "-e", "HOME=/tmp/home",
                        "-v", f"{d}:/home/near/code", "-w", "/home/near/code/contracts/defuse", IMG,
                        "cargo", "near", "build", "non-reproducible-wasm", "--locked", "--features=contract",
                        "--abi-features=abi,contract"], capture_output=True, text=True)
    wasm = os.path.join(d, "target/near/defuse/defuse.wasm")
    if b.returncode != 0 or not os.path.exists(wasm):
        rec["result"] = "BUILD FAILED"; rec["detail"] = (b.stdout + b.stderr)[-300:]; res.append(rec); print(rec, flush=True); continue
    g = subprocess.run([os.path.join(ROOT, "scripts/verify_upgrade.sh"), "--tree", d, N], capture_output=True, text=True)
    try:
        v = json.loads(g.stdout[g.stdout.index("{"):])
        st = v.get("static") or {}
        rec.update(code_hash=v["code_hash"], verdict=v["verdict"], monitors_fired=v["monitors_fired"],
                   replay_disagree=v["replay"]["disagree"], replay_steps=v["replay"]["contract_steps"],
                   world_disagree=(v["replay"].get("world") or {}).get("disagree", 0),
                   world_receipts=(v["replay"].get("world") or {}).get("token_receipts", 0)
                   + (v["replay"].get("world") or {}).get("contract_receipts", 0),
                   static={k: (len(x) if isinstance(x, list) else x) for k, x in st.items()})
        seen = bool(rec["monitors_fired"] or rec["replay_disagree"] or rec["world_disagree"])
        rec["seen_by_run"] = seen
        rec["rejected_by"] = ("the run" if seen else "the static part only" if v["verdict"] == "NEEDS REVIEW" else "nothing")
        if path is None:
            rec["result"] = "PASS" if v["verdict"] == "CARRIES OVER" else "FAIL"
        else:
            rec["result"] = "REJECTED" if v["verdict"] in ("DIVERGES", "NEEDS REVIEW") else "NOT NOTICED"
    except Exception:
        rec["result"] = "GATE FAILED"; rec["detail"] = (g.stdout + g.stderr)[-300:]
    res.append(rec); print(rec, flush=True)
shutil.rmtree(os.path.join(WORK, "src"), ignore_errors=True)
json.dump(res, open(OUT, "w"), indent=1)
rej = sum(1 for r in res if r.get("result") == "REJECTED")
by_run = sum(1 for r in res[1:] if r.get("rejected_by") == "the run")
by_static = sum(1 for r in res[1:] if r.get("rejected_by") == "the static part only")
print(f"source mutants rejected by the gate: {rej} of {len(MUTANTS) - 1} ({by_run} by the run, {by_static} by the static part only); "
      f"control: {res[0].get('result')}")
