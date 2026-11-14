"""Regression check of the repository after a change. Run it before every commit.

usage: selftest.py [--offline]

Offline part (no network):
  * the attested proof directories still hash to the values stored on chain (an edit there needs a new attestation);
  * method names are classified as expected (code change / migration entry point / neither);
  * the MCP server answers `initialize` and lists its tools.
Online part (read-only public RPC; one to three minutes, depending on how the public endpoints rate-limit):
  * known accounts get the expected exit stage, on mainnet and on testnet;
  * the registry returns, for each attested code hash, the bundle hash computed from this checkout.
Exit status 0 iff every check passes.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import bundle_hash  # noqa: E402
import exitproof  # noqa: E402
import rpc  # noqa: E402

# directory -> (code hash the certificate is keyed by, bundle hash stored in registry.exitproof.near)
ATTESTED = {
    "pool-proof": ("J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY",
                   "2d4d8251bb777f346a4ee5b2367dc4a71d37e5643e7da925027e0ba63ee5b618"),
    "wnear-proof": ("DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1",
                    "6c29def20cc0b1a9499559383bddfe729ff909b88ccbb81889acc46c40c875ee"),
    "token-standard": ("3Ty4ENxJ4EicohgXi9E2txgbqMh3DWSshPrtXxY8pksm",
                       "d298726f145773c834ba9ccc2a847f0de75636a760c04880d47ce051ab3f1794"),
    "upgrade-window": ("7m2GRykdzJxaH4r8fmjZg5BJnVvvkKFqDm55GcLLfdPv",
                       "2c6d223219be21901e6fe3231e5b3fb780e71b8e204c56c20669b2c5a7d67439"),
}
# method name -> "code" (a way to change the contract's own code), "migration" or None
NAMES = {
    "upgrade": "code", "deploy_code": "code", "deploy_upgrade": "code", "upgrade_and_migrate": "code",
    "unrestricted_upgrade": "code", "update_contract": "code", "add_full_access_key": "code",
    "delete_account": "code", "up_stage_code": "code", "up_deploy_code": "code",
    "up_stage_update_staging_duration": "code", "migrate_code": "code",
    "migrate": "migration", "state_migrate": "migration", "migrate_ok": "migration",
    "up_staged_code": None, "up_staged_code_hash": None, "get_upgrade_delay_blocks": None,
    "deploy_erc20_token": None, "deploy_token_callback": None, "add_token_deployer": None,
    "migrate_deployed_token": None, "update_deployment_info": None, "update_contract_mode": None,
    "verify_migrate_deposit": None, "upgrade_name_symbol": None, "ft_transfer": None, "withdraw": None,
    # code changed by a vote or by attaching a key; an upgrade of another contract is not a path of this one
    "vote_contract_update": "code", "submit_contract_update": "code", "propose_update": "code",
    "attach_full_access_key": "code", "factory_update": "code",
    "contract_update_votes": None, "upgrade_bridge_token": None,
    # names are matched without regard to case: a contract written in another language exports UpgradeContract
    "Upgrade": "code", "UpgradeContract": "code",
    "update": "code", "update_self": "code", "set_wasm": "code", "store_code": "code", "code_update": "code",
    "apply_patch": "code", "update_config": None, "update_metadata": None,
}
# (network, account, expected stage). The staged testnet vault is left out: its stage changes on 2026-11-19.
STAGES = [
    ("mainnet", "astro-stakers.poolv1.near", "2"),
    ("mainnet", "wrap.near", "2"),
    ("mainnet", "token.sweat", "0"),
    ("mainnet", "liver.pool.near", "0"),
    ("mainnet", "v2.ref-finance.near", "0"),
    ("mainnet", "registry.exitproof.near", "U"),
    ("testnet", "quiet-vault.exitproof-demo.testnet", "1"),
    # gated vault with uncertified code staged and its delay passed: one attestation away from a deploy, no time bound
    ("testnet", "vault.gated-upgrade.testnet", "0"),
    # the same gated vault code with nothing staged and a delay of seven days
    ("testnet", "gated-quiet-vault.testnet", "1"),
    # code changed by a vote of the contract's participants, of a DAO, of a multisig: not "no path found"
    ("mainnet", "v1.signer", "0"),
    ("mainnet", "ref-finance.sputnik-dao.near", "0"),
    ("mainnet", "foundation.near", "0"),
]

# token account -> (census verdict, behaves as the standard now)
TOKENS = [
    ("4illia-222.meme-cooking.near", "STANDARD", True),
    # the core runs are standard, and its owner can pause, blacklist and destroy a holder's funds: unknown, not a pass
    ("usdt.tether-token.near", "STANDARD + EXTENSIONS", None),
    ("batman-4.nearlytrade.near", "DEVIATES", False),
    ("registry.exitproof.near", "NOT A TOKEN", None),
    # the core runs are standard, a transfer fee reads on now
    ("nearsight.v2-launchpad.justhoot.near", "STANDARD + EXTENSIONS", False),
    # an extension that changes transfers and no view to read its state from: unknown, not a pass
    ("eth.omft.near", "STANDARD + EXTENSIONS", None),
]
# token account whose deployed code hash has a certificate of the token-monitors kit in evidence/token-certificates/
CERTIFIED_TOKEN = "blackdragon.tkn.near"

results = []


def check(name, ok, detail=""):
    results.append(ok)
    print(("ok   " if ok else "FAIL ") + name + (f" — {detail}" if detail and not ok else ""))


def classify(name):
    if exitproof.MIGRATION_RE.search(name):
        return "migration"
    if exitproof.CODE_RE.search(name) and not exitproof.NOT_SELF_CODE_RE.search(name):
        return "code"
    return None


def offline():
    for d, (_, want) in ATTESTED.items():
        got, n = bundle_hash.bundle_hash(os.path.join(ROOT, d))
        check(f"bundle hash of {d}/ ({n} files) equals the attested one", got == want,
              f"got {got}: the directory changed since it was attested. If you only ran its check.sh, restore the "
              f"run logs (git checkout -- {d} && git clean -fdq {d}). If you edited it, revert the edit or attest "
              f"again (registry/attest.py) and update ATTESTED here and EVIDENCE.md")
    bad = {n: (classify(n), want) for n, want in NAMES.items() if classify(n) != want}
    check(f"method-name classes ({len(NAMES)} names)", not bad, f"(got, expected): {bad}")
    req = [{"jsonrpc": "2.0", "id": 1, "method": "initialize",
            "params": {"protocolVersion": "2025-06-18", "capabilities": {}, "clientInfo": {"name": "selftest", "version": "0"}}},
           {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
           {"jsonrpc": "2.0", "id": 3, "method": "ping"},
           {"jsonrpc": "2.0", "id": 4, "method": "tools/call",
            "params": {"name": "exit_check", "arguments": {"account_id": "Not An Account"}}}]
    p = subprocess.run([sys.executable, os.path.join(HERE, "mcp_server.py")], input="\n".join(map(json.dumps, req)) + "\n",
                       capture_output=True, text=True, timeout=60)
    names, pong, refused = [], False, False
    for line in p.stdout.splitlines():
        try:
            j = json.loads(line)
        except ValueError:
            continue
        names += [t["name"] for t in (j.get("result") or {}).get("tools", [])]
        pong = pong or (j.get("id") == 3 and j.get("result") == {})
        refused = refused or (j.get("id") == 4 and bool((j.get("result") or {}).get("isError")))
    check("MCP server lists exit_check, exit_plan and token_check",
          sorted(names) == ["exit_check", "exit_plan", "token_check"], f"got {names}")
    check("MCP server answers ping", pong)
    check("MCP server refuses an argument that is not an account id", refused)
    import token_check
    certs = token_check.load_certificates()
    named = all(os.path.exists(os.path.join(token_check.CERT_DIR, h + ".json")) for h in certs)
    good = all(c["verdict"] == "PASS" and c["violations"] == 0 and (c["checks"] or 0) > 0 for c in certs.values())
    check(f"token certificates in evidence/token-certificates/: {len(certs)}, each named by its code hash, PASS with "
          f"checks made and no violation", len(certs) >= 4 and named and good, f"got {[(h[:8], c['verdict']) for h, c in certs.items()]}")
    # a certificate edited by hand is refused: the three edits a forger would try first
    some = sorted(certs)[0]
    honest = json.load(open(os.path.join(token_check.CERT_DIR, some + ".json")))
    edits = []
    for change in (lambda c: c["wasm"].__setitem__("near_code_hash", "H2jJZoTmYjhwmEDAUiWruB3wcmwW1ctsE9H7cPrC36dK"),
                   lambda c: c["wasm"].__setitem__("sha256", "00" * 32),
                   lambda c: c["monitors"][sorted(c["monitors"])[0]].__setitem__("violations", 3),
                   lambda c: c["run"].__setitem__("traces_requested", 100000)):
        e = json.loads(json.dumps(honest))
        change(e)
        edits.append(bool(token_check.certificate_faults(e)))
    check("a token certificate edited by hand is found inconsistent (code hash, wasm hash, counts, number of traces); "
          "the unedited one is consistent", all(edits) and not token_check.certificate_faults(honest), f"got {edits}")
    # the page (web/) runs these tools in the browser: every file it copies must exist, and it must see the same
    # token certificates as the command line
    page = json.load(open(os.path.join(ROOT, "web", "files.json")))
    there = all(os.path.isfile(os.path.join(ROOT, f)) for f in page)
    need_files = {"tools/rpc.py", "tools/exitproof.py", "tools/token_check.py", "tools/proofs.json", "evidence/token-census.json"}
    need_files |= {f"evidence/token-certificates/{h}.json" for h in certs}
    check("the page's file list (web/files.json) names files that exist and covers the tools and every token certificate",
          there and need_files <= set(page), f"missing from the list: {sorted(need_files - set(page))}")
    import numbers_check
    facts = numbers_check.main()
    bad = [f"{what}: {detail}" for ok, what, detail in facts if not ok]
    check(f"the documents quote the numbers of the evidence files ({len(facts)} facts, tools/numbers_check.py)", not bad, "; ".join(bad))
    live = os.path.join(ROOT, "evidence", "intents-live-backing.json")
    if os.path.exists(live):
        import intents_backing
        d = json.load(open(live))
        again = intents_backing.summarize(d["tokens"], d["summary"]["block"], d["summary"]["ledger_token_ids"])
        std = again["standard_verdict"]
        check(f"saved reading of the Intents ledger: summary follows from its {len(d['tokens'])} rows, "
              f"no token with a standard verdict has the ledger above the holdings ({std['tokens']} tokens)",
              again == d["summary"] and std["deficits"] == 0 and std["tokens"] > 300, f"got {std}")


def synthetic(**over):
    """A report of a keyless contract with no upgrade method, to test the stage rules without the network."""
    rep = {"account": "x.near", "balance": "0", "locked": "0", "code_hash": "h", "effective_code_hash": "h", "has_code": True,
           "keys": [], "full_access_keys": [], "own_function_call_keys": [], "self_governed": None,
           "global_contract_account_id": None, "exports": ["deposit", "withdraw"], "roles": {}, "controllers": {},
           "method_classes": {"code": [], "migration": [], "funds": [], "freeze": [], "mint": [], "ownership": []},
           "proof": None, "onchain_certificates": [],
           "deployments": [{"tx": "t1", "ts": 1600000000, "by": "factory.near"}]}
    rep.update(over)
    rep["verdict"] = exitproof.verdict(rep)
    rep["stage"] = exitproof.stage(rep)
    return rep


def unread_code_refused():
    was = exitproof.wasm_path
    exitproof.wasm_path = lambda acc, a: (None, None)
    try:
        exitproof.scan("wrap.near", history=False, controllers=False)
        return False
    except exitproof.RpcUnavailable:
        return True
    finally:
        exitproof.wasm_path = was


def plugin_contract(code=(), unread=(), staged=None, staging_ts=None, gate=False, proof=None, certs=()):
    """A synthetic contract with the upgrade plugin and a staging delay of seven days."""
    roles = {"upgrade_delay_status": {"staging_duration": str(7 * 24 * 3600 * 10**9), "staging_timestamp": staging_ts,
                                      "new_staging_duration": None, "new_staging_duration_timestamp": None},
             "staged_code_hash": staged, "unread": list(unread)}
    if gate:
        roles["gate"] = {"registry": "r.near", "kind": "upgrade-window", "attestors": 1}
    exports = ["up_stage_code", "up_deploy_code", "up_get_delay_status", "up_staged_code_hash", "deposit_and_stake",
               "withdraw"] + list(code)
    return synthetic(exports=exports, roles=roles, proof=proof, onchain_certificates=list(certs),
                     method_classes={"code": ["up_stage_code", "up_deploy_code"] + list(code), "migration": [],
                                     "funds": [], "freeze": [], "mint": [], "ownership": []})


def plugin_rules():
    past = str(exitproof.time.time_ns() - 3600 * 10**9)
    gated = {"kind": "gated-upgrade", "statement": "s"}
    uw = [{"attestor": exitproof.ATTESTORS[0], "attested_at_ns": 0,
           "body": {"kind": "upgrade-window", "theorems": ["t"], "artifact_sha256": "00", "check_command": "c"}}]
    got = [plugin_contract(certs=uw)["stage"]["level"],                                 # a certified plugin and a delay: 1
           plugin_contract()["stage"]["level"],                                         # the plugin by names only: 0
           plugin_contract(certs=uw, unread=["up_staged_code_hash"])["stage"]["level"],  # the staged-code view failed
           plugin_contract(certs=uw, unread=["acl_role_variants"])["stage"]["level"],    # the role list failed
           plugin_contract(certs=uw, staging_ts=past)["stage"]["level"],                 # staged code past its delay, view null
           plugin_contract(certs=uw, code=["up_deploy_now"])["stage"]["level"],          # an up_-named method of its own
           plugin_contract(certs=uw, code=["deploy_certified"], gate=True)["stage"]["level"],  # a gate view on other code
           plugin_contract(code=["deploy_certified"], gate=True, proof=gated)["stage"]["level"]]  # the proved gated vault
    check("stage 1 needs the plugin established for this code (a certificate or a proof of this repository) and fails "
          "closed: names alone, a view the window depends on that does not answer, a staging timestamp in the past, a "
          "code method beyond the plugin's own, or a gate that is not the proved gated vault give stage 0",
          got == ["1", "0", "0", "0", "0", "0", "0", "1"], f"got {got}")
    import agent_demo
    was = exitproof.scan
    try:
        # a stage 1 from a proof of this repository, without a certificate on chain: the agent still wants the certificate
        exitproof.scan = lambda acc, history=True, controllers=True: plugin_contract(proof={"kind": "upgrade-window"})
        ok_uncert, reasons, _ = agent_demo.decide("x.near", "1", 1, min_window_h=1)
        exitproof.scan = lambda acc, history=True, controllers=True: plugin_contract(certs=uw)
        ok_cert, _, _ = agent_demo.decide("x.near", "1", 1, min_window_h=1)
    finally:
        exitproof.scan = was
    try:
        agent_demo.decide("x.near", "1", 0)
        zero_refused = False
    except ValueError:
        zero_refused = True
    check("the reference agent stakes at stage 1 only when the plugin of this code is certified, and accepts no "
          "policy below stage 1", (ok_uncert, ok_cert, zero_refused) == (False, True, True),
          f"got {(ok_uncert, ok_cert, zero_refused)}, {reasons}")


def tool_rules():
    import shutil
    import tempfile
    wasm = open(os.path.join(ROOT, "pool-proof", "wasm", "staking_pool.wasm"), "rb").read()
    same = exitproof.code_hash_of(wasm) == "J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY"
    # a digest that starts with a zero byte: its hash starts with "1", and it decodes back to the same 32 bytes
    import hashlib
    z = next(str(i).encode() for i in range(100000) if hashlib.sha256(str(i).encode()).digest()[0] == 0)
    zh = exitproof.code_hash_of(z)
    n = 0
    for ch in zh:
        n = n * 58 + exitproof.B58.index(ch)
    back = b"\0" * (len(zh) - len(zh.lstrip("1"))) + n.to_bytes((n.bit_length() + 7) // 8, "big")
    same = same and zh.startswith("1") and back == hashlib.sha256(z).digest()
    # bytes that are not the code the account names are neither used nor kept
    was_codes, was_q = exitproof.CODES, exitproof.q
    tmp = tempfile.mkdtemp()
    try:
        exitproof.CODES = tmp
        h = exitproof.code_hash_of(wasm)
        open(os.path.join(tmp, h + ".wasm"), "wb").write(b"\0asm\x01\0\0\0")          # a cached file of other bytes
        exitproof.q = lambda *a, **k: {"result": {"code_base64": __import__("base64").b64encode(b"\0asm\x01\0\0\0").decode()}}
        try:
            exitproof.wasm_path("x.near", {"code_hash": h})
            refused = False
        except exitproof.RpcUnavailable:
            refused = not os.path.exists(os.path.join(tmp, h + ".wasm"))
    finally:
        exitproof.CODES, exitproof.q = was_codes, was_q
        shutil.rmtree(tmp, ignore_errors=True)
    check("a wasm is taken only if its hash is the code hash the account names (computed as NEAR does: the pool "
          "wasm hashes to J1arLz48…); a cached file of other bytes is removed", same and refused, f"got {same}, {refused}")
    import token_check
    was_view = exitproof.view
    got = []
    try:
        for cfg in ({"fee_bps": 150}, {"fee_enabled": True}, {"transfer_fee": "1.5"}, {"fee": 0.5}, {"fee": "2%"},
                    {"fee": 0}, {"fee_enabled": False}, {"fee_receiver": "x.near"}):
            exitproof.view = lambda acc, m, args=None, eps=None, cfg=cfg: (True, cfg)
            got.append(token_check.switches_now("t.near", ["get_config"])[0]["on"])
    finally:
        exitproof.view = was_view
    check("a token's fee view reads ON for a positive amount in any notation or a true flag, OFF for zero, false "
          "or an account name", got == [True] * 5 + [False] * 3, f"got {got}")
    got = []
    try:
        for cfg in ({"transfer_fee": {"numerator": 300, "denominator": 10000}}, {"tiers": [{"bps": 0}] * 20 + [{"bps": 500}]},
                    {"buy_bps": 500, "sell_bps": 0}, {"owner": "o.near"}):
            exitproof.view = lambda acc, m, args=None, eps=None, cfg=cfg: (True, cfg)
            x = token_check.switches_now("t.near", ["get_config"])[0]
            got.append((x["on"], x.get("recognised")))
    finally:
        exitproof.view = was_view
    check("a fee held as a fraction, in the 21st of 21 tiers or as top-level fields reads ON; a view with no fee field "
          "is not taken as a reading of the fee", got == [(True, True)] * 3 + [(False, False)], f"got {got}")
    was_q = exitproof.q
    exitproof.q = lambda *a, **k: {"error": {"name": "HANDLER_ERROR", "cause": {"name": "UNKNOWN_ACCOUNT"}}}
    try:
        exitproof.keys("x.near")
        refused = False
    except exitproof.RpcUnavailable:
        refused = True
    finally:
        exitproof.q = was_q
    check("a key list read that says \"unknown account\" for an account just read is no answer, not an empty list",
          refused)


def rules():
    exit_cert = [{"attestor": exitproof.ATTESTORS[0], "body": {"kind": "exit"}}]
    local = {"kind": "exit", "statement": "s"}
    two = [{"tx": "t1", "ts": 1600000000, "by": "x.near"}, {"tx": "t2", "ts": 1700000000, "by": "x.near"}]
    full = {"deployments": ["t1", "t2"]}
    pinned = {"kind": "exit", "origin": {"x.near": {"deployments": ["t1", "t2"], "note": "n", "full_history": full}},
              "stage_condition": "c"}
    unread_full = {"kind": "exit", "origin": {"x.near": {"deployments": ["t1", "t2"], "note": "n"}}}
    between = {"kind": "exit", "origin": {"x.near": {"deployments": ["t1", "t2"], "note": "n",
                                                     "full_history": {"deployments": ["t1", "t3", "t2"]}}}}
    later = [two[0], {"tx": "t4", "ts": 1750000000, "by": "x.near"}]
    got = [synthetic(onchain_certificates=exit_cert)["stage"]["level"],                               # one deployment
           synthetic(onchain_certificates=exit_cert, deployments=two)["stage"]["level"],              # ran other code before
           synthetic(onchain_certificates=exit_cert, deployments=[])["stage"]["level"],               # unknown to the indexer
           synthetic(onchain_certificates=exit_cert, deployments={"error": "e"})["stage"]["level"],   # history not read
           synthetic(onchain_certificates=[{"attestor": "someone-else.near", "body": {"kind": "exit"}}])["stage"]["level"],
           synthetic(onchain_certificates=exit_cert, deployments=two, proof=pinned)["stage"]["level"],
           # the indexer's short list shows first and latest; a deployment in between is in the full list only
           synthetic(onchain_certificates=exit_cert, deployments=two, proof=between)["stage"]["level"],
           synthetic(onchain_certificates=exit_cert, deployments=two, proof=unread_full)["stage"]["level"],  # no full list
           synthetic(onchain_certificates=exit_cert, deployments=later, proof=pinned)["stage"]["level"],     # code changed since
           # the certified code runs as a global contract by hash: which code wrote the state is not in the history
           synthetic(onchain_certificates=exit_cert, code_source="global_by_hash")["stage"]["level"]]
    cond = synthetic(onchain_certificates=exit_cert, deployments=two, proof=pinned)["stage"].get("condition")
    check("stage 2 needs the origin of the account's state: one code deployment, or exactly the deployments the proof "
          "names, recorded from every deployment receipt, with none since; not for a global contract; a certificate of an attestor that is not "
          "accepted does not count",
          got == ["2", "U", "U", "U", "U", "2", "U", "U", "U", "U"] and cond == "c", f"got {got}, condition {cond}")
    fc = {"key": "ed25519:k", "full": False, "receiver": "app.near", "methods": [], "allowance": None}
    got = synthetic(onchain_certificates=exit_cert, keys=[fc])["stage"]["level"]
    check("stage 2 needs an account with no access key at all: a function-call key to another contract pays its gas "
          "from the account's balance", got == "U", f"got {got}")
    plugin_rules()
    tool_rules()
    got = [exitproof.scan(a)["error"][:22] for a in ("DROP TABLE", "", "Upper.near", "a")]
    check("a string that is not an account id is refused before the chain is asked",
          all(g.startswith("not a NEAR account id") for g in got), f"got {got}")
    got = [synthetic()["stage"]["level"],
           synthetic(onchain_certificates=exit_cert)["stage"]["level"],
           synthetic(proof=local)["stage"]["level"],                                    # local proof list only
           synthetic(onchain_certificates=exit_cert, own_function_call_keys=["ed25519:k"])["stage"]["level"],
           synthetic(onchain_certificates=exit_cert, self_governed={"account": "x.near", "kind": "multisig"})["stage"]["level"]]
    check("stage rules: 2 needs the certificate on chain; a key on the contract's own account or a self-governing "
          "contract is stage 0", got == ["U", "2", "U", "0", "0"], f"got {got}")
    got = [exitproof.own_key_is_power(m) for m in ([], ["execute_intents"], ["ft_resolve_transfer"], ["upgrade"], ["on_stake_action"])]
    check("a key on the contract's own account counts when it is unlimited or reaches a callback or a privileged "
          "method, not when it is limited to an ordinary method", got == [True, False, True, True, True], f"got {got}")
    pv = exitproof.public_view(synthetic(proof={"kind": "ledger-backing", "attested": False, "statement": "s"}))
    check("a proof that is not an exit proof is reported apart and never as exit_proof",
          pv["exit_proof"] is None and len(pv["other_proofs"]) == 1, f"got {pv['exit_proof']}, {pv['other_proofs']}")


def unread_registry_refused():
    was = exitproof.registry_lookup
    exitproof.registry_lookup = lambda code_hash: None
    try:
        exitproof.scan("registry.exitproof.near", history=False, controllers=False)
        return False
    except exitproof.RpcUnavailable:
        return True
    finally:
        exitproof.registry_lookup = was


def online():
    check("a contract whose code could not be read gets no verdict (the scan refuses instead of reporting stage U)",
          unread_code_refused())
    check("a contract with no code-change path gets no verdict when the certificate registry could not be read (no "
          "answer is not \"no theorem\")", unread_registry_refused())
    for net, acc, want in STAGES:
        rpc.use_network(net)
        try:
            got = exitproof.scan(acc, history=False)["stage"]["level"]
        except exitproof.RpcUnavailable as e:
            got = f"no answer from the RPC ({e})"
        check(f"{acc} is at stage {want}", got == want, f"got {got}")
    rpc.use_network("mainnet")
    import token_check
    for acc, want, now in TOKENS:
        try:
            r = token_check.check(acc)
            got = (r.get("verdict"), r.get("behaves_as_standard_now"))
        except exitproof.RpcUnavailable as e:
            got = f"no answer from the RPC ({e})"
        check(f"token check of {acc}: {want}", got == (want, now), f"got {got}")
    try:
        r = token_check.check(CERTIFIED_TOKEN)
        ct = r.get("certificate") or {}
        got = (ct.get("verdict"), ct.get("code_hash") == r.get("code_hash"))
        other = token_check.check("usdt.tether-token.near", os.path.join(token_check.CERT_DIR, ct.get("code_hash", "x") + ".json"))
        refused = bool(other.get("certificate_refused")) and "certificate" not in other
    except exitproof.RpcUnavailable as e:
        got, refused = f"no answer from the RPC ({e})", False
    check(f"token check of {CERTIFIED_TOKEN} shows the certificate of the code it runs; the same certificate is refused "
          f"for a token that runs other code", got == ("PASS", True) and refused, f"got {got}, refused {refused}")
    for d, (code_hash, want) in ATTESTED.items():
        certs = exitproof.registry_lookup(code_hash) or []
        got = sorted({(c.get("body") or c).get("artifact_sha256") for c in certs})
        check(f"registry certificate for {d}/ pins this checkout's bundle hash", want in got, f"registry has {got}")


if __name__ == "__main__":
    offline()
    rules()
    if "--offline" not in sys.argv:
        online()
    if "--offline" not in sys.argv:
        n = len(results) + 1
        quoted = open(os.path.join(ROOT, "docs", "ROADMAP.md")).read()
        check(f"docs/ROADMAP.md quotes the number of checks of this file ({n})", f"{n} checks" in quoted)
    print(f"{sum(results)}/{len(results)} checks passed")
    sys.exit(0 if all(results) else 1)
