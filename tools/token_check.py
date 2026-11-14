"""Token check: does a NEAR fungible token behave as the proved NEP-141 standard? (read-only)

usage: token_check.py <token account> [--json] [--network testnet] [--certificate certificate.json [--accept-certificate]]

A contract that accepts a token (an exchange, a bridge, NEAR Intents) trusts the numbers the token reports. The
proof of the Intents ledger in intents-proof/ holds only for tokens that behave as the standard. This tool answers,
for one token:
  * the verdict for its code hash from the token census (evidence/token-census.json): the deployed code was run on
    the nearcore runtime on 1000 random traces with monitors of the proved properties P1-P4;
  * what is switched on right now, read from the token's own views (a transfer tax or fee);
  * the methods it has beyond the standard;
  * whether its code can change (the exit stage of tools/exitproof.py): a standard token today is a different
    contract after an upgrade.
A code hash that is not in the census gets NOT CHECKED, never a pass — unless there is a certificate for it.

Certificates. A token team can run its own wasm through token-monitors/certify.sh (the same model-free monitors,
any library version, any initialiser) and gets a certificate file. A certificate is a record of a run, not a
proof, and a file proves nothing about who wrote it. So:
  * the certificates kept in evidence/token-certificates/ are runs made for this repository and count, by code hash;
  * a certificate passed with --certificate is checked for consistency (its code hash is the hash of the wasm it
    names and of the code the account runs now, its digest and totals match its contents) and then SHOWN AS A CLAIM:
    it changes no verdict. Re-run it yourself with token-monitors/verify-certificate.sh <certificate> <wasm> --rerun;
    after that, --accept-certificate makes this tool count it.

The field `behaves_as_standard_now` has three values. true: the runs of this code are standard and it has no
extension that changes transfers, or every fee or tax view it has was read, holds a field recognised as the fee, and
is off. It is about the code that runs now: whether that code can change is the exit stage beside it
(`code_can_change`), as for any contract. A token whose code follows another account is null instead, because that
account can change the token's code with no transaction to the token's account, which a watch of the token
cannot see. false: the runs deviate, or a
fee or tax reads on. null (unknown): everything else — the code has methods with which a privileged party freezes or
lowers a holder's balance (pause, blacklist, destroy, burn_from…, listed in `holder_balance_powers`), the code has an
extension that changes transfers and this tool cannot read its state, a view did not answer, the code was not run,
or the token's code is a global contract that another account can replace. `core_standard_on_runs` says separately what the runs of the code showed.
"""
import glob
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402
from exitproof import RpcUnavailable  # noqa: E402

CENSUS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "evidence", "token-census.json")
STANDARD_METHODS = {
    "ft_transfer", "ft_transfer_call", "ft_total_supply", "ft_balance_of", "ft_resolve_transfer", "ft_metadata",
    "storage_deposit", "storage_withdraw", "storage_unregister", "storage_balance_bounds", "storage_balance_of",
    "new", "new_default_meta", "contract_source_metadata", "__contract_abi",
}
CORE = ["ft_transfer", "ft_transfer_call", "ft_total_supply", "ft_balance_of", "ft_resolve_transfer"]


CERT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "evidence", "token-certificates")
CERT_FORMAT = "nep141-monitors-certificate/1"
KIT_SCRIPTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "token-monitors", "scripts")


def certificate_faults(c):
    """Why a certificate cannot be what it says, from its own contents: [] when nothing is wrong.

    Consistency, not authenticity: whoever writes the file can make it consistent. What this catches is a file
    edited by hand — a code hash that is not the hash of the wasm it names, a digest, a config hash or totals
    that do not match the rest."""
    sys.path.insert(0, KIT_SCRIPTS)
    try:
        import kitlib
    except Exception as e:
        return [f"the kit in token-monitors/ could not be loaded ({type(e).__name__})"]
    finally:
        sys.path.remove(KIT_SCRIPTS)
    faults = []
    try:
        if c["wasm"]["near_code_hash"] != kitlib.b58encode(bytes.fromhex(c["wasm"]["sha256"])):
            faults.append("its NEAR code hash is not the hash of the wasm it names")
        if c["config_sha256"] != kitlib.config_sha256(c["config"]):
            faults.append("its config hash does not match its config")
        core = {"wasm_sha256": c["wasm"]["sha256"], "config_sha256": c["config_sha256"],
                "kit_bundle_sha256": c["kit"]["bundle_sha256"], "traces": c["run"]["traces_requested"],
                "seed": c["run"]["seed"], "trace_digest": c["run"].get("trace_digest"),
                "monitors": {n: [m["checks"], m["violations"]] for n, m in c["monitors"].items()},
                "verdict": c["verdict"]}   # the same fields as token-monitors/scripts/certificate.py result_digest
        if c["result_digest"] != kitlib.sha256_bytes(kitlib.canonical_json(core)):
            faults.append("its result digest does not match its contents")
        viol = sum(m["violations"] for m in c["monitors"].values())
        idle = [n for n, m in c["monitors"].items() if m["checks"] == 0]
        if (c["verdict"] == "FAIL") != (viol > 0) or (c["verdict"] == "PASS" and idle) or c.get("violations_total") != viol:
            faults.append("its verdict or totals disagree with the counts of its monitors")
    except Exception as e:
        faults.append(f"a field is missing or malformed ({type(e).__name__})")
    return faults


def read_certificate(path):
    """A certificate file as a short record, or None if it is not a certificate of the known format."""
    try:
        c = json.load(open(path))
    except Exception:
        return None
    if not isinstance(c, dict) or c.get("format") != CERT_FORMAT or not isinstance(c.get("wasm"), dict):
        return None
    run, kit = c.get("run") or {}, c.get("kit") or {}
    return {"code_hash": c["wasm"].get("near_code_hash"), "wasm_sha256": c["wasm"].get("sha256"),
            "verdict": c.get("verdict"), "reasons": c.get("reasons") or [],
            "traces": run.get("traces"), "token_receipts": run.get("token_receipts"),
            "checks": c.get("checks_total"), "violations": c.get("violations_total"),
            "monitors": len(c.get("monitors") or {}), "kit": f"{kit.get('name')} {kit.get('version')}",
            "kit_bundle_sha256": kit.get("bundle_sha256"), "created_utc": c.get("created_utc"),
            "result_digest": c.get("result_digest"), "file": os.path.basename(path),
            "faults": certificate_faults(c),
            # a run made for this repository, as opposed to a file the caller brought
            "own": os.path.realpath(os.path.dirname(os.path.abspath(path))) == os.path.realpath(CERT_DIR)}


def load_certificates():
    """The certificates of evidence/token-certificates/ by NEAR code hash; a file with a fault is left out."""
    out = {}
    for path in sorted(glob.glob(os.path.join(CERT_DIR, "*.json"))):
        c = read_certificate(path)
        if c and c["code_hash"] and not c["faults"]:
            out[c["code_hash"]] = c
    return out


def load_census():
    try:
        with open(CENSUS) as f:
            return json.load(f)
    except Exception:
        return {"families": {}}


def tax_now(acc, exports):
    """The token's own answer about its transfer tax: None when it has no such method, else a dict."""
    if "get_tax" not in exports:
        return None
    ok, v = exitproof.view(acc, "get_tax")
    if not ok:
        return {"readable": False}
    t = (v or {}).get("tax") if isinstance(v, dict) else None
    if isinstance(v, dict) and not isinstance(t, dict) and ("buy_bps" in v or "sell_bps" in v):
        t = v                                   # the same fields at the top level
    if isinstance(v, dict) and set(v) <= {"tax"} and t is None:
        return {"readable": True, "on": False}  # {"tax": null}: no tax set
    if not isinstance(t, dict):
        return {"readable": False}              # an answer of a shape this tool does not know is no answer
    try:
        buy, sell = int(t.get("buy_bps") or 0), int(t.get("sell_bps") or 0)
    except (TypeError, ValueError):
        return {"readable": False}
    return {"readable": True, "on": buy > 0 or sell > 0, "buy_bps": buy, "sell_bps": sell,
            "taxed_counterparties": len(t.get("pairs") or [])}


SWITCH_VIEWS = ("get_tax", "get_config", "tax_state", "get_fee_state", "get_accumulated_info")
FEE_NAME = re.compile(r"fee|tax|deflat|burn_strategy", re.I)
# Methods with which a privileged party lowers or freezes a holder's balance: the proved property "only the holder
# lowers its balance" (P4) does not hold for a code that has one, whatever its runs showed. Read from names.
POWER_RE = re.compile(r"(^|_)(pause|freeze|lock_account)|black_?list|deny_?list|block_?list|destroy|burn_from|seize|"
                      r"confiscate|clawback|force_?(transfer|burn|withdraw)|admin_(transfer|burn|withdraw)|wipe", re.I)
POWER_EXEMPT = re.compile(r"^(get|is|has|view)_|^un(pause|freeze|lock|black)|^remove_from_|_status$", re.I)
FEE_KEY = re.compile(r"fee|tax|bps|pips|burn", re.I)
OFF_WORDS = {"", "none", "off", "disabled", "notax", "no_tax"}


LEAVES_MAX = 2000


def _leaves(x, path=""):
    if isinstance(x, dict):
        for k, v in x.items():
            yield from _leaves(v, f"{path}.{k}" if path else str(k))
    elif isinstance(x, list):
        for i, v in enumerate(x):
            yield from _leaves(v, f"{path}[{i}]")
    else:
        yield path, x


def switches_now(acc, exports):
    """What the token's own views say about a fee or a tax on transfers: one record per view it has.
    A view counts as ON when a field named like a fee or a tax holds a positive number (an integer, a decimal, a
    string of either, a percentage) or true, or a mode field holds anything but "off". Fail-closed reading: a cap,
    a past total or an exemption flag that is positive or true also reads as ON."""
    out = []
    for m in SWITCH_VIEWS:
        if m not in exports:
            continue
        ok, v = exitproof.view(acc, m)
        if not ok:
            out.append({"view": m, "readable": False})
            continue
        hot, seen = {}, 0
        leaves = list(_leaves(v))
        if len(leaves) > LEAVES_MAX:
            out.append({"view": m, "readable": False, "why": f"more than {LEAVES_MAX} fields"})
            continue
        for path, val in leaves:
            leaf = path.split(".")[-1]
            # a fee may sit under a field named like a fee: {"transfer_fee": {"numerator": 300, ...}}
            feeish = FEE_KEY.search(path)
            seen += bool(feeish) or leaf.lower() == "mode"
            if leaf.lower() == "mode" and isinstance(val, str) and val.lower() not in OFF_WORDS:
                hot[path] = val
            elif feeish and isinstance(val, bool):
                if val:   # fee_enabled: true, tax_on: true
                    hot[path] = "true"
            elif feeish:
                # a positive amount in any notation reads ON: 150, "150", 0.5, "1.5", "2%"
                try:
                    if float(str(val).strip().rstrip("%")) > 0:
                        hot[path] = str(val)
                except (TypeError, ValueError):
                    pass
        out.append({"view": m, "readable": True, "on": bool(hot), "recognised": seen > 0, "fields": dict(list(hot.items())[:4])})
    return out


LIVE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "evidence", "intents-live-backing.json")


def intents_ledger_row(acc):
    """The saved reading of the NEAR Intents ledger for this token, if it is there (tools/intents_backing.py)."""
    try:
        d = json.load(open(LIVE))
    except Exception:
        return None
    for r in d.get("tokens", []):
        if r.get("token") == acc:
            return {"block": d["summary"]["block"], "ledger": r.get("owed"), "held_by_intents": r.get("held"),
                    "relation": {"equal": "ledger = held", "surplus": "held > ledger", "DEFICIT": "LEDGER > HELD",
                                 "unread": "not readable"}.get(r.get("relation"), r.get("relation"))}
    return None


def check(acc, certificate=None, accept=False):
    """certificate: path of a certificate file brought by the caller. It is shown as a claim; it counts only with
    accept=True, which is the caller saying "I have re-run it"."""
    if certificate and read_certificate(certificate) is None:
        return {"account": acc, "error": f"{certificate} is not a certificate of the format {CERT_FORMAT}"}
    rep = exitproof.scan(acc, history=False, controllers=False)
    if "error" in rep:
        return {"account": acc, "error": rep["error"]}
    exports = rep.get("exports") or []
    code_hash = rep.get("effective_code_hash") or rep.get("code_hash")
    out = {"account": acc, "code_hash": code_hash, "is_token": all(m in exports for m in CORE[:4])}
    if not out["is_token"]:
        out["verdict"] = "NOT A TOKEN"
        out["why"] = "the code does not export " + ", ".join(m for m in CORE[:4] if m not in exports)
        return out
    ok, meta = exitproof.view(acc, "ft_metadata") if "ft_metadata" in exports else (False, None)
    out["symbol"] = meta.get("symbol") if ok and isinstance(meta, dict) else None
    fam = load_census()["families"].get(code_hash)
    out["extensions"] = sorted(m for m in exports if m not in STANDARD_METHODS and not m.startswith("ft_metadata"))[:40]
    out["tax_now"] = tax_now(acc, exports)
    out["switches"] = switches_now(acc, exports)
    out["code_follows_another_account"] = rep.get("code_source") == "global_by_account"
    row = intents_ledger_row(acc)
    if row:
        out["intents_ledger"] = row
    st = rep.get("stage") or {}
    out["code_can_change"] = {"exit_stage": st.get("level"), "label": st.get("label"), "why": (st.get("why") or [])[:2]}
    cert = load_certificates().get(code_hash)
    claim = None
    if certificate:
        given = read_certificate(certificate)
        name = os.path.basename(certificate)
        if given["faults"]:
            out["certificate_refused"] = f"the certificate {name} is not consistent: " + "; ".join(given["faults"])
        elif given["code_hash"] != code_hash:
            out["certificate_refused"] = f"the certificate {name} is for code {given['code_hash']}, and the account runs {code_hash}"
        elif given["own"] or accept:
            cert = given
        else:
            claim = given
            out["certificate_claim"] = dict(given, note=(
                "a claim of whoever wrote the file: consistent with the code this account runs, not re-run here, and "
                "it changes no verdict. Re-run: token-monitors/verify-certificate.sh <certificate> <wasm> --rerun; "
                "then --accept-certificate"))
    if cert:
        out["certificate"] = cert
    certified = bool(cert and cert["verdict"] == "PASS" and cert["violations"] == 0)
    if fam is None and certified:
        # no census run of this code, but a certificate of a run with the same monitors
        out["verdict"] = "STANDARD"
        out["verdict_source"] = ("certificate" if cert["own"] else
                                 "certificate brought by the caller and accepted with --accept-certificate")
    elif fam is None:
        out["verdict"] = "NOT CHECKED"
        out["why"] = "this code hash is not in the token census; nothing is known about how it behaves"
        if cert:
            out["why"] += f"; its certificate says {cert['verdict']}"
        if claim:
            out["why"] += f"; a certificate brought by the caller claims {claim['verdict']} and is not counted"
        if "ft_resolve_transfer" not in exports:
            out["why"] += "; it does not export ft_resolve_transfer"
    else:
        out["verdict"] = fam["verdict"]
        out["census"] = {k: fam.get(k) for k in ("family", "held_by_intents", "listed_on_exchange", "traces", "token_receipts", "monitors_fired",
                                                 "reason", "extension_effect", "exact_model_5_29_0", "library")}
    sw = out["switches"]
    on = [x for x in sw if x.get("on")] or ([{"view": "get_tax"}] if (out["tax_now"] or {}).get("on") else [])
    unread = [x["view"] for x in sw if not x.get("readable")]
    effect = bool(fam and fam.get("extension_effect"))
    feeish = [m for m in exports if m not in STANDARD_METHODS and FEE_NAME.search(m)]
    out["core_standard_on_runs"] = {"STANDARD": True, "STANDARD + EXTENSIONS": True, "DEVIATES": False}.get(out["verdict"])
    powers = sorted(m for m in exports if POWER_RE.search(m) and not POWER_EXEMPT.search(m))
    out["holder_balance_powers"] = powers
    unknown = None
    if out["verdict"] == "DEVIATES" or on:
        now = False
    elif out["verdict"] not in ("STANDARD", "STANDARD + EXTENSIONS"):
        now, unknown = None, "the code of this token has no verdict from a run"
    elif out["code_follows_another_account"]:
        now, unknown = None, "the token's code is a global contract referenced by account id: that account can replace it at any time"
    elif powers:
        now, unknown = None, ("a privileged party can freeze or lower a holder's balance through "
                              + ", ".join(powers[:5]) + (" …" if len(powers) > 5 else "")
                              + ": the runs show the standard core, but not that these are never called")
    elif unread:
        now, unknown = None, "a fee or tax view of the token did not answer: " + ", ".join(unread)
    elif effect or feeish:
        # the code can change transfers: "off" needs a view that holds a field this tool recognises as the fee,
        # and every such view read off; a view with no fee field says nothing about the fee
        known = [x for x in sw if x.get("recognised") or x["view"] == "get_tax"]
        if known and len(known) == len(sw):
            now = True
        else:
            now, unknown = None, ("the code has an extension that changes transfers when it applies"
                                  + (" (" + ", ".join(feeish[:4]) + ")" if feeish else "")
                                  + (", and no view of the token holds a field this tool recognises as its fee"
                                     if sw else ", and this tool has no view to read its state from"))
    else:
        now = True
    out["behaves_as_standard_now"] = now
    if unknown:
        out["unknown_because"] = unknown
    return out


def render(r):
    if "error" in r:
        return f"{r['account']}: {r['error']}"
    L = [f"# {r['account']}  ({r.get('symbol') or 'no symbol'}; code {str(r['code_hash'])[:12]}…)"]
    if r["verdict"] == "NOT A TOKEN":
        return "\n".join(L + [f"TOKEN CHECK: NOT A TOKEN — {r['why']}"])
    c = r.get("census") or {}
    tax = r.get("tax_now") or {}
    head = {"STANDARD": "BEHAVES AS NEP-141", "STANDARD + EXTENSIONS": "CORE BEHAVES AS NEP-141, HAS EXTENSIONS",
            "DEVIATES": "DEVIATES FROM NEP-141", "NOT RUN": "NOT CHECKED", "NOT CHECKED": "NOT CHECKED",
            "UNDER REVIEW": "NOT CHECKED (the run of this code is under review)"}[r["verdict"]]
    hot = [x for x in (r.get("switches") or []) if x.get("on")]
    if (tax.get("on") or hot) and r["verdict"] != "DEVIATES":
        head = "DOES NOT BEHAVE AS NEP-141 NOW (a transfer tax or fee is on)"
    elif r.get("code_follows_another_account"):
        head = "NO VERDICT — the token's code follows another account (" + head + " for the code published now)"
    why = c.get("reason") or r.get("why") or ""
    L.append(f"TOKEN CHECK: {head}" + (f" — {why}" if why else ""))
    ct = r.get("certificate")
    if ct:
        L.append(f"Certificate [run]: {ct['kit']}, {ct['verdict']} — {ct['traces']} traces, {ct['token_receipts']} token receipts, "
                 f"{ct['checks']} checks of {ct['monitors']} monitors, {ct['violations']} violations ({ct['created_utc']}); "
                 f"re-check: token-monitors/verify-certificate.sh evidence/token-certificates/{ct['file']} <wasm> --rerun")
    if r.get("certificate_refused"):
        L.append("Certificate refused: " + r["certificate_refused"])
    cl = r.get("certificate_claim")
    if cl:
        L.append(f"Certificate claim [not re-run, not counted]: {cl['file']} says {cl['verdict']} — {cl['traces']} traces, "
                 f"{cl['violations']} violations ({cl['created_utc']}); {cl['note']}")
    if c:
        fired = c.get("monitors_fired") or []
        if r["verdict"] in ("STANDARD", "STANDARD + EXTENSIONS"):
            tail = "; monitors fired: none"
        elif fired:
            tail = "; monitors fired: " + ", ".join(fired)
        else:
            tail = ""
        L.append(f"Checked [run]: this code hash, {c.get('traces')} random traces of the deployed code on the nearcore runtime "
                 f"({c.get('token_receipts')} token receipts){tail}"
                 + ("; exact agreement with the proved 5.29.0 model" if c.get("exact_model_5_29_0") == "PASS" else ""))
        L.append(f"Same code: {c.get('held_by_intents')} token(s) held by NEAR Intents, {c.get('listed_on_exchange')} listed on the "
                 f"largest exchange ({c.get('family')})")
        if c.get("extension_effect"):
            L.append(f"Extension [run]: {c['extension_effect']}")
    if tax:
        if not tax.get("readable"):
            L.append("Now [view]: the token has a transfer-tax method but did not answer")
        elif tax.get("on"):
            L.append(f"Now [view]: transfer tax ON — {tax['buy_bps'] / 100:.2f}% buy, {tax['sell_bps'] / 100:.2f}% sell, "
                     f"with {tax['taxed_counterparties']} counterparty account(s)")
        else:
            L.append("Now [view]: transfer tax off")
    for x in r.get("switches") or []:
        if x["view"] == "get_tax":
            continue
        if not x.get("readable"):
            L.append(f"Now [view]: {x['view']} did not answer")
        elif x.get("on"):
            L.append(f"Now [view]: {x['view']} reads ON — " + ", ".join(f"{k} = {v}" for k, v in x["fields"].items()))
        else:
            L.append(f"Now [view]: {x['view']} shows no fee or tax")
    il = r.get("intents_ledger")
    if il:
        L.append(f"NEAR Intents [view, block {il['block']}]: {il['relation']} — ledger {il['ledger']}, held {il['held_by_intents']}")
    if r.get("holder_balance_powers"):
        L.append("A privileged party can freeze or lower a holder's balance [name]: " + ", ".join(r["holder_balance_powers"][:8])
                 + (" …" if len(r["holder_balance_powers"]) > 8 else ""))
    if r.get("extensions"):
        L.append("Methods beyond the standard [code]: " + ", ".join(r["extensions"][:16]) + (" …" if len(r["extensions"]) > 16 else ""))
    cc = r.get("code_can_change") or {}
    L.append(f"Code can change [chain]: exit stage {cc.get('exit_stage')} — {cc.get('label')}"
             + (f" ({'; '.join(cc.get('why') or [])})" if cc.get("why") else ""))
    ext_note = (" The extensions listed above were not exercised." if r["verdict"] == "STANDARD + EXTENSIONS" else "")
    L.append({True: "For a contract that accepts it: behaves as the standard on these runs; this holds for this code hash only."
                    + ext_note,
              False: "For a contract that accepts it: do not credit what it reports; measure what arrives.",
              None: "For a contract that accepts it: unknown (" + (r.get("unknown_because") or "not checked")
                    + "); measure what arrives instead of crediting what it reports."}[r["behaves_as_standard_now"]])
    return "\n".join(L)


if __name__ == "__main__":
    argv = sys.argv[1:]
    certificate = None
    if "--certificate" in argv:
        i = argv.index("--certificate")
        if i + 1 >= len(argv) or not os.path.isfile(argv[i + 1]):
            sys.exit("--certificate takes the path of a certificate file")
        certificate = argv[i + 1]
        del argv[i:i + 2]
    if "--network" in argv:
        i = argv.index("--network")
        if i + 1 >= len(argv) or argv[i + 1] not in ("mainnet", "testnet"):
            sys.exit("--network takes mainnet or testnet")
        exitproof.rpc.use_network(argv[i + 1])
        del argv[i:i + 2]
    args = [a for a in argv if not a.startswith("--")]
    if len(args) != 1:
        sys.exit(__doc__)
    try:
        r = check(args[0], certificate, accept="--accept-certificate" in sys.argv)
    except RpcUnavailable as e:
        print(f"{args[0]}: the public RPC did not answer ({e}); no verdict — retry in a minute", file=sys.stderr)
        sys.exit(2)
    print(json.dumps(r, indent=1) if "--json" in sys.argv else render(r))
    sys.exit(1 if "error" in r else 0)   # 1: not an account, not found, not a certificate; 2 (above): the chain was not read
