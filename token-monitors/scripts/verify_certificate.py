#!/usr/bin/env python3
"""verify_certificate.py CERTIFICATE.json TOKEN.wasm [--rerun]  (see ../verify-certificate.sh)"""
import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kitlib  # noqa: E402
import certificate  # noqa: E402

cert = json.load(open(sys.argv[1]))
wasm = open(sys.argv[2], "rb").read()
rerun = "--rerun" in sys.argv[3:]
ok = True


def line(good, text):
    global ok
    ok &= bool(good)
    print(("ok    " if good else "WRONG ") + text)


line(cert.get("format") == certificate.FORMAT, f"format {cert.get('format')}")
line(cert["wasm"]["sha256"] == kitlib.sha256_bytes(wasm), f"wasm sha256 {cert['wasm']['sha256']}")
line(cert["wasm"]["near_code_hash"] == kitlib.near_code_hash(wasm), f"NEAR code hash {cert['wasm']['near_code_hash']}")
line(cert["config_sha256"] == kitlib.config_sha256(cert["config"]), f"config sha256 {cert['config_sha256']}")
line(not kitlib.validate_config(cert["config"]), "the embedded config is well-formed")
line(cert["kit"]["bundle_sha256"] == kitlib.bundle_sha256(),
     f"kit bundle {cert['kit']['bundle_sha256']} (this kit: {kitlib.bundle_sha256()})")
line(cert["result_digest"] == certificate.result_digest(cert), f"result digest {cert['result_digest']}")
viol = sum(m["violations"] for m in cert["monitors"].values())
zero = [n for n, m in cert["monitors"].items() if m["checks"] == 0]
consistent = (cert["verdict"] == "FAIL") == (viol > 0) and not (cert["verdict"] == "PASS" and zero)
line(consistent, f"verdict {cert['verdict']} agrees with the counts ({viol} violations, {len(zero)} monitors without checks)")
if rerun and ok:
    with tempfile.TemporaryDirectory() as d:
        cfg = os.path.join(d, "config.json")
        json.dump(cert["config"], open(cfg, "w"))
        out = os.path.join(d, "certificate.json")
        r = subprocess.run([os.path.join(kitlib.KIT_ROOT, "certify.sh"), sys.argv[2], cfg, "--traces",
                            str(cert["run"]["traces_requested"]), "--seed", str(cert["run"]["seed"]), "--out", out],
                           capture_output=True, text=True)
        if not os.path.exists(out):
            line(False, "the re-run wrote no certificate: " + (r.stderr.strip().splitlines() or ["?"])[-1])
        else:
            again = json.load(open(out))
            line(again["result_digest"] == cert["result_digest"],
                 f"re-run: verdict {again['verdict']}, result digest {again['result_digest']}")
print("VERIFIED" if ok else "NOT VERIFIED")
sys.exit(0 if ok else 1)
