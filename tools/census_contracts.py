"""Run the Exit Proof scanner over a list of value-holding contracts; keep only the aggregated public view."""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exitproof  # noqa: E402

accs = [a.strip() for a in open(sys.argv[1]) if a.strip() and not a.startswith("#")]
out = sys.argv[2]
done = {}
if os.path.exists(out):
    done = {r["account"]: r for r in json.load(open(out))}
for acc in accs:
    if acc in done and "error" not in done[acc]:
        continue
    try:
        rep = exitproof.scan(acc)
        done[acc] = exitproof.public_view(rep) if "error" not in rep else rep
    except exitproof.RpcUnavailable as e:
        done[acc] = {"account": acc, "error": "rpc unavailable (retry later): " + str(e)[:150]}
    except Exception as e:
        done[acc] = {"account": acc, "error": "scanner error: " + str(e)[:200]}
    json.dump(list(done.values()), open(out, "w"), indent=1)
    print(acc, "no-path" if (done[acc].get("no_code_change_path_found") or done[acc].get("immutable_code")) else "code-change-path/err", flush=True)
    time.sleep(2)
