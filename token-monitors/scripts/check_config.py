#!/usr/bin/env python3
"""check_config.py CONFIG.json: validates a config against the format of CONFIG.md.
Prints the problems and exits with 3 when there are any; prints the config's hash otherwise."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kitlib  # noqa: E402

if len(sys.argv) != 2:
    print(__doc__); sys.exit(3)
cfg, errors = kitlib.load_config(sys.argv[1])
if errors:
    print(f"the config {sys.argv[1]} is not valid:", file=sys.stderr)
    for e in errors:
        print("  - " + e, file=sys.stderr)
    sys.exit(3)
print(kitlib.config_sha256(cfg))
