#!/usr/bin/env bash
# Fetches the pinned plugin source (near-plugins tag v0.5.1) into plugin/near-plugins and checks
# it against PLUGIN_PIN.json: the commit and the sha256 of the two source files the model follows.
set -euo pipefail
KIT=$(cd "$(dirname "$0")/.." && pwd)
PIN="$KIT/PLUGIN_PIN.json"
get() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$PIN" "$1"; }
D="$KIT/plugin/near-plugins"
if [ ! -d "$D/.git" ]; then
  mkdir -p "$KIT/plugin"
  git clone -q --depth 1 --branch "$(get tag)" "$(get repository)" "$D" 2> /dev/null \
    || { echo "FAIL: cannot clone $(get repository) at $(get tag)"; exit 1; }
fi
[ "$(git -C "$D" rev-parse HEAD)" = "$(get commit)" ] || { echo "plugin commit differs from PLUGIN_PIN.json"; exit 1; }
for f in $(python3 -I -c 'import json,sys; print(" ".join(json.load(open(sys.argv[1]))["sha256"]))' "$PIN"); do
  want=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["sha256"][sys.argv[2]])' "$PIN" "$f")
  [ "$(sha256sum "$D/$f" | cut -d' ' -f1)" = "$want" ] || { echo "sha256 of $f differs from PLUGIN_PIN.json"; exit 1; }
done
echo "plugin source: $(get tag) $(get commit) (matches PLUGIN_PIN.json)"
