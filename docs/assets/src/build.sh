#!/usr/bin/env bash
# Renders the pictures of docs/assets/ from the pages next to this script: hero.png, stages.png, pipeline.png.
# Needs Chrome or Chromium (CHROME=<binary> to name one). The pages hold the numbers as text: after a number in
# README.md changes, change it here and run this again.
set -euo pipefail
cd "$(dirname "$0")"
CHROME=${CHROME:-}
if [ -z "$CHROME" ]; then
  for c in "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" chromium chromium-browser google-chrome; do
    if [ -x "$c" ] || command -v "$c" > /dev/null 2>&1; then CHROME=$c; break; fi
  done
fi
[ -n "$CHROME" ] || { echo "no Chrome or Chromium found: set CHROME=<binary>"; exit 1; }
shot() {  # shot <page> <height in CSS pixels>
  "$CHROME" --headless=new --disable-gpu --hide-scrollbars --force-device-scale-factor=2 --window-size=800,"$2" \
    --default-background-color=00000000 --screenshot="$PWD/../${1%.html}.png" "file://$PWD/$1" > /dev/null 2>&1
  echo "docs/assets/${1%.html}.png"
}
shot hero.html 450
shot stages.html 440
shot pipeline.html 505
