#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
export PATH="$ROOT/toolchains/lean-4.32.0-rc1-linux/bin:$PATH"
OUT="$ROOT/replay432/Common"
export LEAN_PATH="$OUT/lib:$ROOT/toolchains/lean-4.32.0-rc1-linux/lib/lean"
mkdir -p "$OUT/lib/MathCan"
cp -u "$ROOT/replay432/Transport/lib/MathCan/"*.olean "$OUT/lib/MathCan/"
cd MathCan
dirty=0
for module in CommonGateBound CommonGateCapture; do
  digest=$(sha256sum "MathCan/$module.lean" | cut -d ' ' -f 1)
  stamp="$OUT/$module.compiled.sha256"
  if [[ "$dirty" == 0 ]] && [[ -f "$stamp" ]] && [[ "$(cat "$stamp")" == "$digest" ]] && [[ -f "$OUT/lib/MathCan/$module.olean" ]]; then
    continue
  fi
  lean -o "$OUT/lib/MathCan/$module.olean" "MathCan/$module.lean" > "$OUT/${module}_native.log" 2>&1 || { sed -n '/error:/,+35p' "$OUT/${module}_native.log"; exit 1; }
  printf '%s\n' "$digest" > "$stamp"
  dirty=1
done
echo 'Common modules compiled.'
