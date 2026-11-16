#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC=/home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux
OUT="$ROOT/replay435/Common"
export PATH="$TC/bin:$PATH"
export LEAN_PATH="$OUT/lib:$TC/lib/lean"
MODULES=(CommonGateBound CommonGateCapture)
mkdir -p "$OUT/lib/MathCan"
cp -u "$ROOT/replay435/Transport/lib/MathCan/"*.olean "$OUT/lib/MathCan/"
before=$(sha256sum "$TC/bin/lean" "$TC/bin/leanchecker")
for module in "${MODULES[@]}"; do sha256sum "MathCan/MathCan/$module.lean"; done > "$OUT/source_before.sha256"
for module in "${MODULES[@]}"; do
  lean -o "$OUT/lib/MathCan/$module.olean" "MathCan/MathCan/$module.lean" > "$OUT/${module}_native.log" 2>&1 || { sed -n '/error:/,+30p' "$OUT/${module}_native.log"; exit 1; }
done
pids=()
for module in CommonGateBound CommonGateCapture; do
  leanchecker "MathCan.$module" > "$OUT/${module}_leanchecker.log" 2>&1 & pids+=("$!")
done
status=0
for pid in "${pids[@]}"; do if ! wait "$pid"; then status=1; fi; done
test "$status" = 0
after=$(sha256sum "$TC/bin/lean" "$TC/bin/leanchecker")
test "$before" = "$after"
sha256sum -c "$OUT/source_before.sha256"
printf '%s\n' "$after" > "$OUT/preserved_binary_hashes.txt"
lean --version > "$OUT/version.txt"
echo 'All Hamming/Taylor modules passed preserved Lean 4.35 and leanchecker.'
