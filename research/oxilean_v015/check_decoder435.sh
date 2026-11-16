#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC=/home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux
OUT="$ROOT/replay435/Decoder"
export PATH="$TC/bin:$PATH"
export LEAN_PATH="$OUT/lib:$TC/lib/lean"
mkdir -p "$OUT/lib/MathCan"
cp -u "$ROOT/replay435/SpatialFormalization/lib/MathCan/"*.olean "$OUT/lib/MathCan/"
before=$(sha256sum "$TC/bin/lean" "$TC/bin/leanchecker")
cd MathCan
for module in SentinelDecoder DecodedJetCapture; do
  lean -o "$OUT/lib/MathCan/$module.olean" "MathCan/$module.lean" > "$OUT/${module}_native.log" 2>&1 || { cat "$OUT/${module}_native.log"; exit 1; }
  leanchecker "MathCan.$module" > "$OUT/${module}_leanchecker.log" 2>&1 || { cat "$OUT/${module}_leanchecker.log"; exit 1; }
done
after=$(sha256sum "$TC/bin/lean" "$TC/bin/leanchecker")
test "$before" = "$after"
printf '%s\n' "$after" > "$OUT/preserved_binary_hashes.txt"
lean --version > "$OUT/version.txt"
echo 'Both decoder modules passed preserved Lean 4.35 and leanchecker.'
