#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
export PATH="$ROOT/toolchains/lean-4.32.0-rc1-linux/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/SpatialScalar"
export LEAN_PATH="$REPLAY_OUT/lib:$ROOT/toolchains/lean-4.32.0-rc1-linux/lib/lean"
mkdir -p "$REPLAY_OUT/lib/MathCan"
cd MathCan
dirty=0
for module in SpatialScalar SpatialRouting SpatialNormalized SpatialClipped; do
  case "$module" in
    SpatialScalar) prefix="";;
    SpatialRouting) prefix="routing_";;
    SpatialNormalized) prefix="normalized_";;
    SpatialClipped) prefix="clipped_";;
  esac
  digest=$(sha256sum "MathCan/$module.lean" | cut -d ' ' -f 1)
  stamp="$REPLAY_OUT/$module.checked.sha256"
  if [[ "$dirty" == 0 ]] && [[ -f "$stamp" ]] && [[ "$(cat "$stamp")" == "$digest" ]] && [[ -f "$REPLAY_OUT/lib/MathCan/$module.olean" ]]; then
    continue
  fi
  lean -o "$REPLAY_OUT/lib/MathCan/$module.olean" "MathCan/$module.lean" > "$REPLAY_OUT/${prefix}native.log" 2>&1 || { cat "$REPLAY_OUT/${prefix}native.log"; exit 1; }
  leanchecker "MathCan.$module" > "$REPLAY_OUT/${prefix}leanchecker.log" 2>&1 || { cat "$REPLAY_OUT/${prefix}leanchecker.log"; exit 1; }
  printf '%s\n' "$digest" > "$stamp"
  dirty=1
done
echo 'All spatial modules compiled and checked.'
