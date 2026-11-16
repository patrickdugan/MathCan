#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"; TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"; ML="$ROOT/mathlib432-local"
export PATH="$TC/bin:$PATH"; export REPLAY_OUT="$ROOT/replay432/Synthesis"
export LEAN_PATH="$REPLAY_OUT/lib:$ML/.lake/build/lib/lean:$TC/lib/lean"
for pkg in "$ML"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
if [[ -n "${SYNTHESIS_MATHLIB_MIRROR:-}" ]]; then
  python3 - "$SYNTHESIS_MATHLIB_MIRROR" "$ROOT" <<'PY'
import hashlib,json,sys
from pathlib import Path
target,root=sys.argv[1:];root=Path(root);r=root/'replay432/Synthesis'
m=json.loads((r/'mathlib_mirror.json').read_text())
assert m['status']=='matched' and m['target']==target
assert m['artifact_receipt_sha256']==hashlib.sha256((root/'MATHLIB_ARTIFACT_RECEIPT.json').read_bytes()).hexdigest()
(r/'mirror_used.json').write_text(json.dumps({'target':target,'artifact_receipt_sha256':m['artifact_receipt_sha256']},indent=2)+'\n')
PY
  export LEAN_PATH="${LEAN_PATH//"$ML"/"$SYNTHESIS_MATHLIB_MIRROR"}"
fi
