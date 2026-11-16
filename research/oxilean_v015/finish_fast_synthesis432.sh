#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/synthesis_env432.sh"
CANONICAL_OUT="$REPLAY_OUT"
export REPLAY_OUT=/dev/shm/oxilean-synthesis432-20261116/replay
python3 - <<'PY'
from pathlib import Path
import hashlib,json,os
r=Path(os.environ['REPLAY_OUT']);v=json.loads((r/'verdicts.json').read_text())
assert all(d['verdict']=='verified' for d in v['decls'])
assert v['totals']['unsupported']==v['totals']['rejected']==0
h=hashlib.sha256()
with (r/'Lemmas.ndjson').open('rb') as stream:
 for data in iter(lambda:stream.read(1024*1024),b''):h.update(data)
assert h.hexdigest()==v['input']['sha256']
print(v['totals'],flush=True)
PY
python3 "$ROOT/audit_export_fast.py" "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json" > "$REPLAY_OUT/audit_status.log" 2>&1 &
audit_pid=$!
export LEAN_PATH="$LEAN_PATH:$ROOT/replay432/lean4export-source/.lake/build/lib/lean"
lean -j 2 "$CANONICAL_OUT/CompareSynthesis.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1 &
compare_pid=$!
result=0
wait "$audit_pid" || result=1
wait "$compare_pid" || result=1
cat "$REPLAY_OUT/audit_status.log"
if [[ "$result" != 0 ]]; then cat "$REPLAY_OUT/source_export_comparison.log"; exit 1; fi
cp "$REPLAY_OUT/source_export_comparison.log" "$REPLAY_OUT/axioms.log"
sha256sum -c "$CANONICAL_OUT/source_before.sha256"
sha256sum -c "$CANONICAL_OUT/binary_before.sha256"
python3 "$ROOT/mirror_synthesis_mathlib432.py" --verify-only
printf 'Full audit, native source comparison and mirror revalidation passed.\n'
