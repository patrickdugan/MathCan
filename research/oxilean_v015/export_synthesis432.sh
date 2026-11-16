#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/synthesis_env432.sh"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
mapfile -t ROOTS < "$REPLAY_OUT/roots.txt"
"$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" ApproximationMathlib.MultivariateCapture -- "${ROOTS[@]}" > "$REPLAY_OUT/Lemmas.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 -c 'import json,os; v=json.load(open(os.environ["REPLAY_OUT"]+"/verdicts.json")); print(v["totals"]); assert all(d["verdict"]=="verified" for d in v["decls"])'
python3 audit_export.py "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
printf 'All synthesis exports replayed through OxiLean.\n'
