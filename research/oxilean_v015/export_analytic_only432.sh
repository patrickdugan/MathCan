#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"; TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"; ML="$ROOT/mathlib432-local"
export PATH="$TC/bin:$PATH"; export REPLAY_OUT="$ROOT/replay432/Analytic"
export LEAN_PATH="$REPLAY_OUT/lib:$ML/.lake/build/lib/lean:$TC/lib/lean"
for pkg in "$ML"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/binary_before.sha256"
mapfile -t ROOTS < "$REPLAY_OUT/roots.txt"
"$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" ApproximationMathlib.CapturedApproximation -- "${ROOTS[@]}" > "$REPLAY_OUT/Lemmas.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 -c 'import json,os; v=json.load(open(os.environ["REPLAY_OUT"]+"/verdicts.json")); print(v["totals"]); assert all(d["verdict"]=="verified" for d in v["decls"]),v["totals"]'
python3 audit_export.py "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
printf 'Analytic export, OxiLean replay and structural audit passed.\n'
