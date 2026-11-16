#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export PATH="$TC/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/Common"
export LEAN_PATH="$REPLAY_OUT/lib:$TC/lib/lean"
MODULES=(CommonGateBound CommonGateCapture)
python3 prepare_common_replay.py
for module in "${MODULES[@]}"; do sha256sum "MathCan/MathCan/$module.lean"; done > "$REPLAY_OUT/source_before.sha256"
bash check_common432.sh
check_module() {
  local module="$1"
  leanchecker "MathCan.$module" > "$REPLAY_OUT/${module}_leanchecker.log" 2>&1
  sha256sum "MathCan/MathCan/$module.lean" | cut -d ' ' -f 1 > "$REPLAY_OUT/$module.checked.sha256"
}
pids=()
for module in CommonGateBound CommonGateCapture; do check_module "$module" & pids+=("$!"); done
status=0
for pid in "${pids[@]}"; do if ! wait "$pid"; then status=1; fi; done
test "$status" = 0
lean "$REPLAY_OUT/PrintCommon.lean" > "$REPLAY_OUT/axioms.log" 2>&1
mapfile -t ROOTS < "$REPLAY_OUT/roots.txt"
"$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" MathCan.CommonGateCapture -- "${ROOTS[@]}" > "$REPLAY_OUT/Lemmas.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 audit_export.py "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json"
export LEAN_PATH="$REPLAY_OUT/lib:$ROOT/replay432/lean4export-source/.lake/build/lib/lean:$TC/lib/lean"
lean "$REPLAY_OUT/CompareCommon.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
sha256sum -c "$REPLAY_OUT/source_before.sha256"
python3 accept_common432.py
echo 'Hamming/Taylor/capture replay completed.'
