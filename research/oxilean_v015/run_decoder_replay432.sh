#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export PATH="$TC/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/Decoder"
export LEAN_PATH="$REPLAY_OUT/lib:$TC/lib/lean"
python3 prepare_decoder_replay.py
sha256sum MathCan/MathCan/SentinelDecoder.lean MathCan/MathCan/DecodedJetCapture.lean > "$REPLAY_OUT/source_before.sha256"
bash check_decoder432.sh
for module in SentinelDecoder DecodedJetCapture; do
  leanchecker "MathCan.$module" > "$REPLAY_OUT/${module}_leanchecker.log" 2>&1
  sha256sum "MathCan/MathCan/$module.lean" | cut -d ' ' -f 1 > "$REPLAY_OUT/$module.checked.sha256"
done
lean "$REPLAY_OUT/PrintDecoder.lean" > "$REPLAY_OUT/axioms.log" 2>&1
mapfile -t ROOTS < "$REPLAY_OUT/roots.txt"
"$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" MathCan.DecodedJetCapture -- "${ROOTS[@]}" > "$REPLAY_OUT/Lemmas.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 audit_export.py "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json"
export LEAN_PATH="$REPLAY_OUT/lib:$ROOT/replay432/lean4export-source/.lake/build/lib/lean:$TC/lib/lean"
lean "$REPLAY_OUT/CompareDecoder.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
sha256sum -c "$REPLAY_OUT/source_before.sha256"
python3 accept_decoder432.py
echo 'Decoder and spatial capture replay completed.'
