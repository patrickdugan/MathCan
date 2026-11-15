#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
export TC432="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export EXPORTER_SOURCE="$ROOT/replay432/lean4export-source"
export EXPORTER="$EXPORTER_SOURCE/.lake/build/bin/lean4export"
export MATHCAN_SOURCE="$ROOT/replay432/MathCan-source"
export OXI_BIN="$ROOT/build/oxilean-verify"
export REPLAY_OUT="$ROOT/replay432/Hodge"
export AUDITOR="$ROOT/audit_export.py"
export PATH="$TC432/bin:$PATH"
mkdir -p "$REPLAY_OUT"
exec > >(tee "$ROOT/logs/hodge432_pipeline.log") 2>&1
lean --version > "$REPLAY_OUT/lean-version.log"
grep -F 'b4812ae53eea93439ad5dce5a5c26591c31cb697' "$REPLAY_OUT/lean-version.log"
bash "$ROOT/replay.sh"
export LEAN_PATH="$REPLAY_OUT/lib:$EXPORTER_SOURCE/.lake/build/lib/lean:$TC432/lib/lean"
lean "$ROOT/replay432/CompareExport.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
python3 "$ROOT/accept_hodge432.py"
sha256sum "$REPLAY_OUT/Hodge.ndjson" "$REPLAY_OUT/lib/MathCan/Hodge.olean"
