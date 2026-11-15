#!/usr/bin/env bash
# No installation or download. Run only after the exact prerequisites exist.
set -euo pipefail
: "${TC432:?Set TC432 to an existing Lean 4.32.0-rc1 installation}"
: "${EXPORTER:?Set EXPORTER to the prebuilt pinned lean4export binary}"
: "${EXPORTER_SOURCE:?Set EXPORTER_SOURCE to the pinned exporter source worktree}"
: "${MATHCAN_SOURCE:?Set MATHCAN_SOURCE to the unchanged pinned MathCan source worktree}"
: "${OXI_BIN:?Set OXI_BIN to the verified OxiLean 0.1.5 binary}"
: "${REPLAY_OUT:?Set REPLAY_OUT to a new writable result directory}"
: "${AUDITOR:?Set AUDITOR to audit_export.py}"
test -x "$TC432/bin/lean" && test -x "$TC432/bin/leanchecker"
test -x "$EXPORTER" && test -x "$OXI_BIN"
export PATH="$TC432/bin:$PATH"
lean --version | tee /dev/stderr | grep -F 'version 4.32.0-rc1,'
test "$(git -C "$EXPORTER_SOURCE" rev-parse HEAD)" = 3de59f10bc4b4a0f2de698597aeb1246caa0df0a
test "$(git -C "$MATHCAN_SOURCE" rev-parse HEAD)" = 13151576dd83939f7850f7f3025a49fa98e370b8
test -z "$(git -C "$EXPORTER_SOURCE" status --porcelain --untracked-files=no)"
test -z "$(git -C "$MATHCAN_SOURCE" status --porcelain --untracked-files=no)"
echo "6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5  $MATHCAN_SOURCE/MathCan/Hodge.lean" | sha256sum --check
mkdir -p "$REPLAY_OUT/lib/MathCan"
"$OXI_BIN" --version > "$REPLAY_OUT/checker-version.log"
grep -F 'oxilean-verify 0.1.5' "$REPLAY_OUT/checker-version.log"
cd "$MATHCAN_SOURCE"
# Avoid lake/elan shims and leave lean-toolchain and all 4.35 outputs untouched.
lean -o "$REPLAY_OUT/lib/MathCan/Hodge.olean" MathCan/Hodge.lean > "$REPLAY_OUT/native432.log" 2>&1
export LEAN_PATH="$REPLAY_OUT/lib:$TC432/lib/lean"
leanchecker MathCan.Hodge > "$REPLAY_OUT/leanchecker432.log" 2>&1
"$EXPORTER" MathCan.Hodge -- MathCan.Hodge.closed_path_gauge > "$REPLAY_OUT/Hodge.ndjson"
sha256sum "$REPLAY_OUT/Hodge.ndjson" > "$REPLAY_OUT/export.sha256"
set +e
"$OXI_BIN" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Hodge.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
code=$?
set -e
printf '%s\n' "$code" > "$REPLAY_OUT/oxilean.exit-code"
if [ "$code" -gt 1 ]; then exit "$code"; fi
python3 "$AUDITOR" "$REPLAY_OUT/Hodge.ndjson" --target MathCan.Hodge.closed_path_gauge --output "$REPLAY_OUT/axiom-graph.json"
# A separate acceptance step must compare the imported type to this source,
# inspect every dependency verdict and approve the precise axiom inventory.
# Exit 0 here is NOT a successful campaign acceptance decision.
printf '%s\n' 'Replay artifacts produced; statement and closure acceptance review still required.'
