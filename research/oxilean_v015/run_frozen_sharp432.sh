#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/sharp_env432.sh"
chmod +x "$EXEC_RAM/bin/lean" "$EXEC_RAM/bin/leanchecker"
bash "$ROOT/freeze_sharp432.sh"
canonical="$ROOT/replay432/Sharp"
mkdir -p "$SHARP_RAM/results"
cp "$canonical/manifest.json" "$canonical/roots.txt" "$canonical/modules.txt" "$canonical/DirectKernel.lean" "$canonical/CompareSharp.lean" "$canonical/source_before.sha256" "$canonical/binary_before.sha256" "$SHARP_RAM/results/"
export SHARP_REPLAY_OUT="$SHARP_RAM/results"
bash "$ROOT/build_sharp432.sh"
bash "$ROOT/kernel_sharp432.sh"
bash "$ROOT/export_sharp432.sh"
bash "$ROOT/compare_sharp432.sh"
echo 'Frozen build, native kernel, independent replay and full comparison completed.'
