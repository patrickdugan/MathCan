#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/synthesis_env432.sh"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
set +e
timeout 300 "$TC/bin/leanchecker" -v ApproximationMathlib.JetSynthesis > "$REPLAY_OUT/stock_checker_probe.log" 2>&1
result=$?
set -e
printf '%s\n' "$result" > "$REPLAY_OUT/stock_checker_probe.exitcode"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
printf 'Stock checker probe exit code: %s\n' "$result"
exit "$result"
