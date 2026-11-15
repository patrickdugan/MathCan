#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
TC=/home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux
export PATH="$TC/bin:$PATH"
export LEAN_PATH="$PWD/MathCan/.lake/build/lib/lean:$TC/lib/lean"
exec > >(tee logs/native_dependency_audit.log) 2>&1
cd MathCan
lean research/oxilean_v015/NativeAudit.lean
