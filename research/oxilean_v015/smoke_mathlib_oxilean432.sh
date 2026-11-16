#!/usr/bin/env bash
set -euo pipefail
cd /mnt/c/Users/patri/Documents/Codex/2026-11-15/files-pasted-by-the-user-oxilean/work
ROOT="$PWD"; TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"; ML="$ROOT/mathlib432-local"; OUT="$ROOT/replay432/Analytic"
export PATH="$TC/bin:$PATH"
export LEAN_PATH="$OUT/lib:$ML/.lake/build/lib/lean:$TC/lib/lean"
for pkg in "$ML"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
lean -o "$OUT/lib/RealSmoke.olean" "$OUT/RealSmoke.lean" > "$OUT/real_smoke_native.log" 2>&1
leanchecker RealSmoke > "$OUT/real_smoke_leanchecker.log" 2>&1
"$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" RealSmoke -- OxiLeanDiagnostics.real_add_zero > "$OUT/RealSmoke.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$OUT/real_smoke_verdicts.json" "$OUT/RealSmoke.ndjson" > "$OUT/real_smoke_oxilean.log" 2> "$OUT/real_smoke_oxilean.stderr.log"
python3 -c 'import json; v=json.load(open("replay432/Analytic/real_smoke_verdicts.json")); print(v["totals"]); assert all(d["verdict"]=="verified" for d in v["decls"])'
