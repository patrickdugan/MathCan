#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
mkdir -p replay432 logs
exec > >(tee logs/setup_replay432_sources.log) 2>&1
for spec in 'MathCan 13151576dd83939f7850f7f3025a49fa98e370b8' 'lean4export 3de59f10bc4b4a0f2de698597aeb1246caa0df0a'; do
  read -r name pin <<< "$spec"
  dest="$ROOT/replay432/$name-source"
  if [ ! -d "$dest/.git" ]; then
    git clone --no-checkout --local --no-hardlinks "$ROOT/$name-repo" "$dest"
    git -C "$dest" config core.autocrlf false
    git -C "$dest" config core.filemode false
    git -C "$dest" checkout --detach "$pin"
  fi
  test "$(git -C "$dest" rev-parse HEAD)" = "$pin"
  test -z "$(git -C "$dest" status --porcelain --untracked-files=no)"
  printf '%s %s\n' "$name" "$pin"
done
echo '6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5  replay432/MathCan-source/MathCan/Hodge.lean' | sha256sum --check
