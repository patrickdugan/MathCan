#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
mkdir -p build logs
exec > >(tee logs/build_checkers.log) 2>&1
RUST_BIN=/home/duganist/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin
export PATH="$RUST_BIN:$PATH"
export CARGO_PKG_VERSION=0.1.5
export CARGO_PKG_NAME=oxilean-kernel
rustc --version --verbose
sha256sum --check --status checker_source_sha256.txt
# All runtime dependencies are these three crates. Compile their default-feature
# sources directly to avoid resolving/downloading unrelated workspace dev deps.
rustc --crate-name oxilean_kernel --crate-type rlib --edition=2021 -C opt-level=2 oxilean/crates/oxilean-kernel/src/lib.rs -o build/liboxilean_kernel.rlib
export CARGO_PKG_NAME=oxilean-export
rustc --crate-name oxilean_export --crate-type rlib --edition=2021 -C opt-level=2 -L dependency=build --extern oxilean_kernel=build/liboxilean_kernel.rlib oxilean/crates/oxilean-export/src/lib.rs -o build/liboxilean_export.rlib
export CARGO_PKG_NAME=oxilean-verify
rustc --crate-name oxilean_verify --crate-type rlib --edition=2021 -C opt-level=2 -L dependency=build --extern oxilean_kernel=build/liboxilean_kernel.rlib --extern oxilean_export=build/liboxilean_export.rlib oxilean/crates/oxilean-verify/src/lib.rs -o build/liboxilean_verify.rlib
rustc --crate-name oxilean_verify_bin --edition=2021 -C opt-level=2 -L dependency=build --extern oxilean_kernel=build/liboxilean_kernel.rlib --extern oxilean_export=build/liboxilean_export.rlib --extern oxilean_verify=build/liboxilean_verify.rlib oxilean/crates/oxilean-verify/src/main.rs -o build/oxilean-verify
build/oxilean-verify --version
sha256sum build/oxilean-verify
