# Reproduction and scope

The report and JSON inventories distinguish native Lean 4.35 checks from the
blocked pinned Lean 4.32/OxiLean target replay. The control files are already
exported upstream fixtures, not freshly generated exports.

The original campaign workspace has this layout:

```
work/
  MathCan/          # this isolated research worktree
  oxilean/         # unmodified OxiLean 3adb983 source
  lean4export/     # pinned 3de59f1 source; not built
  build/           # locally built oxilean-verify and rlibs
  checker_source_sha256.txt
```

When using the copies of scripts committed in this directory, set
CAMPAIGN_WORK to that work directory (a Linux /mnt/c/... path under WSL).
The installed binaries are not installed by these scripts. Native checks
currently use the discovered existing runtime:

```
/home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux
/home/duganist/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin
```

For an existing compatible environment:

```bash
export CAMPAIGN_WORK=/absolute/path/to/work
bash "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/build_checkers.sh"
python3 "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/run_controls.py"
bash "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/check_hodge.sh"
bash "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/check_quantized_jet.sh"
bash "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/check_native_audit.sh"
python3 -m unittest discover -s "$CAMPAIGN_WORK/MathCan/research/oxilean_v015" -p test_audit_export.py -v
```

The build script verifies every included checker source file against the
manifest generated from the pinned Git blobs. No Cargo dependencies are
downloaded. normalize_sources.py was used only on fresh private worktrees to
restore exact Git blobs after Windows checkout newline conversion; it is not
an update command and refuses a different HEAD.

To resume the blocked 4.32 replay, use the prerequisites and explicit environment
variables in OXILEAN_V015_REPLAY_REPORT.md. Use a source-only MathCan worktree
at the pinned source commit. replay.sh never installs anything and refuses
missing prerequisites. Its final exit message is not an acceptance decision.

The native dependency graph is a 4.35 environment inspection. The NDJSON auditor
is structural. Neither is an OxiLean verdict for the intended target. Only the
eight control exports currently have OxiLean per-record verdicts.

MathCan/QuantizedJet.lean is a standalone Init-only module, checked explicitly
by the script. Its exact statements and #print axioms are retained in the
source and log. It is not imported by the existing MathCan umbrella file.

The companion Compactification-Theory branch has the detailed mathematical
audit, correction to the note, exact-rational controls and a conditional
whole-network theorem with explicit outstanding spatial-interface premises.
