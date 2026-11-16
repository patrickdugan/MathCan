Multivariate synthesis continuation: 47 new authored roots prove arbitrary-dimensional
Taylor jet synthesis, constructed tau/2 coefficient accuracy and decoded smooth/Holder
approximation. All 257 research roots now have replay evidence. See
MULTIVARIATE_SYNTHESIS_REPORT.md for verification and remaining network obligations.

Taylor-analysis continuation (2026-11-16): 40 authored roots and 12 attributed
upstream roots now establish common gates, genuine scalar Taylor remainders,
and decoded capture approximation bounds. All 210 research roots have replay
evidence. Read COMMON_TAYLOR_FORMALIZATION_REPORT.md for exact scope and open work.

Common gate continuation (2026-11-16): 23 new replayed roots establish the
uniform 2^(k+1)*D^k transport bound and its exact/robust decoded spatial capture.
Read COMMON_GATE_BOUND_REPORT.md. This checkpoint has 181 research roots.

# Current reproduction entry points

Hamming/Taylor continuation (2026-11-16): 63 additional proved and replayed
lemmas now connect computed amplitude words, concrete polynomial Taylor matrices,
fixed-width correction frames and scheduled decoded spatial capture. Read
HAMMING_TAYLOR_FORMALIZATION_REPORT.md for the current 158-root research status.
Remainder lists and communication statuses below describe earlier checkpoints.


Decoder continuation (2026-11-16): 39 additional lemmas prove exact/robust
sentinel decoding and its composition with clipped spatial jet capture.
See DECODER_FORMALIZATION_REPORT.md for the current 95-root research status,
trace fixtures and remaining obligations. Publication of the research branches
is now authorized; the earlier local-only statements below describe the prior run.


The pinned Hodge replay is now accepted. Read OXILEAN_V015_REPLAY_REPORT.md and
the two pinned432_*/ACCEPTANCE.json files. The previous blocked report is kept
under its PRE_INSTALL name. Native 4.35 evidence remains separate historical
and project-compatibility evidence.

Set CAMPAIGN_WORK to the original work directory, using a /mnt/c/... path in
WSL. All new shell scripts and acceptance validators honor it. The exact
Lean 4.32 runtime is under $CAMPAIGN_WORK/toolchains/lean-4.32.0-rc1-linux;
the pinned exporter source/build is under replay432/lean4export-source.
The source-only Hodge checkout remains at the requested source commit.

```bash
export CAMPAIGN_WORK=/absolute/path/to/work
bash "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/run_hodge432.sh"
bash "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/check_spatial_lean432.sh"
bash "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/export_research_lemmas432.sh"
python3 "$CAMPAIGN_WORK/MathCan/research/oxilean_v015/accept_research_lemmas432.py"
python3 -m unittest discover -s "$CAMPAIGN_WORK/MathCan/research/oxilean_v015" -p test_hodge_acceptance.py -v
```

When restoring the bundle elsewhere, first copy the included root-level shell and Python helpers into CAMPAIGN_WORK, and the two Compare*.lean files into CAMPAIGN_WORK/replay432. Provision the source checkouts and private toolchain paths described above before running the commands.

The comparison Lean sources must be at $CAMPAIGN_WORK/replay432/CompareExport.lean
and CompareLemmas.lean. Their exact copies are included here. Installation and
build metadata are included; toolchain binaries are not in Git or the packet.
The official archive URL/digest is in lean432_release.json, and the private
installation receipt is LEAN432_INSTALLATION.json. Restoring the 12 relative
symlinks uses finish_lean432_install.py after archive extraction. No default
toolchain change is needed. build_exporter432.sh builds the exact pinned source.

The standalone Init-only modules QuantizedJet and SpatialInterface are checked
explicitly, without changing the existing MathCan umbrella imports. Exported
types AND proof values are compared with their native source environment.

For the mathematical construction, read SPATIAL_INTERFACE_THEOREM.md and run
the companion Compactification-Theory research/quantization/test_spatial_circuit.py.
The generated numeric matrices contain only rational affine/ReLU layers.
The complete analytic theorem is proved on paper, not formalized in Lean.

## Ordered-field spatial continuation

Read LEAN_SPATIAL_FORMALIZATION.md and pinned432_spatial/ACCEPTANCE.json.
The four additional standalone modules have 42 proved and replayed lemmas;
native Lean 4.32 and preserved 4.35 kernel checks both pass. The full analytic
theorem remains open. For the latest pipeline, copy the included spatial
helpers into CAMPAIGN_WORK, then run replay_spatial_scalar432.sh and
test_spatial_acceptance.py there. The old 14-lemma corpus is retained intact.
