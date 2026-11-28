# RAM-12 preregistration: state-conditioned Lean traces of certified historical tactic scripts

Date: 2026-11-15. This protocol is committed **before** the first RAM-12 Lean-state extraction.

## Immutable original evidence

- Historical TRAIN source: `patrickdugan/MathCan@c84e2025334e9a967c1297425a490f98d5b3d189`, Lean `leanprover/lean4:v4.35.0`.
- Public original frozen worklist: `research/ram11f/locked_worklist.jsonl`, SHA-256 `f5876539862a0f4f913dc3af620be0d038555efcdd3611754e002dc353c3b2aa`.
- Native RAM-11F original complete-source proofs: 76 scripts across 22 original MathCan TRAIN theorem roots; 152 successful original Lean4.35 compilations, source artifact SHA-256 `536ebffc38c399b730cb3fe14ebdeb3a6a72590518885a9e52e8cd26f20f9b06` (MathCan Actions run 43712039711).
- Corresponding private LoopedTransformers corpus: 230 unique certified prefix-to-next-action labels, 176 prefix contexts; positive-prefix JSONL SHA-256 `221d918c81652d801ab46c8d4a7682511e7a8c715653f478072103e393711899`. These labels have *no newly observed per-step goal state yet*. Source script provenance remains immutable.
- All 76 input scripts were previously chosen by retrospective RAM-11 analysis of RAM-08 original training examples. No new PEF or RAM-10 heldout cases are involved.

## Native instrumentation

Use one **full certified original theorem source** per script. Replace only that original theorem's proof with the original script from the frozen worklist and insert the same fixed `ram12_observe` logging tactic *before* each original tactic action. The inserted tactic may read and pretty-print the actual Lean goal list and visible referenced definitions. It must leave proof goals and the proof term unchanged. Compile the entire instrumented source under the pinned original Lean4.35 source environment; run a second independent compilation for every one of the 76 sources. A previously certified, uninstrumented complete source must be reconstructed and byte-hashed against its original recorded SHA-256 before the new source is generated.

Each run must yield exactly one marked state observation per original tactic position. Both runs must contain the same complete ordered scripts and identical full goal lists/definitions at every position. The only positive labels are `(original theorem, exact prefix, next action)` that belong to a twice-compiled complete source. Keep every candidate source, two separate logs, and exact source hashes. Fail the entire extraction on an incomplete run, compiler error, unexpected axiom, duplicate or missing state marker, mismatched state or modified worklist.

Expected exact labels: 282 action occurrences, 230 unique (theorem, exact prefix, next-action) labels, 176 distinct original theorem-prefix contexts, 22 roots. Duplicate prefixes in different complete source scripts must yield identical state strings and visible definitions; do not average or silently choose one. The original RAM-08 `exact prefix` distinction remains binding. The original theorem source reference proof body is never an input feature.

Prohibited: synthetic proof goals, unobserved successor-as-failure labels, new search heuristics fitted on original PEF/TEST, `sorry` or `admit` in scored replacement proofs, changes to the original theorem statements, new axioms, and model updates before trace audit is complete. The historical RAM-11F *proof script* certification and RAM-12 *state instrumentation* are distinct evidence classes.

## Evaluation and learning boundary

After extraction, create a separately pinned state-conditioned positive curriculum with full printed context, pending goals, candidate action, exact proof provenance, remaining steps along the supporting complete script, and source/checkpoint digests.

For later retrospective model fitting, assign whole original theorem roots using `SHA256("RAM12-FRESH-STATE-20261115/" + source_file + ":" + theorem)` modulo six: residue 0=DEV, 1=holdback, remaining residues=TRAIN. Record counts, script family balance and any repeated goal-state SHA across splits, and prohibit state-based leakage. All three cohorts derive from historical old-MathCan TRAIN, which was used during earlier RAM work; this RAM-12 holdback is *not* an independent unseen theorem-family transfer test. Any numerical result must be labeled retrospective. Run no heldout comparison until all state records have been independently audited and training is frozen.

Historical positives may be paired only with independently compiler-replayed *negative* actions in the same exact original state/prefix; positive actions not previously observed in RAM-08 remain positive and unobserved alternatives remain censored. The original native/shape-frequency and recurrent/flat comparisons remain required for any complete-theorem claim. The original RAM-08 PEF 120-case and RAM-10 new-source assessments remain unchanged and unscored until their dedicated runs.

## Operational constraints

The public MathCan GitHub Actions runner has demonstrated functioning native Lean4.35. Run source-only, in a GitHub-hosted Ubuntu CPU job, with no paid compute. The old MathCan source is an isolated checkout, not a mutated branch worktree. The new code and training labels live in separately named `research/ram12/` files. Archive complete evidence as an Actions artifact. No merge or publication of model capability claims without native audit results.
