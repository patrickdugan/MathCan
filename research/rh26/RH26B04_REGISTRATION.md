# RH-26B-04 preregistration: theta transport proof suppliers

**Date:** 2026-11-23 (Philippines). **Status:** SOURCE-ONLY REGISTRATION, prior to this experiment's upstream file reads.

## Scope

Research the *suppliers*, rather than the definitions, for `WeilTensorModels.StepAlpha`, `StepBeta` and `OneConst` in the community RH repository. Preserve the pinned upstream commit `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, whose exact declarations were inspected in [RH26B03_ORIGINAL_PREMISES.md](RH26B03_ORIGINAL_PREMISES.md). Upstream `main` has since moved: record the observed current head separately, and make no silent substitution of revised source.

## Precommitted search and verification gates

1. Resolve the symbols from narrowly scoped paths, repository Git trees (filename metadata only) and exact path searches. Prefer `Development/AbelianVarietyTheory/Proofs/TwistedOperators`, `Development/AbelianVarietyTheory/PublishedTheorems`, and `Development/AutomorphicArithmetic/ThetaCorrespondence`. Avoid a recursive full-repo listing, archive download or whole-text search.
2. Read at most **eight distinct upstream Lean files**, **250 source lines per file**, **1,200 aggregate lines**, **two dependency hops** from located supplier. Keep precise path and line receipts. Query-specific single-line probes count toward this total.
3. Capture exact supplying declaration (name, input type, output proposition), where it is consumed, and whether the supplied result is the full `StepAlpha`, `StepBeta`, `OneConst`, or a weaker auxiliary. Document any missing critical hypotheses (normalization, archimedean factor, local matching, nonzero, convergence, analytic continuation). A theorem-name resemblance is not evidence of implication.
4. Grade each of the three targets independently: **FOUND** only with a pinned line anchor proving or yielding the exact relevant proposition; **PARTIAL** for an anchored lemma contributing only a subgoal; **BLOCKED / UNSOURCED** if the search boundary runs out first.
5. Compare `main` with pinned SHA using bounded file/blob metadata for the exact touched paths. Record provenance and changed-state uncertainty. Any newly changed upstream theorem needs a separate session and commit pin.
6. Accept a bounded dependency map with at least one exact supplier anchor as source-level PASS; otherwise commit a **BLOCKED** receipt with unresolved names and the next precise file paths. Never claim a kernel verification from a source reading.

## Falsifiers / null

A likely competing explanation is that `ThetaIntegralsAgree` is discharged through a bundled, large published-results interface where named `StepAlpha`, `StepBeta` and `OneConst` are not independently supplied in small files. Reject a proposed simplification whenever a local equality is mistaken for a full rank-change identity with a nonzero scalar, or when the two separate existential integer-unit triples are merged.

## Resources / deliverables

Use GitHub connector reads only, with no full upstream build, paid compute, GPU/QPU, new model inference or CI requirement for source discovery. Write `research/rh26/RH26B04_SUPPLIERS.md`, update `research/rh26/LEDGER.md`, and update draft PR #265. Preserve the separately verified Lean 4.35 scalar gym in RH-26E-01.

**Exact starting anchors:** `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:529-550,597-630`, upstream SHA above. Follow the proof interfaces referenced from `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:833-839` only as needed. Do not repeat earlier broad code scans.

## Restart contract

The next agent reads this registration and the latest ledger entry first. A completed run has an exact upstream pin, eight-or-fewer file receipt, per-target disposition, source-backed dependencies, missing lemmas, and next file path.
