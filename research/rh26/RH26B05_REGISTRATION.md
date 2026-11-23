# RH-26B-05 registration: resolve the theta-comparison endgame

**Registered:** 2026-11-23, before upstream source reads for this experiment.  
**Research branch:** `research/rh26-extraction-rubrics-20261123`, draft MathCan PR #265.  
**Immutable upstream source:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Observed upstream main at registration:** `98cc3736f046abae883d8cda839c84f3004257a7`; source changes are unassessed and will not be substituted into this run.

## Question and null

Determine precisely how `PositivityTheory.ThKG.agree_of_leaves` yields `WeilTensorModels.ThetaIntegralsAgree ∧ LocalMatching` from the leaves assembled by `Sph.Tr.closeSph`, and identify which inputs supply `OneConst`, `StepAlpha`, and `StepBeta`. Investigate whether `EndA` and `EndB` are actual alpha/beta transport suppliers or only auxiliary statements.

**Null:** the endgame is a large aggregator whose apparent short proof rests on distinct analytic or geometric assumptions. A symbol-name match alone cannot establish the claimed correspondence.

## Pinned starting points

1. `src/Development/WeilBound/ThetaLifts/AgreeOfLeaves.lean`, targeted theorem and signature.
2. `src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean`, lines 211 onward, for the completed `endAB_sph` proof.
3. `src/Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesS.lean` only if it materially establishes a missing input type.
4. Follow at most two further named dependency hops within this run; use exact declaration or import pointers to choose additional files.

## Bounds and acceptance

- Maximum **8 unique upstream Lean files**, **250 source lines per file**, and **1,200 source lines total**. Include empty or overlapping line probes in the request ledger. The source may end earlier than the requested range.
- Inspect file-line anchors for every claimed edge. Classify the targets separately as FOUND (direct proof supplying exact statement), PARTIAL (named intermediate), or BLOCKED / UNSOURCED (boundary exhausted). Preserve any mismatch between similarly named propositions.
- Record analytic hypotheses on `EisBL` and `SiegelWeilStd` when visible, and identify whether the full rank-two alpha/beta transport equations or nonzero `IsConst` witnesses are ever established.
- A direct source-level theorem is **not** an independent MathCan Lean verification. The earlier RH-26E-01 passing field-algebra toy remains a separate result.
- Falsifiers: losing `Decay`, `Coinv`, `IsMatched`, uniqueness/nonzero scalar constraints, distinct unit witnesses, or a local ramification/archimedean hypothesis invalidates an alleged compression.
- Output: `research/rh26/RH26B05_ENDGAME.md`, newest `research/rh26/LEDGER.md` entry, and draft PR #265 update. Preserve exact upstream/MathCan SHAs, source-window counts, and the next *precise* symbol to inspect.
- Read-only GitHub connector for upstream; no archive/full-repo source scan, unlicensed code import, local or paid compute, GPU, QPU, or upstream build. An independent mathematical toy is optional only after a concrete formulation emerges.

## Resume contract

Another session can start solely from the latest ledger and `RH26B05_ENDGAME.md`. If the eight-file/1,200-line limit is reached first, commit a BLOCKED receipt with paths and missing declarations, then stop.
