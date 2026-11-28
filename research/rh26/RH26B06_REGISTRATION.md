# RH-26B-06 registration: finish alpha/beta rank-step extraction

**Date:** 2026-11-24 (Asia/Manila).  
**Status:** preregistered before new upstream Lean source reads.  
**Upstream read pin:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Upstream main observed:** `90cc2e125ba4b6ca10be17d918857800ba6c39cc` (changed; no assumption of equivalence).  
**Host:** MathCan branch `research/rh26-extraction-rubrics-20261123`, draft PR #265.

## Question

Finish the precise source proof of `PositivityTheory.ThKG.Leaves.kBeta` and `kAlpha` and identify which nonzero split-component evaluations permit cancellation in the actual automorphic rank-change identities. Relate their proof to the independently checked field-algebra statements in RH-26E-01 without claiming those toy statements establish the analytic inputs.

## Registered scope and acceptance

Read `src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean:251-500` first, with at most 250 source lines. If it ends earlier, record EOF. Prioritize exact theorem signature, hypotheses and proof steps; use only direct dependency pointers where a proof obligation remains ambiguous. Limits: 8 distinct upstream Lean files, 250 lines per file, 1200 aggregate source lines, two further dependency hops, no whole-repository source scan. Count repeated source reads and distinguish requested from returned lines.

**PASS:** source anchors show both complete proof bodies and the actual use of the nonzero test component, split identities, and factor invertibility. **PARTIAL:** one or more conclusions cannot be grounded under the read limit. **BLOCKED:** no precise proof source recovered. Quantitative multiplicity and the conjectured X/m+m bound remain UNSOURCED until an independently located theorem proves them.

Null/falsifier: comparison equalities can become vacuous when the selected component vanishes; alpha and beta unit witnesses and orientations must stay distinct. A proof relying on a zero evaluation, unsupported inverse, missing matched configuration, or incorrect orientation fails the intended abstraction. Preserve the previous `KConst`, `Below(n)`, `EndA/EndB` and `KeyA/KeyB` provenance from RH-26B-05.

## Deliverables

Write `research/rh26/RH26B06_RANK_STEP_PROOFS.md` with source links, exact algebraic proof schematic, read receipt and next experiment. Update LEDGER.md and PR #265. No upstream build, copied upstream proof source, new kernel check, GPU/QPU, or paid compute in this source-only experiment. Any independent Lean abstraction is a separate preregistered RH-26E-02 run.
