# RH-26C-03 registration: recover the source normalization

**Date:** 2026-11-24 (Asia/Manila). Registration precedes new upstream Lean reads.  
**Pinned upstream:** leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b; observed main a78183e11ebfeebab77920b5e976f0a3edf1fc76. No equivalence claim.
**MathCan:** research/rh26-extraction-rubrics-20261123, draft PR #265.

Question: does the actual character-balance estimate normalize the error bracket by nT*m*b, by an additional density factor, or by another scale? Recover the exact theorem and proof that consume the bracket, with the coefficient of the main observable, thresholds, and every additive error and exponent loss visible within the registered source window.

Start at src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:251–500. Maximum 8 files, 250 returned lines/file, 1200 returned lines, 2 dependency hops. If the theorem spans beyond line 500, freeze the partial proof and record the next window. Only read direct named dependencies if needed. Preserve the previous C-02 scalar-domain and normalization derivation; distinguish it from the actual theorem's normalization. A fixed-coefficient no-loss X/m+m assertion remains UNSOURCED unless justified under its precise hypotheses.

Pass: identify the actual theorem denominator and prove a faithful paper-algebra consequence under exactly stated scalar constraints; record if the remainder of the proof is outside the cap. Falsifier: any compression that loses a subgroup/cardinality/density factor, absolute-value/sign requirement, additive error, or necessary existence constraint is insufficient. No independent Lean verification claim until a separately registered isolated CPU test.

Deliverables: research/rh26/RH26C03_NORMALIZATION.md; LEDGER.md checkpoint and draft PR update. Source reads only. No full clone/build, GPU/QPU, paid compute, or copied upstream proof source.
