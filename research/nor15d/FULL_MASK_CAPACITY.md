# NOR-15D: additive upper bounds for complete public-observation signatures

Companion to source-locked [NOR-15D](https://github.com/MoralityLabAI/Compactification-Theory/tree/main/research/nor15d_mask_capacity) in Compactification-Theory and the first-acceptance alias theorem in MathCan NOR15VerifierAlias.

For each observable signature group g, let S(g,c) be the number of examples correctly resolved if all examples with that signature receive the same candidate c. Suppose a verified integer cap K(g) bounds S(g,c) for every c. Then any deterministic signature-only selector f satisfies

\[
  \sum_g S(g,f(g))\le\sum_g K(g).
\]

This follows by summing the individual inequalities. If group size is N(g), the total shortfall at the cap is \(\sum_g (N(g)-K(g))\). The companion Lean source [MathCan/NOR15MaskCapacity.lean](../../MathCan/NOR15MaskCapacity.lean) proves both statements for abstract finite lists and arbitrary nonnegative integer capacities.

On the frozen NOR-15C synthetic dataset, the 40 late_source cases fall into fourteen distinct 16-bit full acceptance-signature classes. Their reported, independently recomputed hindsight maxima are

\[
  [3,3,2,4,3,2,1,1,1,1,1,1,1,1].
\]

The respective class sizes are

\[
  [13,5,5,4,3,2,1,1,1,1,1,1,1,1].
\]

Lean kernel reduction verifies the sums 25 and 40 and the largest group arithmetic 13−3=10. The original numerical report and source JSON SHA-256 establish provenance of these constants in the companion repository. Lean verifies their arithmetic and the generic implication, while the exact public and withheld future membership masks are audited separately by Python.

A hypothetical predictor with complete sixteen-bit public acceptance signatures but without richer source observations can achieve at most 25/40 future-correct on this frozen set, even if its candidate choice per signature is optimized with access to withheld future truth. The bound applies to deterministic selectors and to the **expected** performance of randomized selectors whose choices depend only on the signature.

The source samples were already evaluated by NOR-15B and NOR-15C. These are hindsight upper bounds, not fresh held-out inference results, and the bounds do not constrain a reasoner that analyzes the full public coefficient sequences or performs additional algebraic verification beyond template acceptance bits.
