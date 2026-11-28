# NOR-21: degree-independent public exactness and out-of-family limits

Companion mathematics to the RRC25 NOR-21 applied study in MoralityLabAI/Compactification-Theory.

The study increases public demonstration degree to 512 and 1024 and query-input degree to 768 and 1536, maintaining sixteen exact candidate programs. It tests independently generated source families with coherent planted outputs, demonstrations deliberately corrupted beyond the original 192-coefficient window, and future targets deliberately altered outside the enumeration's generating program family.

The new Lean module [MathCan/NOR21ObservationCompleteness.lean](../../MathCan/NOR21ObservationCompleteness.lean) proves:

- A total finite checker that selects its first publicly compatible candidate must abstain if **every** candidate fails the exact public check.
- Complete-family future correctness holds when the true planted program belongs to the accepted set and all publicly compatible programs predict the same query output.
- Two generative worlds with exactly the same complete public observation but distinct target futures cannot both be correctly predicted by any deterministic public-only selector. This remains true if the selector may abstain, where abstention counts as incomplete in the strong exact-output claim.
- A public selector that returns the valid-world future must return that same output when the hidden target is changed while public data stay identical, causing an explicit out-of-family false acceptance.
- NOR-19's exact finite-list streaming equality theorem applies to arbitrary integer coefficient magnitudes and public series lengths.
- The exact number of coefficient multiplication sites in normalized formal-series reciprocal inversion through degree n obeys the triangular formula \(2C(n)=n(n+1)\). Increasing the degree from n to n+1 adds n+1 multiplication sites.
- Streaming removes thirty-two length-(n+1) candidate-output coefficient arrays in the declared abstract workspace model relative to eager caching.

The proof separates public *compatibility* from private *truth*. The family-completeness premise is essential, and a modified hidden future can create a public-indistinguishable world outside that premise. It would be inaccurate to classify the resulting false acceptance as a counterexample to the conditional Lean theorem.

At degree 1024, the exact inversion site count is 524,800 per normalized full inverse, and at degree 512 it is 131,328. This counts integer multiplication sites, not machine cycles or actual bigint multiplication cost. Source coefficient bit lengths, Python interpreter overhead and live allocation are measured separately in the applied benchmark.

The original RRC25 model-visible header implementation only reads the earliest 192 coefficients. NOR-21 uses it to infer the header while independently implementing full public verifier comparisons at degrees 512 and 1024, so the result does not mistake 192-degree truncation for a deep certificate.
