# NOR-15C: deterministic first-acceptance alias obstruction

Companion formalization of the finite four-verification audit in MoralityLabAI/Compactification-Theory, research/nor15c_verifier_alias.

The source-locked NOR-15B study contained 40 cases with the same 9×8 public model input and corresponding shared hidden state. All deterministic rankers that consume only this representation give the same candidate order before querying the public verifier. The verifier may still distinguish source cases through its candidate-acceptance responses.

The Lean theorem [MathCan/NOR15VerifierAlias.lean](../../MathCan/NOR15VerifierAlias.lean) defines the first accepted candidate in any finite ordered list and proves:

1. If two cases have the same exact public acceptance Boolean function, their first accepted candidate under a common rank is identical.
2. If the two cases have disjoint future-correct candidate sets, one source must fail future correctness whenever the fixed ordering selects a public-accepted candidate.
3. The full alias obstruction composes the two results without relying on model architectures, source generators, or floating-point arithmetic.

The result is **conditional on complete acceptance-mask equality**. Two source cases may share the same input tensor yet have different full acceptance masks. Their verifier transcripts can then distinguish them, so a deterministic ranker with a common initial order can still return different first accepted candidates. The experimental 40-case group has 14 distinct full public-acceptance masks, requiring a separately exact combinatorial enumeration of 16×15×14×13 candidate orders to find its hindsight ceiling.

The companion enumeration finds a sample-specific maximum of 15/40 future-correct cases under fixed-four first-positive stopping, versus 8/40 for the original GRU ranking. Future outcomes are used to select that maximum retrospectively, making it an **oracle upper bound**, not an implementable generalization result or information-theoretic mutual-information claim.

The module builds under Lean 4.35.0, and its axiom prints show only standard propext for the functional-equality proofs. No sorry or supplemental axiom is required.

The next mathematical target is a family-size bound for all public-mask equivalence classes: if an equivalence class contains cases with incompatible future-correct masks, the best single fixed candidate cannot achieve perfect correctness on that class. This requires keeping verifier-alias signatures distinct from neural-representation aliases.
