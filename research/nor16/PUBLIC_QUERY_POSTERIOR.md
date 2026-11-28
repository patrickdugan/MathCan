# NOR-16: predictive consensus and complete-public-input identifiability

Companion to [NOR-16 in Compactification-Theory](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor16-public-query-consensus-20261115/research/nor16_public_query_consensus).

The RRC-25 synthetic proof-template setting gives the reasoner the input source coefficients for the held-out query through degree 256. It withholds the *query output*, which is needed for the final correctness grade. Publicly accepted candidate programs can therefore be applied to that known query input, yielding candidate predictions without consulting the withheld answer.

For a finite set \(A\) of accepted programs and a common uniform prior across them, let \(y_j\) denote the exact prediction of candidate program \(j\) on the public query input. For every proposed output \(y\), its posterior success probability is

\[
\Pr(Y=y\mid\text{public data})=
\frac{\#\{j\in A:y_j=y\}}{|A|}.
\]

The maximum-posterior predictive strategy selects an output with the largest exact multiplicity. With \(M=\max_y \#\{j\in A:y_j=y\}\), any output-only point decision has correct-program count at most \(M\), hence unavoidable expected error probability at least \(1-M/|A|\).

The kernel-checked [MathCan/NOR16PublicQueryConsensus.lean](../../MathCan/NOR16PublicQueryConsensus.lean) formalizes the count-based mass, posterior ceiling, common-denominator ordering, and quantitative \(n-M\) loss lower bound over accepted latent programs.

A second theorem addresses the identifiability barrier directly. Suppose candidate programs \(a\) and \(b\) agree on **all** available public observations, including both degree-192 demonstrations and the degree-256 query *input*, but produce different future query *outputs*. Any deterministic function of that complete public observation must fail for at least one of those two valid possible worlds. The theorem holds for arbitrary public observation and future types. The RRC-25 audit constructs source-specific counterfactual pairs using two accepted candidate programs and their publicly simulated query outputs, without reading the actual withheld target.

The first executed independent NOR-16 experiment evaluated 192 new late_source public inputs sharing one original GRU-visible tensor. It found 140 exact public ambiguity certificates and a full-mask conditional MAP posterior expected success total of 78.9375, compared with 80 observed future-correct in the sixteen-check arm. The four-check consensus achieved 36 correct versus the original GRU's 33, insufficient for its preregistered criterion. All sixteen-check comparisons carry substantial additional public verification work, so they cannot support equal-budget native performance claims.

The uniform posterior identity assumes equal prior weight across accepted U/V candidate programs after conditioning on the public header and source coefficients. If a source generator places unequal prior probabilities on program identities, multiplicities must be replaced by prior-weighted sums. The proof's arithmetic is exact; source-specific candidate equivalence and full JSON provenance are checked separately in the companion repository.
