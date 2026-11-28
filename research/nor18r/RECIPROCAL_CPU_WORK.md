# NOR-18R: reciprocal bigint work and cached verifier parity

Companion mathematics to [NOR-18R](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor18r-cpu-bigint-memory-20261116/research/nor18r_runtime) and the existing [NOR-18 cached verifier theorem](https://github.com/patrickdugan/MathCan/pull/94).

The RRC25 candidate family is the sixteen ordered U/V pairs over four unary transformations. Each unary operation appears four times in the U position and four times in the V position. For one public demonstration, the native independent sixteen-candidate checker therefore executes eight reciprocal R transforms among U/V, with sixteen additional R transforms if the frozen public base operation is itself R.

The cached checker constructs all sixteen candidates using four shared unary transforms, applying the reciprocal operation **once** per demonstration input. Thus the exact savings are **7 R inversions per demonstration when the base is not R**, or **23** when the base is R.

The operand-width audit in Python replays the exact recurrence

\[
r_n=-\sum_{k=1}^{n} f_k r_{n-k}
\]

and records each operand's *observed* positive bit length. For an exact inversion on a given source, let \(w\) be the sum of the products of the two multiplicands' bit lengths. If the two demonstration sources have observed values \(w_1,w_2\), independent full checks incur \(8(w_1+w_2)\) R-inversion operand-width proxy units for a non-R base, while the cached checker incurs \(w_1+w_2\). Under an R base those counts become \(24(w_1+w_2)\) and \(w_1+w_2\), respectively.

The kernel-proven [MathCan/NOR18RReciprocalReuse.lean](../../MathCan/NOR18RReciprocalReuse.lean) establishes these exact counting identities and the fact that a shared public-query inversion does not alter the savings. It also proves that full public acceptance after a sound prefix screen yields exactly the same accepted candidate set as full public verification without that screen.

These theorems support source-locked CPU comparisons of four executable variants: sixteen independent native checks, sixteen full checks reusing four unary transforms, and degree-160/176 cached prefix screens followed by native full checks on surviving candidates.

The operand-width product is a documented integer-operation size proxy. Python's actual multiplication algorithm, memory allocation overhead, OS scheduling, native CPU timings and process peak RSS are measured independently in NOR-18R. None of these physical quantities is derived from the Lean theorem.
