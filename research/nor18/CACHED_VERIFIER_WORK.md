# NOR-18: exact cached-verifier cost algebra and nested public-prefix sieves

Companion to the [NOR-18 Compactification-Theory experiment](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor18-costed-prefix-frontier-20261116/research/nor18_costed_prefix).

The RRC25 program grammar has a frozen base operator and 16 ordered pairs of U/V operations chosen from four unary series transformations. Each full public verifier comparison applies its base, U and V unary transforms to two degree-192 public demonstration sources. Performing those 16 checks separately recomputes the base 16 times and each of the four U/V operations eight times.

A shared-cache checker computes the four unary transforms once on each demonstration, then constructs and compares the same sixteen candidate outputs. Let \(b\) be the proxy cost of the base unary map, \(u\) the sum of the four unary transform costs, and \(c\) one candidate composition/equality comparison cost at a chosen degree \(n\). All are nonnegative integers. The exact identity is

\[
C_{\mathrm{separate}}=2(16b+8u+16c),\quad
C_{\mathrm{cached}}=2(u+16c),
\]

\[
C_{\mathrm{separate}}-C_{\mathrm{cached}}
=2(16b+7u).
\]

The kernel-proven [MathCan/NOR18CachedVerifierWork.lean](../../MathCan/NOR18CachedVerifierWork.lean) establishes this integer identity and both weak and strict cached-work bounds, with strictness when any unary operation cost is positive. The result is exact **for the declared arithmetic proxy**. It is not an empirical claim that cached code runs faster after accounting for Python overhead, memory, or big-integer bit lengths.

The same module proves that agreement of two public coefficient sequences at prefix length \(n\) implies agreement at all shorter prefixes. Consequently, any candidate rejected by a sound shorter prefix cannot revive at a deeper prefix. That explains why NOR-18's source-locked candidate masks form nested sets over degrees 112, 128, 144, 160, 176 and 192.

A budgeted certificate theorem combines public generator-family membership, the survival of every true compatible program under sound screening, unanimity of remaining hypothetical future outputs and an explicit finite coefficient-work cap. The per-program consistency and output interpretation are proved in earlier MathCan NOR-16/17 developments; the new theorem makes computational work an explicit logical obligation.

The NOR-18 empirical experiment uses five short public prefixes and a batched full-degree mask, with a common per-case work unit fixed from the average independent full-template cost across all sixteen candidates. It compares 4-, 8- and 16-unit work caps on heldout complete-public-distinct sources. The selected depth should be evaluated against both a no-screen certificate and the previously studied degree-160 sieve under the same work cap. The numerical result and any statistical claim must be grounded in independent hosted evidence.

No hidden future labels, model weights or candidate-program identities enter the new cost proxy. These are algebraic resource bounds for a synthetic finite program family.
