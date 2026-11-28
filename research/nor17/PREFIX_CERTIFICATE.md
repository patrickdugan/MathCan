# NOR-17: sound public-prefix elimination and budgeted certificates

Companion to the NOR-17 research implementation in MoralityLabAI/Compactification-Theory, under research/nor17_prefix_certificates.

The RRC25 synthetic finite-series benchmark publicly supplies two complete demonstration pairs through degree 192, plus a future query input through degree 256. The true future query output remains sealed. Sixteen public program templates constitute the declared complete generating family.

A short exact public demonstration prefix, such as degrees 0 through 160, can disqualify a candidate before a full degree-192 check. Disagreement at an observed coefficient is an exact proof of incompatibility with the full demonstration. This lets a verifier retain a superset of the true full-compatible candidate programs while spending fewer full exact candidate checks.

Define predicates on a finite candidate family:

- \(F(p)\): candidate \(p\) passes the complete public demonstrations.
- \(S(p)\): candidate \(p\) passes an exact short public prefix.
- \(R(p)\): candidate \(p\) was rejected by a full exact check.
- \(Q(p)\): hypothetical full query output on the known public query input.

The soundness premises are \(F(p)\Rightarrow S(p)\) and \(R(p)\Rightarrow\neg F(p)\). Assume the planted true program \(p_*\) belongs to the enumerated family and satisfies \(F(p_*)\).

If a candidate \(c\) has passed full verification and every currently viable candidate satisfies
\[
 S(p)\wedge\neg R(p)\Longrightarrow Q(p)=Q(c),
\]
then the actual future output is \(Q(p_*)=Q(c)\). The theorem is independent of the total number of full checks made to reach that condition. This allows coverage to vary with budgets 4, 8, and 16 while preserving the same conditional logical safety statement.

The kernel-checked [MathCan/NOR17BudgetedPublicCertificate.lean](../../MathCan/NOR17BudgetedPublicCertificate.lean) contains the short-prefix congruence lemma, true-program-survival lemmas, budget-independent output soundness, monotonicity of unanimity under sound candidate elimination and abstention from two still-possible divergent predictions.

The theorem depends on the membership and exact-interpreter premises, and it does not assert that an arbitrary theorem prover or external natural-language task has a complete enumeration of valid possible programs. The empirical study measures certificate coverage and computational work on fresh source cases, and separately checks full candidate masks *after* all policies have frozen their decisions to guard against accidental false rejection.

A prefix check is an additional computation, charged independently from a full native public verification. The experimental work ledger records the sixteen degree-160 prefix candidate comparisons on both demonstrations, cached unary coefficient transformations and candidate-output computations on the degree-256 public query input.

The strongest next formal target is a costed sound-screening refinement theorem that allows exact arithmetic work to be traded against full proof-template verifications under a pinned total coefficient-operation budget.
