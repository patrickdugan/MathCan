# NOR-15: rigorous finite-resolution bounds for recurrent path observability

Paired with the independent NOR-15A experimental study in \`MoralityLabAI/Compactification-Theory/research/nor15_trajectory_sufficiency/\`.

Let \(p,q\) denote two endpoint hidden states, \(a,b\) the corresponding early states, \(R\) any deterministic reconstruction decoder, and \(d_E,d_L\) distances on early/late state spaces. If \(d_E\) satisfies a triangle inequality and \(R\) is \(L\)-Lipschitz,

\[
d_E(a,b)
\le d_E(a,R(p)) + L\,d_L(p,q)+ d_E(R(q),b).
\]

The theorem holds on abstract sets with Nat-valued distance upper bounds, with no topology, norm, linearity, or GRU assumptions. In particular,

\[
d_E(a,b) > 2\varepsilon + L\,d_L(p,q)
\quad\Longrightarrow\quad
\max\{d_E(a,R(p)),d_E(R(q),b)\}>\varepsilon.
\]

The kernel-proved [MathCan/NOR15TrajectoryObservability.lean](../../MathCan/NOR15TrajectoryObservability.lean) includes the general bound, error-or-separation corollaries, the deterministic endpoint-label collision obstruction, and gate-factorization through an endpoint hidden state. The theorem is useful for finite-precision hidden observations: the experimentally estimated distances require conservative outward rounding to Nat bounds before substituting them into this exact statement.

**Certification limit.** The theorem alone cannot show an actual RRC25 endpoint collision, state-space noninjectivity, or positive conditional mutual information. Empirical finite-difference Jacobians and reconstruction errors are not formal evidence for the theorem's numerical premises without a separate interval enclosure. A pointwise fixed-input-suffix transition Jacobian also differs from the input-varying random mapping from source examples to their terminal hidden states.

Target experiments:
- Train-only H9→H4 linear and nonlinear ridge predictors.
- Test on newly source-locked public inputs and report errors by family.
- Compute local H4→H9 Jacobians while holding the remaining five public input rows fixed.
- On pairs with nearby H9, evaluate both H4 discrepancy and the conservative Lipschitz error budget. Save all numeric assumptions and rounding conventions.

All five Lean declarations use the standard kernel and print their axiom inventories under the pinned \`leanprover/lean4:v4.35.0\` toolchain. This mathematics is a reusable finite-observation lower-bound framework; its significance for learned reasoning depends on an independently established trajectory feature effect.
