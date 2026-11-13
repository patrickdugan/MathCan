# GAT-01: formal graph authorization control

Companion to [Control-Harness PR #43](https://github.com/MoralityLabAI/Control-Harness/pull/43).

The research combines OpenAI Math #104 on mean-payoff games and #186 on sharp graph thresholds. The new game grants a defender a fixed global edge-repair budget before an adversary selects a pair of vertices, and it scores indefinite service through mean payoff and parity.

MathCan's GraphAuthorization.lean verifies the finite four-vertex reliability polynomial's Bernstein-basis count: connected graph counts by 0..6 edges are 0,0,0,16,15,6,1. It also checks the arithmetic equivalence between at most b repairs and at most b+1 connected components (assuming a positive component count) and monotonicity with greater budgets.

The finite connection/repair graph theorem has its full mathematical proof in the Control-Harness research note. This Lean file formalizes its arithmetic component and the four-node enumerator. It does not implement or kernel-verify OpenAI #104's quasipolynomial solver, #186's universal graph threshold-width inequality, or arbitrary finite-network game semantics.

The pinned Lean 4 kernel CI checks all added lemmas and prints their transitive axioms; admitted proofs are rejected in the audit.
