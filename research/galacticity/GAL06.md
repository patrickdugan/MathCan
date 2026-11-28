# GAL-06: Stochastic capital and exact prefix reserves

Full mathematical derivations and synthetic receipts:
https://github.com/MoralityLabAI/Compactification-Theory/blob/research/gal01-nonperturbative-20261128/Galacticity/GAL06.md

MathCan/GalacticityRisk.lean defines the least nonnegative reserve
for a finite list of cumulative signed cash flows and proves its
exact specification, nonnegativity, safety, compatible-set
monotonicity, settlement advancement, violation obstruction, and
acquisition inequality. Two further lemmas prove additive branch
Pareto dominance and preservation of success/risk feasibility.
These nine core-Lean candidates address deterministic arithmetic
and finite prefix lists; the full scenario-tree semantics, weighted
quantile theorem, chance-constrained dynamic program, and randomized
convex-hull characterization are paper proofs, not kernel-certified
probability or planner results. Hosted replay is configured separately.
No actual DataGoblin training or model speedup claim.
