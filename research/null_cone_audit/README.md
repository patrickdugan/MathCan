# NCG-01: trace bounds and closed-cut convergence

The [audit note](audit_notes.md) records the assumptions needed to turn a trace
estimate into a bound on Hilbert-space dimension. It also identifies the
closed-cut convergence step in arXiv:2611.34924v1 that needs further proof review.

The operator examples use exact fractions. They cover a finite-entropy state
with infinite rank, charge matching with an unbounded cutoff, and distinct
normalized limits along strongly exhausting finite-rank projections.

From the repository root:

```bash
python3 research/null_cone_audit/operator_countermodels.py --check research/null_cone_audit/operator_countermodels.json
lake env lean MathCan/NullConeTraceBound.lean
```

`MathCan/NullConeTraceBound.lean` proves four statements about scaled integer
partial sums. Its scope is the finite-sum core of the dimension argument. The
Hilbert-space theorem and its analytic assumptions appear in the audit note.
The workflow compiles this module and checks its printed axiom inventory.

The companion exact finite-field learning oracle is staged for
`MoralityLabAI/Compactification-Theory`, under `research/ncg01` on branch
`research/ncg01-boundary-constraints-20261126`. Its source and receipt accompany
this audit in the deliverable package.

Local validation with Lean 4.35.0 accepted all four theorems. Each printed
axiom inventory is `[propext, Quot.sound]`. The compiler version, source hash,
official archive hash and complete output are retained in
`lean_validation.json` and `lean_validation.log`.
