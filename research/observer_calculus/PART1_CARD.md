# ROC-01 Part 1: a common recurrent-observer card

This is the source contract for every rank-k claim in [Part 0](PART0_INVENTORY.md). Code: [observer_card.py](observer_card.py). Registry: [ROC01_REGISTRATION.md](ROC01_REGISTRATION.md).

Fix a state h and an observed future-output map Y. Obtain the suffix Jacobian T=D(F^n)(h). Write D=T-I, let U have orthonormal columns, and let Q complete U to an orthonormal basis (so Q^T Q=I and U^T Q=0):

| Card entry | Definition | Interpretation |
|---|---|---|
| A | U^T D U | observed-to-observed computed change |
| B | U^T D Q | dark-to-observed injection, necessary for linear quotient closure |
| C | Q^T D U | observed-to-dark outgoing change, necessary for invariance of observer span |
| H | Σ_i w_i J_i^T J_i, J_i=DY_i(h_i) | OLM-07 causal output Gram for a declared task/output/horizon |
| s(U) | tr(U^T H U)/tr(H) | fraction of causal output-Jacobian energy captured; undefined if tr(H)=0 |
| task MSE | same-state frozen decoder and target | remains null until independently measured |
| a,b,c | ||A||_F,||B||_F,||C||_F divided by ||D||_F | dimensionless fractions; when D=0 return zeros plus zero_dynamics flag |

Also retain **unnormalized Frobenius values** and per-observed-coordinate values ||A||_F/√k, ||B||_F/√k, ||C||_F/√k. These differ from the scalar `rho_Delta=||B||/sqrt(||A||²+||B||²)` used in NRF v0.4. A small rho_Delta can result from enormous A as well as very small B; it cannot identify a latch or an irrelevant hidden direction without output H.

The original absolute-cutoff diagnostics are retained as `legacy_absolute_threshold_tags` for historical replay. **Amendment C** supersedes those cutoffs prospectively: the initial raw card is `unclassified` until 128 distinct rank-matched Haar nulls define the per-metric medians and six-direction Holm-adjusted evidence. Compute r_a=a/median_null(a), r_b=b/median_null(b), r_c=c/median_null(c); use relative near-zero ≤0.20 and large B ≥1.20, with Holm p≤0.05. High output capture requires (s-median_null(s))/(1-median_null(s))≥0.80, while low capture requires s/median_null(s)≤0.20, each with Holm p≤0.05. The tags remain nonexclusive and the C≈0 label is **invariant subspace**. Undefined or degenerate nulls give `unclassified` and prohibit calibrated penalty claims. See [dated amendment C](ROC01_AMENDMENT_2026-11-16C.md).

Physical B=0 still means exact one-step local linear quotient closure at the measured state. The new objective uses (b/median_null(b))² so a random rank-k observer has a comparable rank-relative reference across k. Original raw a,b,c,s are retained for interpretability and historical comparisons.
For 128 seeded rank-matched random bases, a lower-tail metric uses p=(1+#{null<=observed})/129, while a higher-tail metric uses p=(1+#{null>=observed})/129. Every null row carries its original seed. The declared six-test family is a↓, b↓, c↓, b↑, s↑, s↓; Holm-adjusted p-values are computed together. A separate physical perturbation must match the intervention norm per state. A rank-null is not a proxy for a norm-matched causal arm.

The implementation is deliberately standard-library-only for small exact and regression cases. For d=512, production usage should vectorize dense projection calculations and verify parity against this reference. It never fabricates absent T, U, H, task targets, or the original checkpoints. The NRF v0.4 public per-state CSV has the **A/B/C per-coordinate** terms for original k=8; it lacks the full ||D||_F, H, and per-state MSE needed for a complete card.

## Verification
`python -m unittest tests.test_roc01_observer_card -v`

The suite includes an actual output register, a high-causal latch and low-causal irrelevant direction with identical A/B, complement/basis gauge invariance, a 128-basis keyed reproducibility check, norm-matched interventions, zero-dynamics reporting, and error handling. These are synthetic algebraic unit tests, not a new neural experiment.
