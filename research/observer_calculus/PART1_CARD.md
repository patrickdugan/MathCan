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

The labels are nonexclusive: B≈0 → closed quotient; C≈0 → invariant/driver; A≈B≈0 with s≥0.8 → latched memory; B≥0.2 with A≈C≈0 → output register; A≈B≈0 with s≤0.2 → irrelevant. The near-zero cutoff is ≤0.05 of ||D||_F; the report includes explicit `unclassified` when these templates do not fit. In an actual nonnormal network, B=0 means exact **one-step local linear** quotient closure at the measured state; global nonlinear closure needs separate tests.

For 128 seeded rank-matched random bases, a lower-tail metric uses p=(1+#{null<=observed})/129, while a higher-tail metric uses p=(1+#{null>=observed})/129. Every null row carries its original seed. Holm-adjusted inference is reported only after the declared family of tests is fixed. A separate physical perturbation must match the intervention norm per state. A rank-null is not a proxy for a norm-matched causal arm.

The implementation is deliberately standard-library-only for small exact and regression cases. For d=512, production usage should vectorize dense projection calculations and verify parity against this reference. It never fabricates absent T, U, H, task targets, or the original checkpoints. The NRF v0.4 public per-state CSV has the **A/B/C per-coordinate** terms for original k=8; it lacks the full ||D||_F, H, and per-state MSE needed for a complete card.

## Verification
`python -m unittest tests.test_roc01_observer_card -v`

The suite includes an actual output register, a high-causal latch and low-causal irrelevant direction with identical A/B, complement/basis gauge invariance, a 128-basis keyed reproducibility check, norm-matched interventions, zero-dynamics reporting, and error handling. These are synthetic algebraic unit tests, not a new neural experiment.
