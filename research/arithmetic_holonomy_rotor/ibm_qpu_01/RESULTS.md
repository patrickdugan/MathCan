# AHR-QPU-01 numerical results (2026-11-23)

Recompute `receipts/offline_validation.json` with `python run_benchmarks.py`. The receipt is deterministic with seed 20261123, 1,000 Bernoulli Monte Carlo replicates and **8,192 total shots** across four phase settings.

## Q2 four-phase experiment, ideal dense matrix

- Model: p=2, q=3, J=1, t=1.6, theta=+0.73 rad.
- Phase offsets: 0, pi/2, pi, 3pi/2.
- Ideal return probabilities: `0.062598787811`, `0.414558696387`, `0.443274388217`, `0.073633234652`.
- Calibrated first harmonic: `a1 = -0.255094195809`.
- Four-point complex quadrature: `Z4 = -0.190337800203 - 0.170462730868i`.
- Noiseless recovered phase: `0.730367749889 rad`, a `+0.000367749889 rad` third-harmonic aliasing shift.
- Conditional known-response Fisher information at B=8192: `1765.09 rad^-2`, conditional Cramér–Rao variance `0.00056654 rad^2`.
- Locally asymptotic 95% half-width <= 5 degrees implies at least about **2,344 total shots** in this calibrated-response Bernoulli model. This bound does not cover drift, unknown noise parameters, finite-time bias or coherent measurement alternatives.

## Equal-total-shot comparison

| Model | Angular RMSE, degrees | Measurement settings |
|---|---:|---:|
| Four-phase, ideal binomial sample | 1.35 | 4 |
| Exhaustive marked-edge mask at equal B | 21.40 | 64 |
| Four-phase, simulated 2% independent readout flips | 1.51 | 4 |
| Four-phase, simulated 5% global depolarization | 1.41 | 4 |
| Four-phase, both illustrative channels | 1.62 | 4 |

The 64-setting result compares against the direct AHR-06 parity estimator. It is an estimator-specific difference, not a bound against all possible measurements or quantum algorithms.

## Q3 finite-dimensional verification

With six cube faces and three chosen programmable edges, the AHR-08 addressability schedule uses 24 phase/initial-state settings. Seeded full-Q3 exact-matrix checks at t=0.12 recover the six signed face angles with max angular discrepancy `0.000624 rad`; they verify Bianchi exactness and gauge-fixed chord reconstruction with five independent cycles. This is a short-time numerical test, not a compiler or hardware result.

## CI and limitations

Local `python -m pytest -q`: **11 passed, 1 skipped**; the skip contains the Qiskit-dependent tests because Qiskit and Aer are unavailable. A separate GitHub Actions job installs the optional Qiskit dependencies and executes circuit synthesis, basis mapping, and statevector tests. Until it passes and an IBM backend is inspected, the hardware decision stays HOLD.
