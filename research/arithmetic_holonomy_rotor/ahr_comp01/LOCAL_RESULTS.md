# Local numerical receipt summary

Source verifier Git blob: 375184c3bfe66dbf8e26b8ffe5308a3d317c4b14 (byte-identical to the locally executed verifier).
Command: OPENBLAS_NUM_THREADS=1 python verify.py --max-qubits 20
Seed: 20261124
Environment: Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0.
Result: PASS. 34 benchmark rows.

- 5 compact-reconstruction fixtures through 20 dimensions, maximum wrapped reconstruction error 8.89e-16; gauge-copy error 1.78e-15.
- 4 dense normalized fourth-moment comparisons, maximum absolute error 2.10e-13; exhaustive per-direction face averages checked.
- 26 exact counting fixtures, satisfying counts 0, 1, 2, 4, 8.
- 16 dense detuned Gaussian comparisons at d=3–6, four evolution times; maximum absolute error 3.25e-14. The no-detuning Clifford formula also checked.
- CNOT construction error 2.23e-16; phase-conjugation error 1.58e-16.
- Product-formula step doubling convergence verified against dense exponential for d=3,4,5,6.

## d=20 at t=0.7

| Arm | Return probability | Method |
|---|---:|---|
| Zero flux | 0.001830313132790649 | exact product |
| Pi flux with detuning | 0.8565881835880323 | exact Gaussian covariance |
| Affine | 0.0033020984705658327 | 8 symmetric steps |
| Quadratic | 0.0039510503796180655 | 8 symmetric steps |
| Quadratic | 0.004102087472968741 | 16 symmetric steps |
| Pi flux with detuning | 0.8690553150121404 | 8 symmetric steps |

Quadratic state L2 distance between 4 and 8 steps: 0.08144825502936784. Between 8 and 16: 0.020019377205431614. These are convergence diagnostics, not exact d=20 error guarantees. Quadratic state storage 16,777,216 bytes, precomputed phase tables 167,772,160 bytes; 722 single-control and 8,778 double-control Rz per unoptimized step. The Gaussian comparison uses only a 42x42 covariance matrix. Local approximate statevector evolution took about 2.17 seconds for the eight-step quadratic case; the Gaussian evaluation took about 0.00043 seconds. These are implementation observations, not a quantum/classical advantage comparison.

Run the exact source verifier to regenerate the complete machine-readable receipt. CI will emit its own independently generated receipt as an Actions artifact. No live hardware use.
