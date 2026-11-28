# PGC-QPU: mathematical findings behind the IBM campaign

Evidence classes are kept separate. **Exact** means integer or rational algebra, or a Lean kernel check. **Simulation** means ideal or noisy NumPy/density-matrix runs. **Retrospective hardware** means analysis of archived counts. No prospective hardware result appears here; the experiment code and receipts live in [tensor-lab `pgc_qpu`](https://github.com/patrickdugan/tensor-lab/tree/main/experiments/channel_mpo/ibm_qc23/pgc_qpu).

## 1. Observation rank of the native kicked-Ising channel model (exact algebra on archived Jacobian rows)

The committed 64-row by 14-column Jacobian (`pgc_qpu/receipt.json`) was decomposed independently with `numpy.linalg.svd` (`pgc_qpu/analysis/jacobian_svd_check.py`, relative threshold 1e-6).

| Observation set | Parameters | Rank | Zero-derivative columns |
|---|---:|---:|---|
| Target sites (16 rows) | 6 | 4 | ZZ_22_23, ZZ_4_5 |
| All sites (64 rows) | 6 | 6 | none |
| Target sites, expanded | 14 | 6 | ZZ_22_23, ZZ_4_5, Z_16_23_16, Z_22_23_22, Z_22_23_23, Z_4_5_4, Z_4_5_5, Z_5_6_6 |
| All sites, expanded | 14 | 12 | Z_22_23_23, Z_4_5_5 |

The two rank-deficient directions of the expanded all-site model are the target endpoint phases of edges 22-23 and 4-5, which the QC-26A observer never excites. The weakest nonzero directions in the restricted all-site model are SX_23 (singular value 0.097) and SX_5 (0.141).

## 2. The Ramsey alias, exactly

For diagonal coherent error `exp[-i/2 (a_c Z_c + a_t Z_t + d Z_c Z_t)]` after each CZ and control bit `b`, the probe phase after `m` repetitions is `m (a_t + (-1)^b d + b pi)`; the control's `a_c` never reaches a Z-eigenstate control's Ramsey signal. Even `m` determines `a_t + (-1)^b d` only modulo `pi`, so `(a_t, d) -> (a_t + pi/2, d + pi/2)` leaves every even-repetition observable invariant (profile chi-square difference zero to 2e-14 in the replay). One odd repetition moves the same shift by `pi` in the observed phase and separates the branches (chi-square gap 8.4e3 in the synthetic replay). Swapping control and probe makes the old control the probe, exposing `a_c`. Both statements are checked in `pgc_qpu/test_pgc_ramsey.py` against a Qiskit statevector (simulation).

## 3. Q3 cubical curl map: finite algebra (exact; Lean file `MathCan/Pregeometry/Q3Curl.lean`)

Twelve edge phases, six face fluxes, `curl: R^12 -> R^6` with integer entries.

| Statement | Result |
|---|---|
| Rank of `curl` | 5 (left null space spanned by the Bianchi vector `(-1,1,1,-1,-1,1)`) |
| Gauge subspace | kernel of dimension 7, equal to the image of vertex-potential gradients (8 vertices minus 1) |
| Gauge-independent cycle degrees of freedom | 5 |
| Five faces | any five of six faces have rank 5; every omitted-face 5x5 chord minor has determinant `-1,-1,1,1,-1,-1`, so reconstruction of the five cycle phases is integral and well defined modulo `2 pi` |
| Four faces | every four-face subset has rank 4: one cycle direction is unobserved, and an explicit pair of configurations with identical four-face data and different sixth flux exists for all 15 subsets |
| Conditioning | five-face edge-space singular value ratio 2.803 for every omitted face; in the chord gauge 2.618 (omit face 1) to 6.846 (omit face 0) |

The Lean file checks the Bianchi relation, vertex-gauge kernel, the six unimodular determinants and the 15 four-face minor facts by kernel evaluation (`decide +kernel`). It is not imported by `MathCan.Pregeometry`; the workflow `pgc-q3-curl.yml` checks it separately. The Python replay uses exact `Fraction` rank and reproduces the same table.

### Measurement-side findings (simulation, seed 20261126)

* A sixth-face consistency check cannot localize an error: the Bianchi residual for a 0.3 rad bias on any one face is 0.31-0.33 rad, so a single violated relation implicates six faces equally.
* Phase-insensitive (cosine-only) face data has exactly two consistent sign patterns in 400 of 400 random configurations (a global orientation reflection); the Z2 flux sector is orientation-blind. Quadrature (cos and sin) data removes the reflection.
* On principal-branch fluxes with 0.05 rad noise, 46.6% of configurations have integer Bianchi winding `n != 0`. Using the wrapped residual keeps the covariance-weighted projection exact modulo `2 pi` (max error 0.42 rad in the extreme noise draw); the unwrapped residual fails by up to 3.14 rad.
* Covariance-weighted Bianchi projection reduces mean squared flux error from 0.0499 (raw) to 0.0416 (identity weights) and 0.0351 (inverse-variance weights; the formula `tr S - B^T S^2 B / B^T S B` gives 0.0355).

Existing hardware receipts cover only the Q2 single face (`ibm_qpu_01/receipts/hardware_q2`); Q3 remains simulation. A Q3 hardware run is not justified by an unresolved measurement question yet, because the four-face and orientation facts above are exact.

## 4. Quantum causal cancellation and `event_response_not_transitive`

The diamond update `F(x0,x1,x2,x3) = (0, x0, x0, x1 xor x2)` of `OperationalCounterexamples.lean` has the CNOT realization `s -> a, s -> b, a -> t, b -> t`, mapping `|s,a0,b0,t0>` to `|s, a0 xor s, b0 xor s, t0 xor a0 xor b0>`. For every one of the eight contexts the target is independent of `s`: source-to-target response is absent although source-to-middle and middle-to-target responses exist and a directed gate path joins `s` to `t`. The Boolean mirror in `pgc_qpu/qpu02/qpu02_sim.py` enumerates all contexts and the clamp theorem (`middle_clamp_restores_source`): resetting either middle register makes the response magnitude 1. For superposition input, the state is `GHZ_3(s,a,b) tensor |0>_t`; the target is product with the GHZ block, `<XXX>_{sab} = +1` and the GHZ fidelity witness is 1. Measure-and-forget dephasing of one middle qubit leaves the target response at 0 while the coherence witness drops to 0, separating operational distinguishability from joint coherence. Noisy simulation shows diagonal coherent ZZ and crosstalk errors and symmetric readout error create no Z-basis influence on the zero-response target; amplitude damping creates apparent influence of 0.9% (Kingston-like) to 2.1% (pessimistic) in the intact circuit, with the depth-matched echo control carrying 0.6% to 1.4%. The Lean theorem concerns the Boolean model; the quantum statements here are simulations of its CNOT realization.
