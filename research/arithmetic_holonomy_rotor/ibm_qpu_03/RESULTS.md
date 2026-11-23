# AHR-QPU-03 results

This report records the historical FakeFez baseline. Its simulated likelihood design passed the registered precision, coverage, convergence, and circuit thresholds. A separate read-only calibration and Open Plan check supports the current proposal. Q3 remains on HOLD for execution pending separate approval of the exact manifest. [Live-calibration results](LIVE_CALIBRATION_RESULTS.md) · [Execution gate](HARDWARE_GATE.md) · [Historical manifest](receipts/q3_candidate_manifest.json)

## Archived Q2 hardware reference

The audit pinned MathCan main at `2efb49fe12b1dfc46434793042efc6daddda16e2`. The merged archive in PR #262 was checked against the original draft #254. PR #264 describes the status update. AHR-07 established the signed Fourier scan and its aliasing limitation. AHR-08 supplied the three marked edges and the six site selectors. AHR-09 supplied the signed cube boundary and tree gauge. AHR-QPU-02 informed the calibration ranking, paired references, and historical-backend fallback.

Replaying job `dc1vksqnj2vs73dfu0n0` verified 36 unique cases, 2,048 shots per case, physical map 9/10, QPY and calibration digests, and the primary acceptance criterion. The forward and reverse phases were +38.903662° and −42.859973°. The measured primary quadrature was −0.154296875 − 0.198730469i, compared with the exact −0.154937987 − 0.203112569i. The tree interval contained zero. The job consumed 21 seconds. This is the Q2 hardware dataset. [Source and replay receipt](receipts/provenance.json) · [Merged hardware archive](../ibm_qpu_01/HARDWARE_Q2_ARCHIVE.md)

## Q3 mathematical and circuit checks

The integer cochain ranks are 7, 5, and 1. The Smith factors of the face map are 1, 1, 1, 1, 1, and 0. Both cochain products vanish. All six exact responses have the prescribed leading orientation, and the scaled complex error drops roughly fourfold when time is halved. The first harmonic at the reference time of 0.12 is only 3.324×10⁻⁵ to 3.354×10⁻⁵ across the six faces. Both the gauge copy and the detuned gauge copy preserve exact return probabilities. The wrong-corner control combines the two adjacent face paths, and the spanning-tree control removes ideal flux sensitivity. [Exact and branch-control receipts](receipts/controls.json) · [Short-time and integer receipts](receipts/provenance.json)

The dated target selected physical qubits 136, 143, and 142 on FakeFez. The same snapshot ranks qubits 8, 9, and 10 as its best extension of the earlier physical pair. The snapshot is dated 2025-02-26. The table reports maxima and uses squared classical fidelity on the binary return/non-return measurement.

| Synthesis on historical target | Max return error | Max CZ | Max depth | Critical path, µs | Mean noisy binary fidelity |
|---|---:|---:|---:|---:|---:|
| Exact with SABRE, level 3 | <1×10⁻¹⁴ | 29 | 127 | 5.17 | 0.9984 |
| Exact with basic routing | <1×10⁻¹⁴ | 46 | 148 | 6.72 | 0.9973 |
| Suzuki 2, 2 repetitions | 0.02043 | 215 | 802 | 25.76 | 0.9910 |
| Suzuki 2, 4 repetitions | 0.00796 | 427 | 1,592 | 49.62 | 0.9833 |
| Suzuki 2, 8 repetitions | 0.00222 | 851 | 3,172 | 97.33 | 0.9701 |
| Suzuki 4, 1 repetition | 0.02958 | 533 | 1,987 | 61.55 | 0.9802 |
| Edge-match Strang, 2 repetitions | 0.05553 | 215 | 483 | 24.08 | 0.9857 |
| Edge-match Strang, 4 repetitions | 0.01321 | 425 | 963 | 46.28 | 0.9710 |

Both exact methods passed. Each product-formula method exceeded the 160-CZ limit. The selected exact method preserves return probabilities to numerical precision on this target. The compiled gauge copy and tree have residual differences in Aer, even though their exact controls behave as predicted. The first-face tree has \(|Z_4| \simeq 0.000744\) in Aer. [Target snapshot](receipts/calibration.json) · [Circuit results](receipts/compilation.json)

## Time and estimator comparison

The training grid selected 1.175 for four-phase Fourier and Richardson, 1.200 for eight-phase Fourier, and 2.000 for the likelihood. The last value is the upper registered grid boundary. The time-grid receipt reports exact phase bias, first- and third-harmonic amplitudes, native approximation and Aer phase bias, shot variance, and delta-normal coverage for each face and time. The final coverage values below come from 1,000 held-out draws per design with shared nuisance perturbations.

| Design at 98,304 inference shots | Worst face RMSE | Lowest face coverage | Joint chord coverage |
|---|---:|---:|---:|
| Four-phase single time | 34.90° | 90.3% | 89.0% |
| Four-phase with shared reference | 25.12° | 80.8% | 79.3% |
| Eight-phase Fourier | 35.01° | 90.5% | 90.4% |
| Two-time Richardson | 118.85° | 60.1% | 20.8% |
| Exact-response likelihood, equal shots | 2.20° | 93.7% | 94.2% |
| Exact-response likelihood, Fisher allocation | 1.86° | 94.3% | 94.4% |

The equal-shot likelihood worst-face RMSE was 3.17°, 2.20°, and 1.56° at 2,048, 4,096, and 8,192 shots per setting. At 4,096 shots its per-face nominal 95% marginal half-widths had medians of 2.12° to 4.39°. Doubling the shared perturbations raised the worst-face RMSE to 2.32°. The likelihood results are local to the commanded field and the held-out phases and noise model. The physical pilot proposal retains equal allocation and budgets a separate 98,304 shots for controls. Fisher allocation is a simulated same-budget comparison. It concentrates shots and uses some settings below 2,048 or above 8,192.

On the four-phase 4,096-shot design the worst raw face RMSE was 29.74° and the worst projected RMSE was 23.45°. Its raw Bianchi RMS was 54.05° and the projected closure residual fell below 2×10⁻¹³ degrees. The five likelihood chord RMSEs were 1.77° to 2.20°. The likelihood enforces Bianchi compatibility by construction. At the phase seams, the separate Gaussian experiment found roughly 75% coordinate wrapping with reliable local projection at the narrowest noise level. As the noise widened to 1.5 rad, 35.8%–36.4% of draws crossed the local Bianchi branch and joint coverage fell to 64.7%–66.3%. A small projected closure residual alone is insufficient evidence for accurate phase recovery. [Training grid](receipts/time_grid.json) · [Held-out statistics](receipts/statistics.json) · [Branch and control results](receipts/controls.json)

These results concern a programmed finite-dimensional hopping Hamiltonian, the calibrated simulator, and the specified inference procedure. The pilot includes both the full-cube spectral response and separate controls for orientation, gauge invariance, broken cycles, and detuning. No Q3 hardware measurements are available.
