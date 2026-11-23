# AHR-QPU-03 live-calibration simulation

**Design GO. Execution HOLD.** The simulation passed the preregistered native compilation, precision, coverage, and convergence gates on a fresh `ibm_kingston` snapshot. The proposed 48 circuits at 4,096 shots each have an estimated 70.27-second QPU usage and a 106-second cap. IBM reported 515 free Open Plan QPU seconds in both read-only checks, most recently at 22:50 Singapore time on 23 November 2026. No Q3 job was submitted. [Exact proposed manifest](receipts/live/q3_candidate_manifest.json) · [Read-only allocation receipt](receipts/live/calibration_recheck.json)

## Target and compilation

- IBM exposed operational connected triples on `ibm_fez`, `ibm_kingston`, and `ibm_marrakesh`. After accounting for native gate errors, edge duration, readout error, and the most recent prior coupler calibration, Kingston qubits 67, 68, and 69 ranked first. The best Fez extension of the Q2 pair was 8, 9, and 10. [IBM calibration snapshot](receipts/live/calibration.json) · [Drift recheck](receipts/live/calibration_recheck.json)
- Kingston's current calibration was timestamped 22:34:13 Singapore time and its prior calibration was 22:03:26. The reported CZ error estimates were unchanged at 0.0991% and 0.1355%. Both CZ durations were 68 ns. Readout errors were 0.525%, 0.476%, and 0.757% on physical qubits 67, 68, and 69, respectively. The repeated read returned the same compact target and noise channels.
- Exact synthesis with SABRE used at most 29 CZ gates, depth 127, and a 5.72 µs critical path in both the 72-setting bakeoff and the proposed workload. Its maximum noiseless return error was below 10⁻¹⁴ in the bakeoff. Mean noisy binary fidelity was 0.99929 in Aer. Each product-formula method exceeded the native gate-count limit. [Compilation comparison](receipts/live/compilation.json)
- All 48 circuits use the same three physical qubits. The classical-bit map is `[68, 69, 67]` for 47 circuits. The zero-field, zero-offset reference uses `[67, 68, 69]`. Reconstruction and the asymmetric Aer readout model use the recorded per-case map. [Case records](receipts/live/q3_candidate_manifest.json)

## Simulated precision

The training sweep selected 1.225 for four-phase Fourier and Richardson, 1.200 for eight-phase Fourier, and 2.000 for exact-response likelihood. At 4,096 shots per setting, the 1,000 held-out likelihood trials gave a **2.08°** worst-face RMSE, **93.9%** lowest marginal face coverage, and **94.9%** joint chord coverage at nominal 95%. The median marginal half-widths ranged from 1.97° to 4.08°. All fits converged under the registered score tolerance.

| Estimator at 98,304 inference shots | Worst face RMSE | Lowest face coverage | Joint chord coverage |
|---|---:|---:|---:|
| Four-phase Fourier | 25.93° | 88.0% | 90.6% |
| Eight-phase Fourier | 20.65° | 90.0% | 92.0% |
| Richardson | 125.84° | 54.5% | 15.3% |
| Exact-response likelihood, equal shots | 2.08° | 93.9% | 94.9% |
| Exact-response likelihood, Fisher allocation | 1.72° | 93.9% | 95.1% |

The equal-shot likelihood worst-face RMSE was 3.01° at 2,048 shots per setting and 1.52° at 8,192. Doubling the shared perturbation scales gave 2.03° worst-face RMSE and 92.0% joint chord coverage in the separate seeded stress test. These estimates are conditional on the calibrated Aer model and the registered local chart. [Training grid](receipts/live/time_grid.json) · [Monte Carlo results](receipts/live/statistics.json) · [Controls](receipts/live/controls.json)

The proposed workload uses equal shots and budgets another 98,304 shots for zero field, orientation reversal, a tree, a gauge copy, matched detuning, and balanced excitation. The modeled reset and acquisition schedule uses a 250 µs repetition delay. The estimated shot-weighted time is 50.27 seconds before the overhead and cap margin. The budget calculation is provisional and IBM has reported no Q3 usage.

The exact proposal's QPY SHA-256 is `ae9ee11b45b73c6f2ad0bac94d2796661b62f4301c342569e762944d041ea7c8`. Execution requires separate approval of the exact manifest and a new balance and calibration check. [Compiled circuits](receipts/live/q3_candidate_isa.qpy) · [Execution gate](HARDWARE_GATE.md)
