# AHR-QPU-03 IBM hardware results

IBM job `dc25sdmq4uuc73a4pbl0` completed on `ibm_kingston`, physical qubits 67, 68, and 69, on 23 November 2026 Singapore time. IBM returned every one of the 48 approved circuits at 4,096 shots per circuit, for 196,608 shots. The provider reported 54 free QPU seconds of usage under the 106-second cap. The verified allocation went from 515 to 461 seconds. IBM's returned PUB metadata matched all 48 case IDs in order. [Job and count receipts](receipts/hardware/) · [Approved circuit manifest](receipts/execution_refresh/q3_candidate_manifest.json)

The authorized timestamp-only refresh retained the byte-identical approved QPY, physical layout, readout maps, and calibrated model at the submission check. The approved manifest named the 22:46:22 calibration, and the matched live model at submission was timestamped 23:20:48. The separate calibration timestamps IBM returned for the job's start and completion are discussed below. [Preflight receipt](receipts/hardware/preflight.json) · [Timestamp refresh comparison](receipts/hardware/timestamp_refresh.json)

## Measured phase recovery

The frozen exact-response likelihood converged at $t=2.0$. The six estimated faces have the correct programmed signs. The maximum absolute face error was 6.62° and the programmed five-chord field fell outside the model's local joint 95% region. The joint score was 29.75 versus the 95% reference value 11.07 for five dimensions.

| Face | Programmed angle | QPU fit | Local 95% half-width |
|---|---:|---:|---:|
| xy, z=0 | −18.33° | −21.09° | 2.64° |
| xy, z=1 | −84.80° | −86.61° | 1.89° |
| xz, y=0 | +20.63° | +24.08° | 2.91° |
| xz, y=1 | −12.03° | −14.51° | 3.46° |
| yz, x=0 | −16.04° | −9.42° | 4.39° |
| yz, x=1 | +17.76° | +17.49° | 3.33° |

In AHR-09 order, the fitted chord angles were 21.09°, −24.08°, 9.42°, −17.49°, and 35.60°. The fitted Bianchi residual is zero by construction of the five-chord model. Independent hardware closure remains unmeasured at this operating point. The local intervals use the frozen model's Fisher covariance, including its shared nuisance terms. [Hardware replay and uncertainty](receipts/hardware/hardware_analysis.json) · [Frozen simulator statistics](receipts/live/statistics.json)

## Controls and return probabilities

The tree control gave $Z_4=0.00330-0.00598i$. Its simultaneous binomial counting rectangle was [−0.01282, 0.01940] for the real part and [−0.02171, 0.00977] for the imaginary part, containing the origin. The four gauge-copy minus target return differences were +0.01685, −0.01587, −0.00244, and +0.01172. These are raw paired-setting contrasts. The controls and per-case probability intervals are in the replay receipt.

For the 24 target settings, the hardware return RMSE was 0.01707 against the exact matrix, 0.01707 against noiseless compilation, and 0.01298 against calibrated Aer. The largest probability discrepancy with calibrated Aer was 0.02967. These discrepancies motivate caution in interpreting the simulated coverage as hardware coverage. [Case-level observations](receipts/hardware/hardware_analysis.json)

## Execution calibration

IBM identified the job-start calibration as 23:20:48, matching the submission snapshot. Its historical lookup at the reported completion time returned 23:28:44. All 109 selected gate and qubit property values agreed across those two snapshots. The result did not expose execution spans, so this checks the job endpoints. [Execution metadata](receipts/hardware/execution_evidence.json) · [Property comparison](receipts/hardware/boundary_calibration.json)

## Reproduce the hardware analysis

```sh
python hardware_analysis.py --manifest receipts/execution_refresh/q3_candidate_manifest.json --statistics receipts/live/statistics.json --hardware receipts/hardware --output reproduced/hardware_analysis.json
```

This is one finite-dimensional hardware pilot. It demonstrates signed phase recovery at the point-estimate level and exposes a joint precision shortfall on the current calibration model.
