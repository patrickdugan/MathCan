# AHR-QPU-01 · Approved Q2 results

IBM job **dc1vksqnj2vs73dfu0n0** completed on **ibm_fez**, running 36 circuits with 2,048 shots each for **73,728 returned shots**. The physical mapping was $x\mapsto9$ and $y\mapsto10$.

The approval covered this Q2 workload on Open Plan. The available balance was 536 s before submission against a 98 s cap. IBM reported **21 s** of QPU use, with **515 s** remaining after collection.

## Primary result

The predeclared complex-harmonic criterion at $t=1.6$ **passed**. The measured $Z_4$ was -0.15430-0.19873i, compared with -0.15494-0.20311i from the exact model and -0.15276-0.20014i from calibrated Aer. The measured zero-outcome counts were 175, 948, 807, 134 in the fixed phase order $0,\pi/2,\pi,3\pi/2$.

| Component | Exact | Measured | Joint 95% counting interval | Interval with systematic allowance |
| --- | ---: | ---: | --- | --- |
| Real | -0.15494 | -0.15430 | [-0.17538, -0.13252] | [-0.18056, -0.12734] |
| Imag | -0.20311 | -0.19873 | [-0.21910, -0.17747] | [-0.22508, -0.17149] |

The directed phase estimates use the independently measured zero-target reference at the same time. The positive and reversed fixtures at the primary time recover their programmed signs. The intervals are conservative 95% circular bounds for each estimate.

| Signal arm | Programmed relative phase | Recovered relative phase | 95% interval |
| --- | ---: | ---: | --- |
| Forward at 0.8 | +41.83° | +41.38° | Unresolved at 95% |
| Forward at 1.2 | +41.83° | +63.25° | [-2.65°, +129.14°] |
| Forward at 1.6 | +41.83° | +38.90° | [+23.43°, +54.38°] |
| Reversed at 1.6 | −41.83° | -42.86° | [-58.46°, -27.26°] |

The tree control gave $Z_4=0.00317-0.00806i$. Its joint counting rectangle contains the origin. The matched-detuning control gave $Z_4=-0.16528-0.21558i$, compared with the exact prediction -0.17193-0.22543i. That control reports the harmonic directly because its diagonal differs from the phase-reference arm.

## Calibration and evidence

Fresh calibration was recorded at 2026-11-23 16:03:41 SGT. IBM reported that calibration at job start and at the last execution chunk. The runtime returned matching case identifiers for all 36 circuits in 1 chunk. The refreshed calibration selected exact synthesis under the original gates. Q3 remains simulation-only.

The portable calibration hash normalizes text line endings. The hardware manifest preserves the raw calibration hash verified before submission and the unchanged binary QPY hash.

- [Raw IBM counts](receipts/hardware_q2/hardware_counts.json) · [Execution evidence](receipts/hardware_q2/execution_evidence.json)
- [Phase estimates and intervals](receipts/hardware_q2/hardware_analysis.json) · [Matching Q2 simulations](receipts/hardware_q2/q2_protocol.json)
- [Fresh calibration](receipts/hardware_q2/calibration.json) · [Manifest](receipts/hardware_q2/manifest.json) · [ISA QPY](receipts/hardware_q2/q2_isa.qpy)
