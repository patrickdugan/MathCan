# AHR-QPU-01 · Hardware gate

**The approved Q2 pilot completed.** IBM job dc1vksqnj2vs73dfu0n0 executed 36 circuits at 2,048 shots per setting. It used 21 Open Plan seconds and left 515 seconds in the account. A further QPU job requires its own explicit authorization and a fresh resource check. Q3 remains simulation-only. [Q2 hardware results](Q2_HARDWARE_RESULTS.md)

## Original planning snapshot

The read-only IBM check on 23 November 2026 at 14:21 Singapore time returned **536 free QPU seconds**. It found an operational **ibm_fez** backend and an adjacent CZ pair with **$x\mapsto9$ and $y\mapsto10$**. The recorded backend calibration was from 13:57:23 Singapore time. The saved Qiskit account file was empty. Authentication succeeded through the SDK token-file path with an existing IBM Cloud credential. The receipts contain no account identifier or credential value.

| Plan | Settings | Shots per setting | Total shots | Gates, measurement and delay allowance | Free time reserved |
| --- | ---: | ---: | ---: | ---: | ---: |
| Initial Q2 | 36 | 2,048 | 73,728 | 37.14 s | **98 s** |
| Higher-shot Q2 | 36 | 8,192 | 294,912 | 148.56 s | **209 s** |

The resource model sums calibrated native instruction durations, adds 500 μs per shot for reset and delays, and adds a 60 s job-level reserve. It estimates usage rather than queue time. The Q2 circuit manifest, compact target and physical QPY share a checked order and calibration. The code uses Qiskit 2.6.2, Aer 0.18.4, and the client-side IBM Runtime 0.52.1 SamplerV2. [IBM work usage](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/estimate-job-run-time)

After explicit approval for a new run, refresh the calibration and rerun simulation if the live snapshot has changed. Submit only to an existing verified Open Plan instance. The submit command rechecks the free balance, calibration and file digests. It writes a unique job checkpoint before requesting execution and caps QPU time at the reserved amount. If a submission outcome is ambiguous, use the checkpoint tag through the collect command instead of resubmitting.

~~~shell
python experiment.py submit --out runs/current --shots 2048 --confirm-free-qpu --token-file PATH_TO_KEY
python experiment.py collect --out runs/current --token-file PATH_TO_KEY
~~~

The primary hardware decision compares both components of the measured $Z_4$ with the exact target using a simultaneous 95% counting rectangle expanded by the precomputed component-specific systematic allowances. Phase direction, the reference and the tree contrast are reported separately. A fresh calibration check must pass even if the original quota remains available.

## Q3 budget · simulation only

At 2,048 shots per setting the shared single-time schedule uses 23 measured circuits and 47,104 shots. The two-time Richardson schedule uses 46 measured circuits and 94,208 shots. With an assumed 520 μs per shot and a 60 s reserve, the nominal usage estimates are 84.5 s and 109.0 s. These are planning values without a Q3 device calibration.

At $t=0.4$, a 10° phase standard-deviation target needs about **1.73 million shots per face** even under the leading-order conditional Fisher model. Six such estimates budget about **5,461 s** under the timing assumption. The 2,048-shot simulations give around 88° phase RMSE at a single time and 102° for equal-shot Richardson extrapolation. Keep Q3 hardware deferred. The compatibility projection helps local stochastic phase errors after the angle branch can be resolved.
