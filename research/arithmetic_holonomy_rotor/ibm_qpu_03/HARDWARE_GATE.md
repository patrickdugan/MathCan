# IBM resource gate

**The authorized Q3 pilot completed. Further QPU execution is on HOLD.** IBM job `dc25sdmq4uuc73a4pbl0` ran the 48 approved circuits at 4,096 shots each on `ibm_kingston`, qubits 67, 68, and 69. The job used 54 free seconds under its 106-second cap, leaving 461 Open Plan seconds when checked. [Hardware results](Q3_HARDWARE_RESULTS.md) · [Job receipt](receipts/hardware/hardware_job.json) · [Post-run allocation](receipts/hardware/post_run_allocation.json)

The original execution preflights held the job when IBM advanced the calibration timestamp. The user then explicitly approved a timestamp-only change for this byte-identical QPY under the same physical model and budget. Immediately before submission, the live target, compact noise, layout, and budget checks matched that authorization. The execution receipt records the selected calibration at submission. [Approved manifest](receipts/execution_refresh/q3_candidate_manifest.json) · [Final preflight](receipts/hardware/preflight.json) · [Underlying simulation](LIVE_CALIBRATION_RESULTS.md)

The manifest binds the exact case IDs, QPY digest, calibration digest, transpiler seed, ordered physical layout, per-case readout map, shot allocation, and estimated return probabilities. The cap adds the registered 20-second fixed overhead, a 1.5× margin, and a 60-second floor to the shot-weighted native critical path with IBM's repetition delay. These are engineering estimates. IBM Open Plan does not expose the server-side dry-run feature used for provider estimates on some other plans. [IBM workload usage](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/estimate-job-run-time) · [IBM dry-run eligibility](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/dry-run-jobs)

The historical FakeFez baseline and the earlier 515-second post-Q2 balance remain separate receipts. The read-only inventory verifies a uniquely selected free Open Plan instance. It ranks connected triples by native edge errors and durations, readout error, and prior calibration changes when available. The scope excludes paid plans, job submission, and credential logging.

```sh
python backend_snapshot.py --credential-file /path/to/approved-ibm-key.json --output live.json
python backend_snapshot.py --credential-file /path/to/approved-ibm-key.json --previous live.json --include-historical-drift --output recheck.json
python run_study.py --snapshot live.json --out reproduced/live
python refresh_proposal.py --prior receipts/live --snapshot recheck.json --output reproduced/refresh
```

Any later execution requires separate approval, a current balance and calibration check against its manifest, and capacity at least equal to its cap. The timestamp-only approval applied to the completed job. The launcher requires an explicit command and manifest digest. [Execution source](hardware_execution.py)
