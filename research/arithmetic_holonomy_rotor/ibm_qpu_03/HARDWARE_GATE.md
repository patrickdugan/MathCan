# IBM resource gate

**Execution decision: HOLD pending approval of the exact Q3 manifest.** The read-only follow-up verified **515 free Open Plan QPU seconds** at 22:47 and again at 22:50 Singapore time on 23 November 2026. The selected target was `ibm_kingston` on qubits `[67, 68, 69]`. The selected calibration, timestamped 22:34:13 Singapore time, produced identical native target and noise inputs in both reads. No IBM Q3 job was submitted. [Calibration and allocation evidence](receipts/live/calibration_recheck.json) · [Live-calibration results](LIVE_CALIBRATION_RESULTS.md)

The approved scope for this follow-up was account and calibration metadata. The proposed manifest binds the exact case IDs, QPY digest, calibration digest, transpiler seed, ordered physical layout, per-case readout map, shot allocation, and estimated return probabilities. The cap adds the registered 20-second fixed overhead, a 1.5× margin, and a 60-second floor to the shot-weighted native critical path with IBM's repetition delay. These are engineering estimates. IBM Open Plan does not expose the server-side dry-run feature used for provider estimates on some other plans. [Exact proposed manifest](receipts/live/q3_candidate_manifest.json) · [IBM workload usage](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/estimate-job-run-time) · [IBM dry-run eligibility](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/dry-run-jobs)

The historical FakeFez baseline and the earlier 515-second post-Q2 balance remain separate receipts. The read-only inventory verifies a uniquely selected free Open Plan instance. It ranks connected triples by native edge errors and durations, readout error, and prior calibration changes when available. The scope excludes paid plans, job submission, and credential logging.

```sh
python backend_snapshot.py --credential-file /path/to/approved-ibm-key.json --output live.json
python backend_snapshot.py --credential-file /path/to/approved-ibm-key.json --previous live.json --include-historical-drift --output recheck.json
python run_study.py --snapshot live.json --out reproduced/live
```

Any later execution requires explicit approval of the exact manifest, a new check of the account balance and calibration against that manifest, and capacity at least equal to its cap. A changed layout or calibration requires recompilation and a new approval.
