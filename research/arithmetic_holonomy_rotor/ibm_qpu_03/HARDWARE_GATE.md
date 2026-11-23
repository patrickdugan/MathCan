# IBM resource gate

**Execution decision: HOLD pending approval of the refreshed Q3 manifest.** The execution preflight verified **515 free Open Plan QPU seconds** at 23:19 Singapore time on 23 November 2026. IBM kept `ibm_kingston` and qubits `[67, 68, 69]` as the best-ranked layout. Its calibration timestamp advanced from 22:34:13 to 22:46:22. The approved manifest was bound to the earlier timestamp. No IBM Q3 job was submitted. [Refreshed calibration and allocation](receipts/execution_refresh/calibration.json) · [Refresh comparison](receipts/execution_refresh/refresh_evidence.json)

The approved and refreshed snapshots have identical native instruction, timing, and noise inputs on the selected triple. Recompilation confirmed the same cases, shots, readout maps, and probability predictions. The previous Monte Carlo remains applicable to this equivalent model. The new manifest binds the new calibration and requires separate approval. [Refreshed manifest](receipts/execution_refresh/q3_candidate_manifest.json) · [Underlying simulation](LIVE_CALIBRATION_RESULTS.md)

The manifest binds the exact case IDs, QPY digest, calibration digest, transpiler seed, ordered physical layout, per-case readout map, shot allocation, and estimated return probabilities. The cap adds the registered 20-second fixed overhead, a 1.5× margin, and a 60-second floor to the shot-weighted native critical path with IBM's repetition delay. These are engineering estimates. IBM Open Plan does not expose the server-side dry-run feature used for provider estimates on some other plans. [IBM workload usage](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/estimate-job-run-time) · [IBM dry-run eligibility](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/dry-run-jobs)

The historical FakeFez baseline and the earlier 515-second post-Q2 balance remain separate receipts. The read-only inventory verifies a uniquely selected free Open Plan instance. It ranks connected triples by native edge errors and durations, readout error, and prior calibration changes when available. The scope excludes paid plans, job submission, and credential logging.

```sh
python backend_snapshot.py --credential-file /path/to/approved-ibm-key.json --output live.json
python backend_snapshot.py --credential-file /path/to/approved-ibm-key.json --previous live.json --include-historical-drift --output recheck.json
python run_study.py --snapshot live.json --out reproduced/live
python refresh_proposal.py --prior receipts/live --snapshot recheck.json --output reproduced/refresh
```

Any later execution requires explicit approval of the exact manifest, a new check of the account balance and calibration against that manifest, and capacity at least equal to its cap. A changed layout or calibration requires recompilation and a new approval.
