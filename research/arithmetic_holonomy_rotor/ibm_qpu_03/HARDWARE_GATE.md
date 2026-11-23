# IBM resource gate

**Execution decision: HOLD.** The Q3 manifest is a simulation artifact from a historical FakeFez target. Q3 has no submission code and no IBM job was submitted. The previous Q2 account evidence was 515 free QPU seconds after IBM job `dc1vksqnj2vs73dfu0n0`. That figure is historical.

The read-only lookup could not authenticate with the authorized credential source. The account's present allocation, accessible physical triple, and current device drift remain unverified. The bundle includes a read-only command to collect the live metadata required for a new manifest.

```sh
python backend_snapshot.py --credential-file /path/to/approved-qiskit-ibm.json --output live.json
python run_study.py --snapshot live.json --out refreshed
```

The read-only command verifies a uniquely selected free Open Plan instance, records sanitized timing and calibration metadata, and never calls a primitive or submits a job. An optional `--previous` snapshot adds an observed two-qubit calibration change on matching edges to the ranking. It records the best extension of physical qubits 9 and 10 when that pair is present. The archived FakeFez snapshot has no contemporaneous drift comparison. Its ranking uses errors, durations and readout from a single timestamp, with the covariance stress study covering a separately assumed drift model.

The manifest binds the exact case IDs, QPY digest, calibration digest, transpiler seed, ordered physical layout, per-case readout map and return predictions. It reports the shot-weighted native critical path plus the backend repetition delay. The provisional cap adds the registered 20 s fixed overhead, a 1.5× timing margin, and a 60 s floor. These are engineering estimates. IBM Open Plan does not expose the server-side dry-run feature used for provider estimates on some other plans. No paid instance or paid fallback is in scope. [IBM workload usage](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/estimate-job-run-time) · [IBM dry-run eligibility](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/dry-run-jobs)

A later execution decision requires the exact manifest regenerated on a current free instance, passing the accuracy and coverage gates, capacity at least equal to its cap, and explicit authorization of that manifest. Any material calibration or layout change requires recompilation and a new manifest. The live allocation must be checked immediately before any authorized submission.
