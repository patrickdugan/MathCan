# AHR-QPU-02: fake-backend compilation and noise gate

**Research status: OFFLINE SNAPSHOT. QPU submission: HOLD.**

This package follows AHR-QPU-01. The default mode compiles to a historical five-qubit `FakeManilaV2` snapshot and runs a noisy Aer simulation. It makes no IBM network calls, incurs no RU expenditure, and does not imply an accessible live backend. Qiskit files are installed only in the GitHub CI job or on an authorized workstation.

From `research/arithmetic_holonomy_rotor/ibm_qpu_02/`:

```sh
python -m pip install -r ../ibm_qpu_01/requirements-qiskit.txt
python -m pytest -q tests/test_backend_gate.py
python backend_gate.py --mode fake --shots 2048 --output receipts/fake_backend_report.json
```

The gate ranks calibrated directed pairs using two-qubit gate and readout error, compiles exact-unitary and Suzuki-Trotter implementations, and selects a method by the mapped two-qubit count among circuits with noiseless return-probability error below 0.015. The JSON receipt includes selected qubits, dated snapshot, native gate counts, circuit depth, phase error, confidence interval, and broken-cycle control.

A four-phase target scan at phase 0.73 rad uses 4 × 2,048 shots. An additional zero-phase reference and broken-cycle control bring the full prespecified pilot to **12 circuits, 24,576 shots**. Additional calibration or repetition costs require separate accounting. Charges depend on backend runtime/RUs, not raw shot count alone.

A paired zero-reference scan allows a complex quadrature ratio to be formed; the bootstrap estimates sampling variability conditional on the calibrated fake noise model. The QPU may have different phase-dependent bias. The snapshot represents historical device properties, not current backend calibration.

## Optional read-only backend inventory

When the IBM Open Plan instance and credential are configured on a user's workstation, obtain current operational backend names, candidate pairs, and calibration dates with:

```sh
python backend_gate.py --mode read-only-inventory \
  --instance "<verified Open Plan instance>" --authorize-cloud \
  --output receipts/local_backend_inventory.json
```

This command uses QiskitRuntimeService for **metadata only** and constructs no Sampler. The receipt does not contain the instance CRN or credential. The operator must confirm the instance's actual plan type and remaining allocation in the IBM Quantum Platform dashboard. The previous Windows credential at `C:\Users\patri\.qiskit\qiskit-ibm.json` was reported to contain `{}`; this code cannot inspect that Windows path from the current environment.

IBM Open Plan grants an RU equivalent of up to 10 minutes per rolling 28-day window, with eligibility and available allocation determined by the user's account. Server-side dry-run access is restricted and should not be assumed for an Open Plan instance.

**The experiment remains HOLD until current backend metadata, account allocation, and final job-budget approval have been verified.** No new live IBM job is authorized by merging these files.

References: [IBM plans](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-platform/plans-overview), [backend inventory](https://quantum.cloud.ibm.com/docs/en/ibm-quantum-compute/qpu-information), [fake backend specification](https://quantum.cloud.ibm.com/docs/en/api/qiskit-ibm-runtime/fake-provider-fake-manila-v2).
