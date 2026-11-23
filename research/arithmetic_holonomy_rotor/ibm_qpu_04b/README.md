# AHR-QPU-04B

Offline follow-up to the archived Q4 Kingston hardware experiment on the routed-memory branch. See [mathematical specification and design](AHR_QPU_04B_SPEC.md).

Run from the repository root:

```sh
python research/arithmetic_holonomy_rotor/ibm_qpu_04b/verify.py --output /tmp/ahr04b.json
python -m pip install -r research/arithmetic_holonomy_rotor/ibm_qpu_04/requirements.txt
python research/arithmetic_holonomy_rotor/ibm_qpu_04b/qpy_audit.py --output /tmp/ahr04b-qpy.json
```

The first command is standard-library-only. The second verifier uses the original pinned Qiskit version and checks the archived 76-circuit QPY and first-loop factorization. The generated design ledger is a proposed set of cases, not compiled circuits and not execution approval. No module contacts IBM or submits a workload. Preserve the hardware parent artifacts unchanged. New hardware remains HOLD.
