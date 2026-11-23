# IBM QPU authorization gate

**Decision: HOLD for cloud submission.**

This agent run performed no IBM API calls or QPU submissions. The execution environment lacked a Qiskit installation and a visible IBM credential. Installed environment used Python 3.13, NumPy 2.3.5 and SciPy 1.17.0, so the Qiskit-specific synthesis checks must execute in CI or on a configured workstation. The Windows local path is not mounted here. Never log the credential, account metadata or token.

## Before moving HOLD to GO

1. Confirm Qiskit 2.6+, Qiskit Aer 0.17+, qiskit-ibm-runtime 0.52+ with actual installed version receipts. The client-side `Sampler` interface is default since runtime 0.52.0; inspect live signatures before calls.
2. Pass all independent matrix/unitarity/phase-sign tests and Qiskit statevector comparisons for all four offsets. Verify compiled ISA qubit layout, gate counts, and return-probability errors within 0.015 in a noiseless local simulator.
3. Use an actual connected IBM physical-qubit pair, record its backend name and current calibration properties. Run a noise-model (AerSimulator.from_backend) simulation with a fixed compiled circuit at matched total shot budgets. No connected backend is available in this environment.
4. Perform gate-depth and shot-cost accounting. Prespecified pilot: 4 phase settings x 2,048 shots = **8,192 shots**, plus controls and calibration settings that must be individually budgeted. For Q3: 6 faces x 4 phases x 2,048 shots = **49,152 shots** before controls; two-time Richardson doubles the number of settings.
5. Verify that the selected instance is Open/Free Plan and the backend is covered by remaining free allocation. The operator must inspect actual account entitlements; backend runtime/charge cannot be inferred from raw shot counts.
6. Obtain explicit QPU job approval for an exact list of circuits and a stated resource budget. `--authorize-qpu --instance OPEN_PLAN_CRN` plus `AHR_QPU_ALLOW_LIVE_SUBMISSION=YES` are both required at run time. A separate `AHR_QPU_FREE_PLAN_VERIFIED=YES` guard requires the operator to confirm free plan. No paid fallback.
7. Confirm no existing GPU tasks or live hardware sessions will be disrupted. Use job mode, not session mode, for Open Plan.

## Out-of-scope evidence

The offline 2% readout-flip and 5% depolarization experiments are illustrative analytic channels, with no measured IBM backend calibration. They cannot support a hardware GO recommendation. This project has not executed a paid service, hardware experiment or IBM credential lookup.

## Sources

- IBM Runtime 0.52.0 release notes (2026-11-09): https://quantum.cloud.ibm.com/docs/en/api/qiskit-ibm-runtime/release-notes
- Current SamplerV2 job-mode interface: https://quantum.cloud.ibm.com/docs/en/api/qiskit-ibm-runtime/sampler-v2
- IBM Quantum Open Plan session restriction: https://quantum.cloud.ibm.com/docs/en/guides/run-jobs-session
