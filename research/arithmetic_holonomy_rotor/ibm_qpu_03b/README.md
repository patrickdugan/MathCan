# AHR-QPU-03B/C follow-up preparation

Read [mathematical and experimental design](AHR03B_C_SPEC.md) and [routed SU(2) QPU-04 proposal](AHR_QPU_04_SPEC.md). The verifier consumes the immutable Q3 parent receipts and runs an independent paired-count diagnostic, a linearized intact-cube consistency diagnostic, a held-out isolated-face closure simulation, and the routed four-qubit non-Abelian oracle.

Run from the repository root:

```sh
python -m pip install numpy==2.3.5 scipy==1.17.0
python research/arithmetic_holonomy_rotor/ibm_qpu_03b/verify.py
```

The source is offline-only. It imports the parent mathematical functions, not the IBM client. No new QPU job is authorized. This PR is stacked on the exact Q3 hardware-evidence commit until #267 is merged; it does not replace the parent evidence.
