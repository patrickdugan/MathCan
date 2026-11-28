# AHR-QPU-01 hardware Q2 archive (23 November 2026)

This is the **actual QPU observation** from IBM job `dc1vksqnj2vs73dfu0n0` on `ibm_fez` physical qubits 9 and 10. It is distinct from AHR-QPU-01's previously merged simulator and the later AHR-QPU-02 historical fake-backend study.

The approved 36-circuit Q2 pilot returned 2,048 shots each (73,728 total). Forward and reversed signed phase estimates were +38.90° and −42.86° for programmed values ±41.83°. The tree control's joint confidence interval includes zero. The prespecified primary complex-harmonic acceptance check passed at t=1.6. IBM charged 21 free QPU seconds, and the account reported 515 remaining at the conclusion.

Original evidence source: [MathCan PR #254](https://github.com/patrickdugan/MathCan/pull/254), commit [981b07b6d555b268ce0f28add39176bf3f39beb4](https://github.com/patrickdugan/MathCan/commit/981b07b6d555b268ce0f28add39176bf3f39beb4).

The old PR predates the merged simulator PR #255 and conflicts with newer files on main. This archive transfers the original evidence as byte-identical Git blobs and preserves the current simulator code.

## Local audit

```sh
python research/arithmetic_holonomy_rotor/ibm_qpu_01/hardware_q2_replay.py
```

This stdlib replay verifies the complete shot count and 36 case identifiers, both signed phases, the primary harmonic, tree magnitude, IBM allocation arithmetic, the original calibrated QPY and text-normalized calibration SHA256, execution ordering, and the archived acceptance indicators. The replay requires **no IBM credentials** and **never submits jobs**.

The full prespecified uncertainty procedure, its Qiskit version dependencies, and the original hardware capture remain reviewable at the pinned source commit. CI validates the archived data consistency. The 95% intervals reproduced in Q2_HARDWARE_RESULTS.md are sourced from that original analysis, rather than independently reestimated in this compact replay.

The mathematical interpretation is finite-dimensional U(1) magnetic-flux interferometry. It establishes a real-hardware response and signed orientation under tested controls. Quantum computational advantage, the Riemann hypothesis, and consciousness remain separate questions. Q3 has received **simulation only**; any Q3 hardware test requires a separate protocol and authorization.
