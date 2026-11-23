# Arithmetic Holonomy Rotor research sequence

AHR-01: two-prime quantum square, exact flux-sensitive return probability and entanglement formulas; IBM Quantum pilot instructions.

AHR-02: prime-exponent cocycles, the pi-flux Clifford cube, explicit two-prime spectrum, gauge-dependent entanglement cautions, primitive-loop graph zeta factors, and a finite SU(2) order-memory construction.

AHR-03: exact hypercube fourth-moment face theorem and an explicitly stable four-oscillator Hamiltonian whose degenerate normal modes carry noncommuting symplectic holonomy.

Each phase includes numerical checks and research notes. The approved AHR-QPU-01 two-qubit IBM pilot completed on 2026-11-23 with archived raw evidence at [`ibm_qpu_01/Q2_HARDWARE_RESULTS.md`](ibm_qpu_01/Q2_HARDWARE_RESULTS.md). Q3 remains simulation-only. The research sequence still has open Lean formalization tasks. The mathematics remains a research proposal with known connections to magnetic graph Hamiltonians, Clifford systems, and holonomic dynamics; priority and physical-computation claims remain open.

Recommended next steps:

1. Lean: prove the AHR-03 face-moment law on hypercube finite graphs, then the AHR-02 even characteristic polynomial.
2. Mechanics: evaluate the stable eigenstructure of the actual reduced Riemann-ellipsoid Hamiltonian and determine whether a separated multi-mode subspace exists over a controllable parameter loop.
3. IBM: analyze the completed Q2 signed-flux pilot, compile the Q3 six-face protocol against a fresh three-qubit calibration in simulation, and require separate approval for any Q3 submission.

Primary reading: `ahr01/AHR01_math_note.md`, `ahr02/AHR02_mathematics.md`, `ahr03/AHR03_symplectic_holonomy.md`.