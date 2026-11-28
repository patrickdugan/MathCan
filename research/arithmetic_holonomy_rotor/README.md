# Arithmetic Holonomy Rotor research sequence

AHR-01: two-prime quantum square, exact flux-sensitive return probability and entanglement formulas; IBM Quantum pilot instructions.

AHR-02: prime-exponent cocycles, the pi-flux Clifford cube, explicit two-prime spectrum, gauge-dependent entanglement cautions, primitive-loop graph zeta factors, and a finite SU(2) order-memory construction.

AHR-03: exact hypercube fourth-moment face theorem and an explicitly stable four-oscillator Hamiltonian whose degenerate normal modes carry noncommuting symplectic holonomy.

Each phase includes a local NumPy/SciPy verifier, machine-readable numerical receipt, and research note. Run verifiers in their respective subdirectories. No QPU jobs have been submitted and no Lean kernel proofs have been checked for this sequence. The mathematics remains a research proposal with known connections to magnetic graph Hamiltonians, Clifford systems, and holonomic dynamics; priority and physical-computation claims remain open.

Recommended next steps:

1. Lean: prove the AHR-03 face-moment law on hypercube finite graphs, then the AHR-02 even characteristic polynomial.
2. Mechanics: evaluate the stable eigenstructure of the actual reduced Riemann-ellipsoid Hamiltonian and determine whether a separated multi-mode subspace exists over a controllable parameter loop.
3. IBM: run the AHR-01 flux vs zero-flux vs broken-loop controls under a strict resource gate; use AHR-03 for a separate modal-order test only after state-preparation and readout design.

Primary reading: `ahr01/AHR01_math_note.md`, `ahr02/AHR02_mathematics.md`, `ahr03/AHR03_symplectic_holonomy.md`.