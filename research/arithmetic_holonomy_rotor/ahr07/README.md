# AHR-07: Four-phase holonomy tomography

The AHR-07A reduction replaces exhaustive on/off marked-edge parity sums with four intact-graph phase settings **when the probed cycle is isolated**. The proof follows from diagonal gauge removal on forests, and the Fourier estimator suppresses second-harmonic aliasing.

Start with AHR07_four_phase_holonomy_tomography.md. Run python ahr07_ci.py using NumPy and SciPy to obtain the reproducible validation JSON. The script performs exact matrix simulations and seeded binomial shot simulations of the two-prime square, a three-prime hexagon with attached tree leaves, and a planted chord confounder.

Current status: mathematical note and local numerical checks, no Lean kernel proofs of the new statements, no QPU execution. Full research materials are available in the accompanying conversation artifact.