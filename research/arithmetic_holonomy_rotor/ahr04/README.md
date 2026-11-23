# AHR-04: Spectral rigidity and arithmetic curvature tomography

Follow-on to merged MathCan AHR-01 through AHR-03.

Contents:
- AHR04_spectral_rigidity_tomography.md: fourth/fifth magnetic trace formulas, spectral rigidity, curvature localization, exact phase-probe inversion, and research limits.
- ahr04_verify.py: independent seeded matrix oracle for random weighted hypercubes in dimensions 2–5.
- ahr04_validation.json: recorded local result from Python/NumPy/SciPy.

Run `python ahr04_verify.py` from this directory. The script rewrites the JSON receipt and fails on numerical inconsistency.

All checks passed locally. The theorems are presented with closed-walk proofs; Lean formalization and QPU measurements remain pending. The rotating-fluid realization still needs a derivation from the reduced Riemann-ellipsoid Hamiltonian.
