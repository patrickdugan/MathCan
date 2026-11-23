# AHR-QPU-03: three-prime curvature tomography

The experiment recovers static U(1) face phases on the three-qubit arithmetic cube, then reconstructs the five chord phases in the AHR-09 spanning-tree gauge. The archive includes measured AHR-QPU-01 Q2 counts, a historical Q3 simulation, and a Q3 simulation compiled using IBM calibration metadata obtained through a read-only account check. The Q3 package has no job submission entry point.

- [Mathematical specification](Q3_MATHEMATICAL_SPEC.md)
- [Results and decision](RESULTS.md)
- [IBM resource and execution gate](HARDWARE_GATE.md)
- [Simulation and provenance receipts](receipts/)
- [Live-calibration simulation](LIVE_CALIBRATION_RESULTS.md)
- [Refreshed circuit manifest for IBM approval](receipts/execution_refresh/q3_candidate_manifest.json)
- [Original live-calibration manifest](receipts/live/q3_candidate_manifest.json)
- [Historical FakeFez circuit manifest](receipts/q3_candidate_manifest.json)

## Reproduce

Use Python 3.12 in an isolated environment. Run these commands from this directory.

```sh
python -m pip install -r requirements.txt
python -m pytest -q
python run_study.py --snapshot receipts/calibration.json --out reproduced
python run_study.py --snapshot receipts/live/calibration.json --out reproduced/live
```

The last command runs the full calibration-snapshot study with 1,000 evaluation replicates per design, shot level, or allocation. Use `--quick` for the CI smoke check. Use `--grid-cache /path/to/cache.json` to reuse a matching training sweep. A cache is bound to the selected method and snapshot. The program without `--snapshot` uses IBM's packaged FakeFez calibration. Building the default model and regenerating the receipts needs no IBM account.

The Q2 audit delegates the immutable count and checksum checks to the merged baseline verifier. It then opens the original QPY and checks the physical ISA and measurement map of each circuit, recomputes the primary exact quadrature, and independently checks its archived acceptance inequalities. The Q3 spectral solver is checked against direct matrix exponentiation, and the Hamiltonian is checked against the latest merged QPU-01 simulator with the conjugated edge convention. The AHR-08 selectors and AHR-09 face ordering and chord gauge are preserved.

## Study protocol

- Register a coarse grid from 0.1 to 2.0 in 0.1 increments. Refine around the two training Fourier minima and the maximum of the weakest face's first harmonic in increments of 0.025. Treat $t=0.12$ as a separate asymptotic reference.
- Select a Fourier time by the worst calibrated training bias-plus-variance proxy. For Richardson, pair the four-phase time with $t/\sqrt 2$. Select the likelihood time by the smallest eigenvalue of the nominal five-chord exact-response Fisher matrix. The final Monte Carlo compares all estimators under the calibrated Aer response. Training-time selection precedes construction of the seeded held-out fields and counts.
- Use three shot levels per setting and an equal-total comparison at 98,304 shots. Include independent references in the Fourier costs. The shared reference uses the real-field symmetry $P(\delta)=P(-\delta)$ and reuses zero-offset rows with identical initial states. Aer can break that circuit-level equivalence. Record the mismatch and propagate covariance from reuse.
- Choose the lowest total native two-qubit gate count among methods with maximum ideal return error at most 0.015, maximum two-qubit count at most 160, and maximum critical-path duration at most 150 µs on the registered 72-setting synthesis benchmark. Also apply those limits to every control arm of the manifest.
- Treat the four calibration perturbations as common across all settings in a trial. Their registered one-sigma scales are a 0.01 readout-contrast perturbation, a 0.025 rad coherent offset, a 0.012 contrast drift with time dependence, and a 0.015 fractional coupling error. These are stress assumptions conditional on a dated model. Report a doubled-perturbation stress case. One shared draw drives all corresponding returns, including cross-face and target/reference covariance.
- Fit a per-setting affine Aer transfer on five public fields, including zero. Penalized exact binomial likelihood uses this transfer, the five-chord Hamiltonian response, and shared nuisance directions. The fit starts within a public local chart around the commanded field. The independent held-out fields perturb each chord by up to 0.19 rad. Calibration residual directions enter the likelihood covariance. Report empirical coverage on the held-out Aer cases rather than treating model covariance as verified coverage.
- The proposed pilot uses the likelihood candidate and interleaves first-face controls with six-face target settings. Simulated GO requires worst-face angular RMSE at most 12°, at least 90% marginal and 90% joint coverage at nominal 95%, at least 98% scored likelihood convergence, passing circuit limits, a verified live calibration, and sufficient current free time. Separate approval of the exact regenerated manifest is required for execution.

The likelihood intervals use local Fisher curvature. Fourier intervals use the delta method at smoothed observed probabilities, including the Bianchi projection. Low-amplitude scans or a wide uncertainty region near a phase seam can invalidate these approximations. The receipts record empirical coverage and independent Gaussian wrapping stress tests.

## Future conditional experiment

AHR-QPU-04 would add an internal two-level degree of freedom and program two SU(2) loops $A$ and $B$. Compare equal-duration sequences $U_BU_A$ and $U_AU_B$ under blinded order labels, with identity and commuting controls, reversed loops, and a matched detuning and depth budget. Estimate operational order-memory fidelity on held-out labels, verify a nontrivial group commutator $U_AU_BU_A^{-1}U_B^{-1}$ with Wilson-loop or process measurements, and report sensitivity to decoherence and readout drift. This proposal is contingent on demonstrating calibrated Q3 phase recovery on hardware.
