# Analytic approximation bridge

This isolated Lean 4.32.0-rc1 project adds the pinned Mathlib dependency at
360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56. The main MathCan toolchain remains
Lean 4.35.0. No Mathlib dependency is added to the main MathCan package.

`ApproximationMathlib.TaylorFoundation` is an attributed, namespaced subset
of the pinned Mathlib Taylor module. It keeps the finite polynomial, derivative,
mean-value, and Lagrange proofs and avoids the unrelated interval-integral imports.
Its 12 theorem roots are upstream proofs, not new authored mathematics. See
UPSTREAM_PROVENANCE.json and LICENSE.mathlib.

`SmoothTaylor` derives integer and fractional remainder bounds from actual
ContDiffOn/within-interval derivative hypotheses, including coincident endpoints.
It also proves a normalized correction bound under mu^s <= 2*tau.

`CapturedApproximation` identifies the core Horner polynomial with the analytic
Taylor polynomial, proves coefficient perturbation estimates, and connects them
to the common-bound Hamming/sentinel/spatial capture circuit. Its uniform scalar
bound is H*rho^s/k! + J*epsilon on cells with radius rho<=1.

The multivariate continuation constructs fixed-anchor coefficients directly from
Frechet derivative tensors (`MultivariateTaylor`), proves their norm and
perturbation bounds (`MultivariateBounds`) and integer/Holder remainders
(`MultivariateBounds`, `MultivariateHolder`). `JetSynthesis` and `FrameSynthesis`
construct rounded/clipped correction frames and prove uniform tau/2 accuracy.
`SynthesisCapture` connects these frames to the existing decoded spatial capture.
`MultivariateCapture` proves the resulting coefficient accuracy and the final
smooth/Holder approximation bounds without an assumed accuracy contract.

The subsequent `SharpTransport` and `WordTransport` modules prove a uniform
correction alphabet and general ordered-word matrix compatibility. The current
`CubeApproximation` module proves intrinsic closed-cube Taylor regularity,
clipped-anchor serpentine coverage and the actual decoded spatial approximation.
Its 58 new roots bring the verified campaign to 374 research roots. For k>=1
the safe-phase error is H*(D*mu)^(k+alpha)/k! + J*D^k*tau/2. A global smooth
extension, a compatibility oracle and an assumed anchor-distance bound are not
premises. Safe-phase aggregation, approximate multiplication and the dense
quantized ReLU resource compiler remain open. See
[CUBE_APPROXIMATION_REPORT.md](../oxilean_v015/CUBE_APPROXIMATION_REPORT.md).
For the current frozen replay, restore the cube helpers into CAMPAIGN_WORK and
follow that report; the analytic helpers below describe the earlier scalar run.

The standard Lake project pins Mathlib by exact Git revision and requires the
parent MathCan package by path. For the space-constrained local replay, use the
workspace helpers in research/oxilean_v015 after restoring them into CAMPAIGN_WORK:
check_analytic432.sh and run_analytic_replay432.sh. The dependency receipts record
source Git blobs, package revisions and retained artifact SHA-256 values. The
local cache omits regenerable C and editor-index files and compresses the retained
proof/interpreter artifacts; no proof file or cache hash rule is changed.
