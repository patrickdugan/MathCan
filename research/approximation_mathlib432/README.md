# Scalar analytic approximation bridge

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

Coefficient accuracy of the concrete reference recurrence is an explicit
hypothesis of the capture-to-approximation results. The analytic identities
between multivariate derivative jets and the transport matrices, the synthesis
of all correction words from those jets, and the dense ReLU arithmetic/resource
compiler are separate remaining obligations. These files do not claim the full
multivariate approximation rate in network parameter count.

The standard Lake project pins Mathlib by exact Git revision and requires the
parent MathCan package by path. For the space-constrained local replay, use the
workspace helpers in research/oxilean_v015 after restoring them into CAMPAIGN_WORK:
check_analytic432.sh and run_analytic_replay432.sh. The dependency receipts record
source Git blobs, package revisions and retained artifact SHA-256 values. The
local cache omits regenerable C and editor-index files and compresses the retained
proof/interpreter artifacts; no proof file or cache hash rule is changed.
