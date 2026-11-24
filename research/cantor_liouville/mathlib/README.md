# CLN-02 — Prime-power returns and Fourier collision energy

Isolated Mathlib project, aligned with MathCan's Lean 4.35.0 toolchain. No changes to the root project's dependency graph. The Mathlib tag v4.35.0 is pinned; source signatures checked against that tag.

Run `lake update`, then `lake exe cache get`, then `lake env lean CLN02.lean` here. The dedicated CI job records the exported axiom closures. No sorry or new axioms are intended; status is pending until actual kernel execution.

Targets: odd-prime LTE return iff, exact principal-unit order, even-exponent 2-adic return iff, standard character orthogonality, collision cross-Gram matrix, arbitrary complex-weight bilinear identity, conjugation, squared Fourier energy. The 2-adic statement suffices for the period lower bound: if b^P is 1 modulo 2^t, so is b^(2P); the theorem forces 2^max(t-v2(b-1)-v2(b+1),0) to divide P. Composite assembly, conditional measure estimates, Weyl criterion and Liouville corollary remain further targets.

References: Mathlib v4.35.0 Mathlib/NumberTheory/Multiplicity.lean, Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean, Mathlib/Algebra/Group/AddChar.lean and Mathlib/GroupTheory/OrderOfElement.lean. See ../CLN01_PREFIX_ENTROPY.md for the mathematical derivation and source provenance.
