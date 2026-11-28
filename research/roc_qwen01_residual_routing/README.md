# ROC-QWEN-01: exact donor-routing identities

This companion to ROC-01 amendment C is synthetic exact rational mathematics.
It does not claim new Qwen measurements or a neural recurrent-state quotient.

Let U,V be d-by-k matrices with U^T U = V^T V = I and U^T V=0.
For any coefficient vector c, the maps UV^T: span(V) -> span(U) and
VU^T: span(U) -> span(V) are inverse isometries. Indeed UV^T(Vc)=Uc,
VU^T(Uc)=Vc, and ||Uc||^2=||Vc||^2=c^T c. The map UU^T fixes Uc and
annihilates Vc. Thus donor coefficients can be physically routed dark-to-observed,
observed-to-dark and observed-to-observed with identical prescribed L2 radii.

The source frame V is a selected rank-k part of the dark complement, not the
entire d-k dimensional complement. No dimension-reducing global isometry from
all dark space to observed space is asserted. An arbitrary donor difference z
must first be projected to V^T z or U^T z; a zero coefficient vector makes
normalization undefined and must fail explicitly.

`verify.py` checks nine rational radius/coefficient pairs on a non-coordinate
5-dimensional example, including exact orthogonality, isometry and routing.
Run `python3 research/roc_qwen01_residual_routing/verify.py` using the standard
library. Square-root rounding is avoided by choosing rational unit coefficients.

These maps specify an experimental intervention. They are not the blocks
U^T(T-I)V or V^T(T-I)U of a measured dynamical transition. Intermediate neural
residuals do not supply the complete DeltaNet/attention-cache state, and erasing
their U projection is not a separable readout-only ablation. A full four-arm ROC
card and T-B closure remain unavailable until the correct state transition and
readout boundary are instrumented. Synthetic exactness cannot fill that gap.

Amendment source: MathCan PR #99, commit
`37bbac210c175ccb98e0ff0d4aa8bdd2be0764e6`, dated amendment C, 16 November 2026.

