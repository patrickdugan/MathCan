# ROC-01 dated amendment B: conditional-null degeneracy and ideal allocation

**2026-11-16.** Preserve the frozen ranks, thresholds, random seeds, model sources and prior failed CI runs. This is an explanatory amendment to the T-B *readout-constrained* null interpretation. It does not alter the ROC-01 full-space random-basis requirement.

## Counterexample before inference

For the T-B closure-price optimization, every admissible rank-k subspace U contains row(G). When k=rank(G), row(G) is the **only** admissible subspace. When k=d, all admissible bases span the full space, giving B=0. Thus generating 128 independently seeded *conditional completions* at either extreme returns identical measurements, with zero statistical variation. More generally, the conditional leakage values may all be equal even if orientations differ.

The full ROC-01 card uses **128 unconstrained rank-k Haar/QR null bases** on each frozen state and observer. The readout-constrained T-B sweep uses a distinct 128-attempt ensemble inside ker(G) with k-rank(G) free dimensions. These distributions answer different questions. Their p-values are never interchangeable.

The T-B closure-sweep implementation now reports conditional_null_degenerate=true and one_sided_rank_p_for_svd_candidate=null when k=rank(G), k=d or the measured conditional leakage distribution is constant within numerical tolerance. It retains the original seeds and all attempted null measurements for provenance, while abstaining from a misleading rank-p significance statement. A separate physical norm-matched intervention remains required for any causal endpoint.

The initial test asserted that two source identifiers should produce different random medians even when k=rank(G). That test failed because the null has no free orientation; the corrected test checks k>rank(G) for actual variation. The earlier failed CI records remain public.

## Exact idealized T-C allocation

For the *hypothetical* five-type binary signature table, the smallest noiseless separating set has three arm types. Under Gaussian unit-variance independent effects, let x,y,z,w be allocation shares for dark-to-observed, observed-to-dark, freeze U and readout ablation. The worst-pair squared mean difference per draw is t=min(z,x+y,x+w,y+w). Since x+y+z+w=1,

5t <= 2z+(x+y)+(x+w)+(y+w)=2,

and equality is attained by (x,y,z,w)=(1/5,1/5,2/5,1/5). The max-min Gaussian pair KL is t/2=1/5. The readout ablation arm gets positive allocation despite being unnecessary for *noiseless* separation.

This is a checked exact-Fraction linear-program calculation, with a narrow integer-scaled Lean inequality. The optimal neural intervention allocation remains unknown until measured case-conditioned effect distributions and routing data exist.

## Literature and Lean trust boundary

Finite observability and invariant output subspaces belong to established Kalman theory; balanced realization and model reduction trace to B. C. Moore (1981). Classical Hankel-singular-value error bounds for stable balanced truncation cannot be transferred directly to the B block norm.

The existing finite Lean bit-pair witness uses standard propext; the new integer-scaled allocation inequality uses standard propext and Quot.sound through omega. These are ordinary Lean axioms. Real Frobenius/singular-value bounds and stochastic Chernoff theory remain written proofs, outside the present Lean module.
