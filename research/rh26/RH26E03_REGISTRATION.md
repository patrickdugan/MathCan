# RH-26E-03 preregistration: exact density-normalized scalar bound

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, branch research/rh26-extraction-rubrics-20261123.
**Provenance:** frozen upstream leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b; RH26C02_ERROR_BRACKET.md and RH26C03_NORMALIZATION.md. Relevant prior anchors: ErrorFormsWeakWindowsFalse.lean:117-119, GrowthBoundGivesRiemannHypothesis.lean:148-161, ChCore.lean:336-342,396-495. No new upstream reads or imported upstream proof.

## Scope and mathematical contract

Independently prove the scalar implication behind GrowthSizeBound. Use real variables x, eps, n,N,P,m,b,k,a, generalizing the source's natural n,N,P,m by coercion. Window retains the scalar source constraints:
x>=3, eps>0, n>0, b>0, a>=0, a<=2*x*b,
N>=x^(-eps/8)*n/2, P/n>=x^(-eps), P<=n,
x^(1/2-eps)<=m<=x^(1/2+eps/2),
x*m<=k<=n^2*x^(1/2-eps), 26<=x^(3*eps/8).
The source C>=0 and Err upper bound remain separate premises of the final theorem. Derive all needed positive denominators; do not assume positivity of the signed observable G. Define the independently written exact raw bracket B=N*a*(1+m^2/k)+m*(2*n*m*b*x^eps+P*k*b*x^eps/(n*(n*x^(-eps)))). Q=N*m*b, delta=P/n.

## Registered declarations (RH26E03 namespace)

1. window_positive: derive x,N,P,m,k positive from Window.
2. bracket_normalization: B/Q equals a/(m*b)+a*m/(b*k)+(2*n/N)*m*x^eps+(P/N)*(k/n^2)*x^(2*eps) under positive denominators.
3. card_ratio: n/N <= 2*x^(eps/8) under Window.
4. component_bounds: all four normalized terms <= 2*x/m, 2, 4*m*x^(9*eps/8), 2*x^(1/2+9*eps/8), respectively.
5. bracket_bound: B/Q <= 10*x^(1/2+13*eps/8) under Window.
6. two_term_envelope: B/Q <= x^(13*eps/8)*(4*x/m+6*m) under Window and m>=1 (automatic for positive natural m).
7. density_inverse: positive delta>=x^(-eps) yields 1/delta<=x^eps.
8. density_normalize: from Q*(delta/2)*(G-4*J)<=H*B+2*Q/x, with Q,delta,x positive, derive G<=2*H*(B/Q)/delta+4/(delta*x)+4*J (equivalent rearrangement permitted).
9. growth_bound: with Window, C>=0, Err<=x^(C*eps)*B and the exact source scalar inequality Q*(delta/2)*(G-4*x^(1/2+eps))<=Err+2*Q/x, prove G<=x^(1/2+(C+3)*eps). Prove actual real-power identities and constant absorption; no extra postulated power relations. Real coercions encompass natural source parameters.
10. zero_density_control: explicit zero-density case, inequality holds with G>26.
11. zero_volume_control: explicit zero-Q case, inequality holds with G>26.
12. missing_density_control: explicit positive Q,delta,x example satisfying the inequality but violating the expression obtained by dropping inverse density.
13. no_loss_family: positive natural t>=2 with x=t^2, m=b=t, n=N=P=x, k=a=x*t, eps=1, source absorption threshold and 2*x>A+D; prove Window and B/Q>A*x/m+D*m for any fixed positive A,D. This is scalar data only; no actual arithmetic family realization claimed.
14. no_uniform_no_loss: for each A,D>0 exhibit an integer t meeting the previous conditions. Show absence of a uniform fixed-coefficient envelope on the scalar domain for the normalized bracket, not for the possibly smaller actual gap.

## Acceptance and resources

All fourteen named declarations must compile under pinned Lean 4.35.0 and Mathlib v4.35.0, with exactly their transitive axiom receipts and only propext, Classical.choice, Quot.sound allowed. No admissions or custom axioms. Controls are positively proved witnesses or parameterized counterexamples. A failed or pending job is recorded as such. Do not change frozen mathematical contracts to pass.

Use isolated research/rh26/lean/RH26E03GrowthBound.lean, existing experiments/deligne_mathlib environment, one CPU workflow per changed code/workflow push, 25-minute timeout. Capture source SHA-256, compiler and Mathlib SHAs, exact axiom audit, isolated timing/RSS. No full Deligne or upstream build, paid cloud, GPU/QPU. Record report and ledger, update draft PR. Source only until actual CI confirms the proof. Scientific scope: scalar consequence conditional on the upstream gap inequality and eligible family constraints; no new analytic or RH proof, no fixed-coefficient bound for an unconstrained prime sum.
