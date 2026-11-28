# NRF-03: observable-fiber contraction with a measurable leakage obstruction

Date: November 15, 2026. Research-program theorem and proof, mathematical priority unassessed.

## Motivation and source scope

NRF-01 and NRF-02 combined OpenAI math preprint #325, *A direct proof of the complete Crouzeix inequality* (September 26, 2026), with #328, *Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces* (September 24, 2026). NRF-02's global hidden-state contraction assumptions can fail for trained residual loops of the form x -> x + beta W2 tanh(W1 x + b1) + beta b2. The new question is whether an observation or decoder can remain predictable when the hidden dynamics expand. Such a decoder must pay for coupling from its discarded (dark) fiber.

The general numerical-range polynomial estimate remains conditional on the claimed complete Crouzeix result. The quotient theorem below needs neither preprint and has a direct proof. Precedents include factor maps, semiconjugacy, quotient dynamical systems, perturbation comparison inequalities and graph-weighted contraction; no worldwide novelty claim is made.

## Theorem NRF-03A: exact factorization criterion

Let X,Y be sets; let pi:X->Y be surjective and F:X->X. Then the following are equivalent:

1. There is a (necessarily unique) map f:Y->Y such that pi F=f pi.
2. F respects observational equivalence: pi(x)=pi(x') implies pi F(x)=pi F(x').

For (1)->(2), substitute f pi on both sides. For (2)->(1), select a right inverse s:Y->X and define f(y)=pi F(s(y)). Fiber compatibility makes its value independent of the chosen section and proves pi F=f pi. Uniqueness follows from surjectivity.

MathCan/ObservableQuotient.lean checks this equivalence and uniqueness over arbitrary types using Init. Classical.choice is used to obtain a section from surjectivity. This is a structural result; norm estimates below have human-readable proofs.

## Theorem NRF-03B: graph-weighted approximate quotient

Let C be a subset of a normed vector space, Y a normed observation space, pi:C->Y a surjection with section s:Y->C, and K_e:C->C a family of permitted graph-edge maps. Define f_e(y)=pi(K_e(s(y))) and assume the induced f_e is Lipschitz with constant ell_e>=0. Suppose a uniform fiber defect is available:

    || pi K_e(x) - f_e(pi x) || <= Delta_e       for every x in C.

For two state trajectories x_t,z_t following the SAME externally permitted edge sequence e_t, write E_t=||pi x_t - pi z_t||. Then

    E_(t+1) <= ell_(e_t) E_t + 2 Delta_(e_t).

Indeed, insert f_e(pi x_t) and f_e(pi z_t) between their two outputs. The two fiber defects cost at most Delta_e each, while the middle term costs ell_e E_t. Iterating gives

    E_T <= (product_(t<T) ell_(e_t)) E_0
           + sum_(j<T) 2 Delta_(e_j) product_(j<k<T) ell_(e_k).

If positive graph vertex weights w satisfy ell_e*w_source<=alpha*w_target with 0<alpha<1, then

    E_T/w_(v_T) <= alpha^T E_0/w_(v_0)
                  + sum_(j<T) alpha^(T-1-j) (2 Delta_(e_j))/w_(v_(j+1)).

Unlike full-state contraction, this can hold when sup ||D K_e|| exceeds one. A state-dependent *hard* edge policy must also pass the NRF-02 strict guard margin, since different branches are not governed by a shared-path comparison.

## Theorem NRF-03C: differentiable leakage criterion

Let H be a Hilbert space, pi:H->Y a bounded surjective linear observation, and F:H->H be differentiable on an open convex domain U. If there is an exact observation factor f with pi F=f pi on U, then

    pi (D F(x) h) = 0    for each x in U and h in ker(pi).

Proof: for sufficiently small scalar t, x+th belongs to U and pi(x+th)=pi x. Thus pi F(x+th)=pi F(x), and dividing by t and sending t->0 gives the claim.

Conversely, suppose every pair x,z in U with pi x=pi z is connected by its straight segment in U and

    pi D F(a) h = 0 for all a in U, h in ker(pi).

Integrate the derivative of pi F along x+t(z-x) to obtain pi F(x)=pi F(z). NRF-03A gives an induced map on pi(U). Therefore the vanishing *dark-to-observed Jacobian block* is a necessary-and-sufficient local criterion for exact observation factorization under the stated segment condition.

For approximate factors, let s be a section whose fiber segments remain in U. If

    sup_(a in U) || pi D F(a)|_(ker pi) || <= L_dark

and every such segment has length at most R_fiber, then the mean-value integral gives the global fiber-defect certificate

    Delta <= L_dark * R_fiber.

A pointwise Jacobian measurement provides a **lower witness of nonzero leakage** and is not a uniform L_dark bound.

## Theorem NRF-03D: tanh residual global certificate and local obstruction

For stored finite-dimensional real matrices W1,W2, biases b1,b2 and nonnegative scales alpha,beta, let

    F(x)=alpha*x + beta*(W2*tanh(W1*x+b1)+b2).

Differentiation yields

    D F(x)=alpha I + beta W2 diag(sech^2(W1*x+b1)) W1.

Since ||diag(sech^2)||<=1, a global Lipschitz upper bound is

    L_global = alpha + beta ||W2||_2 ||W1||_2.

For each matrix W, the elementary inequality

    ||W||_2 <= sqrt(||W||_1 ||W||_infinity)

provides an upper enclosure using row and column sums. If weights are IEEE binary32, every entry is an integer multiple of 2^-149. One can sum absolute row/column entries exactly as integers over this common denominator, take an integer ceiling square root and round the resulting L_global **upward** to an explicit decimal grid.

For any R-step composition Q=F_R o ... o F_1 and base point x, the chain-rule product

    J_R(x) = D F_R(x_(R-1)) ... D F_1(x_0)

supplies a local obstruction. If ||J_R(x)v|| > c||v|| for one nonzero direction v, then Q is not globally c-Lipschitz on any neighborhood of x. In particular a local amplification greater than one rules out a global full-cycle strict contraction. A deterministic power-iteration estimate is a *numerical lower witness*, not a rigorous global operator-norm upper bound.

## Worked exact-rational model and failure of an exact quotient

Take C=[-1,1]^2 and pi(x,y)=x, s(x)=(x,0). Let

    F(x,y)=(x/2+y/4, y/2).

F maps C to C. The induced section map is f(x)=x/2, with uniform fiber defect Delta=1/4. Two trajectories with identical observed initial x but hidden y=1 and y=-1 separate by 1/2 in their first observation. This attains E_next<=ell E+2Delta with ell=1/2, making the factor-of-two defect term sharp.

The linear map (x,y)->(x/2,2y) on R^2 illustrates exact observable contraction despite expanding hidden dynamics: its induced f(x)=x/2 and pi DF(0,1)=0. Adding an off-diagonal coupling (x,y)->(x/2+a*y,2y) immediately destroys the exact factor when a!=0, even though the observed self-dynamics still has coefficient 1/2. A small but nonzero dark-to-observed derivative is enough to refute exact quotient equivalence.

## Empirical protocol and evidence limits

MoralityLabAI/LoopedTransformers PR #56 includes NRF-03 frozen checkpoint replay. The tested split is fixed in advance: pi selects the first eight of 128 coordinates; the other 120 form the discarded fiber. The analysis must use actual saved-weight hashes, a pinned zero-state starting point, a fixed deterministic dark direction and an independently measured perturbation direction. One-point dark leakage refutes exact factorization near that point if numerically stable, but establishes no uniform Delta or extrapolation benefit. A different decoder, trained or derived from semantic labels, requires a separate registration and matched random-projection controls.

The scalar polynomial numerical-range theorem still applies to polynomial filters; the actual tanh residual block uses the independently proved derivative bound above. The distinction between these model classes is important for interpreting NRF-01 to NRF-03.
