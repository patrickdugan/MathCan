# NRF-04: Task-observation closure and a sharp Jordan leakage frontier

November 15, 2026. A concrete synthesis developed for the LoopedTransformers/MathCan research program. The mathematical observations are new derivations for this project; priority in the literature is **not claimed**. Exact rowspace and lumping criteria have substantial prior art, notably Kalman observability and algorithmic exact lumping.

## Input problem and empirical motivation

The two OpenAI preprints used by NRF-01 to NRF-04 are:
- *A direct proof of the complete Crouzeix inequality* (2026-09-26), https://github.com/openai/math/tree/main/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026
- *Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces* (2026-09-24), https://github.com/openai/math/tree/main/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026

NRF-03 proved factorization through observations and an approximate quotient bound. NRF-04 tests actual tied residual-loop weights with the signed-permutation teacher. Its frozen protocol and twelve-checkpoint results are in MoralityLabAI/LoopedTransformers PR #56. All twelve supervised rank-eight projections improve held-out task MSE compared with eight matched-rank random projections, and all twelve have higher pointwise dark-to-observed leakage than the random median. Those data motivate an exact mathematical obstruction.

**Prior-art boundaries.** The smallest invariant observable subspace is a classical concept from Kalman observability. Exact reduction by a Jacobian-invariant rowspace appears in the nonlinear lumping literature, including https://par.nsf.gov/servlets/purl/10396180 and https://www.iris.sssup.it/retrieve/a350b573-497e-43da-91e6-052a987f1801/RSPA_ApproximateReduction.pdf. NRF-04 contributes a concrete tanh-residual gate-family specialization, a finite rational verifier, and a sharp two-dimensional task/leakage example, within this research program.

## Theorem NRF-04A: minimal robust gate closure

Let W1 in R^{p x n}, W2 in R^{n x p}, and let C be the k x n task observation. For every diagonal D=diag(d1,...,dp), define R_D=W2 D W1. Set a_j=W2[:,j] and b_j^T=W1[j,:], so R_D=sum_j d_j a_j b_j^T.

Among rowspaces S containing row(C) and satisfying S R_D subset S for *every independently chosen diagonal D* (it suffices to test D in [0,1]^p), the unique smallest S is obtained by this finite iteration:

    S_0 = row(C)
    S_(t+1) = span(S_t union
                {b_j^T : exists s in S_t with s a_j != 0}).

The chain stabilizes after at most n-rank(C) strict dimension increases. Rational W1, W2, C yield an exact rational RREF algorithm.

**Proof.** For s in S, s R_(E_j)=(s a_j) b_j^T, so invariance under every E_j requires either S a_j=0 or b_j^T in S. Conversely that condition for each j implies invariance under each rank-one R_(E_j) and thus every linear combination R_D. Every admissible invariant S contains S_0. If it contains S_t, the rank-one invariance conditions force it to contain S_(t+1). Induction proves minimality. Once a step adds no dimension, its rowspace satisfies all gate-invariance conditions. Since each strict step increases dimension and dim(S)<=n, termination is finite.

### Stronger necessity for actual tanh residuals

For the real map

    F(x)=alpha*x+beta*W2 tanh(W1*x+b1)+beta*b2,

the Jacobian is J(x)=alpha*I+beta*W2 diag(sech^2(W1*x+b1)) W1. If beta!=0, invariance under the *independent-gate family* is sufficient for observation-factor invariance at every state.

If the domain is all R^n, p=n and W1 is invertible, it is also necessary: W1*x+b1 ranges across R^n; the coordinates sech^2(u_j) can independently fill (0,1]. Compare Jacobians with diagonal gates differing in a single component. Closure under all such J(x) forces closure under every rank-one a_j b_j^T. By the differentiable-factor criterion of NRF-03, this is the minimal dimension of a linear observation that can retain row(C) and admit an exact induced nonlinear update on the entire state space. The conclusion is conditional on the stated invertibility and full-domain hypotheses. On a restricted reachable-state set the derivative gates may be coupled, and the independent-gate closure may overestimate the necessary dimension.

## Theorem NRF-04B: exact task/leakage Pareto frontier in dimension two

Let X in R^2 have mean zero and covariance I_2. Take teacher y=e1^T X and the nonnormal linear recurrent map J=aI+b E12 with b real. Compress to rank one via P=uu^T where u=(cos theta,sin theta). Let E(P) be the minimum mean-squared teacher error achievable by any linear decoder of PX; let L(P)=||P J(I-P)||_F be the local dark-to-observed Jacobian leakage.

Then, with E=E(P) and L=L(P),

    E=sin^2(theta),  L=|b| cos^2(theta)
    and therefore       L + |b| E = |b|,   0<=E<=1.

Every point on this exact Pareto frontier is attained by some rank-one P. If b!=0, no rank-one projection can have both perfect teacher prediction E=0 and vanishing leakage L=0. A rank-two observation P=I has E=L=0. Thus the minimal exact-closure dimension jumps from one (b=0) to two (b!=0).

**Proof.** Under isotropic covariance, the optimal linear prediction of e1^T X from u^T X is u1 (u^T X), hence its squared prediction error is ||(I-P)e1||^2=u2^2. Let v=(-u2,u1) span the orthogonal complement. Since u^T I v=0 and u^T E12 v=u1^2, the rank-one matrix PJ(I-P)=(b u1^2) u v^T has Frobenius norm |b|u1^2. Consequently L+|b|E=|b|(u1^2+u2^2)=|b|. The rank-two case is immediate from I-P=0.

For a nonnegative penalty lambda, the minimizer of the tradeoff objective

    E+lambda*L^2 = E+lambda*b^2*(1-E)^2

is

    E*=0,                                      if 2 lambda b^2<=1;
    E*=1-1/(2 lambda b^2),                    if 2 lambda b^2>1.

Differentiate the convex quadratic on [0,1] and clamp the unconstrained minimum at zero. This is a fully explicit regularization path for the task/observability tradeoff.

## Theorem NRF-04C: linear Krylov boundary

For a single n-dimensional linear update J and task output C, the smallest rowspace containing row(C) and closed under right multiplication by J is

    S_min = row(span(C, C J, C J^2, ..., C J^(n-1))).

This follows by successive right multiplication and Cayley-Hamilton. For J=aI+bE12 with task C=e1^T, C J=a e1^T + b e2^T. The minimal dimension is two when b!=0 and one when b=0, matching the rank-one frontier above.

This is the standard observability Krylov construction. NRF-04A extends it to a finite *family of rank-one activation gates* for a nonlinear tied residual MLP.

## Exact code and formal scope

- research/compactification/observable_closure.py implements exact Fraction RREF, activation-gate closure, direct Jordan matrix products, and the Pareto penalty minimizer.
- tests/test_observable_closure.py checks **512 binary two-by-two weight families** and **108 exact rational Jordan matrices**, plus 1,300 discrete penalty comparisons and a rank-jump witness.
- MathCan/ObservableFamily.lean proves abstract finite-family fiber compatibility and induced-factor existence by importing the earlier Lean-checked ObservableQuotient module. Its Lean kernel does **not** certify the full rowspace, differentiable necessity, or stochastic-risk theorem.
- The empirical NRF-04 result is a **negative joint-gate outcome**. Prediction improves while leakage worsens relative to matched random controls. Theorems above explain a possible structural mechanism, without proving it is the cause of that observation.

### Next measurable proposition

For the saved 128x128 trained W1 and W2, test the exact/interval-certified dimension of the gate-family closure starting from the eight learned decoder rows, and repeat from matched random rows. Independent-gate closure may saturate the full space, in which case test a *restricted activation-gate family* on a preregistered reachable-state region, using reliable upper bounds. A smaller learned subspace should be promoted only if its measured held-out task utility and calibrated leakage bounds both meet the prespecified criterion.


## Exact native-weight corroboration (NRF-04E)

A separate binary32/finite-field audit of **all twelve source-hashed tied ToyLoop checkpoints** from MoralityLabAI/LoopedTransformers PR #56 establishes that every archived 128×128 W1 is invertible over the rationals and reals when its stored IEEE binary32 values are interpreted exactly. For each W1, multiply every entry by 2^149 to obtain an integer matrix; its determinant is nonzero modulo both independent primes 65,521 and 65,519. Each of the twelve W2 matrices has zero exact-zero entries.

For every nonempty **coordinate projection** C (e.g. the first eight stored coordinates), C W2[:,j] is nonzero for every activation channel j. The first step of the NRF-04A closure therefore includes all 128 rows of W1, which have full row rank. Consequently the minimal globally invariant observation space containing such a coordinate selection has dimension 128. On the **full real state domain**, the invertible W1 makes the actual tanh derivative gates vary independently, so this is a necessary condition for an exact linear observable factor, as established by the full-domain qualification in NRF-04A.

Evidence: [LoopedTransformers NRF-04 exact gate closure receipt](https://github.com/MoralityLabAI/LoopedTransformers/blob/research/crouzeix-fixedpoint-switching-20261115/experiments/numerical_range_fixed_point_v1/nrf04_exact_gate_closure.json) and its independent Python replay verifier with five local tests. The checkpoint repository is private, and this public mathematical note states only the dimension and modular-certificate summary.

The theorem applies to the specified coordinate observations. It does **not** establish the minimal gate closure for every learned non-coordinate task decoder, nor the rank needed on a bounded reachable-state subset. An approximate quotient may remain useful despite failure of the exact full-domain criterion.

**Lean scope:** MathCan/ObservablePareto.lean checks two cross-multiplied Pythagorean/Nat fragments of the rank-one Jordan frontier. Analytic real-norm, probability, and minimal rowspace assertions are supported by written proofs and the exact-rational Python oracle rather than a complete Lean formalization.


## NRF-04F: exact certificate for the learned eight-dimensional observation

The coordinate-only result in NRF-04E has been extended to the **specific supervised rank-eight subspaces** trained in the frozen decoder experiment. For every one of the twelve checkpoints, the first basis vector u of the supervised observation was recorded as 128 canonical IEEE binary64 hex patterns. This vector lies in the learned observation rowspace.

For each stored binary32 W2 and each activation channel j, compute the exact dyadic dot product u W2[:,j]. Multiplication by 2^(1074+149) produces an integer, and reducing it modulo 65,521 and 65,519 yields a nonzero value for **all 128 channels in all twelve models**. This proves the true real dot product is nonzero, independently of any floating tolerance. As the native W1 integer-scaled determinants are nonzero modulo both primes, the first closure step already spans all 128 dimensions.

Thus, under the stated **full-state-domain** tanh assumptions and the *exact recorded binary64* supervised observation vectors, the minimal globally closed linear observation containing each trained eight-dimensional subspace has dimension 128. An induced exact nonlinear update on only those eight observed coordinates cannot exist globally for these particular maps.

Evidence: [learned projection exact closure receipt](https://github.com/MoralityLabAI/LoopedTransformers/blob/research/crouzeix-fixedpoint-switching-20261115/experiments/numerical_range_fixed_point_v1/nrf04_learned_projection_exact_closure.json), which preserves the full basis vector bits and first-eight modular residues, and the independent verifier research_gym/analysis/nrf04_verify_learned_projection.py. Four local verifier tests check dyadic scaling, signed zeros, cancellation and failure on invalid encodings.

The basis vectors came from a deterministic JavaScript float64 realization of the preregistered teacher decoder. A fresh PyTorch-native replay can differ in last-bit rounding; its own exact binary64 basis vectors must be sealed and checked separately before extending the certificate to that implementation. The statement concerns the recorded trained subspaces and full-domain exact observation factors. It leaves the finite reachable set, approximate factorization, and nonlinear observation choices open.
