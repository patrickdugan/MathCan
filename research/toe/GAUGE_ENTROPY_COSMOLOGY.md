# TOE-01/02: Gauge-relative entropy, discrete curvature, and cosmological null space

**Research status, 2026-11-11:** written finite-dimensional proofs, exact-rational tests, a kernel-checked *target* for integer graph-gauge lemmas. No Einstein equations or observational cosmology are derived. The first mathematics is classical Gaussian/Hodge geometry, distinct from geometric quantum relative entropy in Bianconi's gravity proposal.

## Provenance

Source-linked TOE episodes: [Ginestra Bianconi, July 13, 2026](https://podscan.fm/podcasts/theories-of-everything-with-curt-jaimungal/episodes/ginestra-bianconi-the-physicist-who-unexpectedly-derived-gravity-from-entropy) (07:38 relative entropy, 23:45 emergent dark energy); [Lucrezia Ravera, September 14, 2026](https://podcastrex.com/shows/theories-of-everything-with-curt-jaimungal/she-says-spacetime-points-are-just-where-fields-meet/transcript) (05:31 dressing, 33:52 Gribov–Singer); [Jonathan Gorard, October 5, 2026](https://podscan.fm/podcasts/theories-of-everything-with-curt-jaimungal/episodes/jonathan-gorard-the-physicist-revolutionizing-physics-with-ai) (executable mathematical versus physical results); [Erik Verlinde, February 16, 2026](https://podscripts.co/podcasts/theories-of-everything-with-curt-jaimungal/erik-verlinde-this-physicist-unexpectedly-derived-gravity-from-information) (46:18 contrast with Jacobson). See [the six-episode intake](EPISODE_INDEX.json) and [triage note](TRANSCRIPT_TRIAGE.md).

Primary sources: [Bianconi, Gravity from Entropy](https://arxiv.org/abs/2408.14391); [François–Ravera, Geometric Relational Framework](https://arxiv.org/abs/2407.04043); [Bianconi's October 2026 ΛGfE extension](https://arxiv.org/abs/2610.34496). The last paper was published after Bianconi's July interview. The recorded interviews motivate comparisons; the following constructions belong to this MathCan investigation. Third-party machine transcripts can mishear technical terms. They require audio/paper verification for scientific attribution.

## TOE-01: the finite Gaussian quotient action

For a connected graph with n vertices and m oriented edges, let D be its m×(n−1) edge–vertex incidence matrix with the root gauge fixed. An edge field is q∈R^m and its positive-definite observational covariance is Σ. Define

\[
I_G(q)=\min_\phi\frac12(q-D\phi)^\top\Sigma^{-1}(q-D\phi).
\]

For Gaussians with identical covariance, the expression being minimized is precisely KL divergence between N(q,Σ) and the flat-model family N(Dφ,Σ). Let C be a full-row-rank basis of the cycle space ker(Dᵀ), so CD=0.

**T1 (exact gauge-quotient identity).**

\[
\boxed{I_G(q)=\frac12(Cq)^\top(C\Sigma C^\top)^{-1}(Cq).}
\]

*Proof.* The optimal residual r=q−Dφ satisfies the normal equation DᵀΣ⁻¹r=0. Therefore r=ΣCᵀλ for some λ. The constraint Cr=Cq gives λ=(CΣCᵀ)⁻¹Cq. Substitution proves the formula. Since ker(C)=im(D), the minimum is zero exactly when q is an exact vertex-gradient. For a tree the cycle space is zero-dimensional, so every edge field is an exact gradient. QED.

**T2 (sufficient cycle statistic).** For X∼N(q,Σ), the cycle vector CX has mean Cq and covariance CΣCᵀ, independently of vertex gauge. The KL divergence from the flat cycle distribution N(0,CΣCᵀ) equals T1. Thus all *quotient-model discrepancy* information is present in the cycle statistic.

**T3 (information loss under linear coarse observation).** Given a linear observation A with independent rows, covariance AΣAᵀ and nuisance family im(AD), the new minimum I_A satisfies

\[
0\le I_A(Aq)\le I_G(q).
\]

*Proof.* The matrix Σ^(1/2)Aᵀ(AΣAᵀ)⁻¹AΣ^(1/2) is an orthogonal projector. For every residual x, xᵀAᵀ(AΣAᵀ)⁻¹Ax≤xᵀΣ⁻¹x. Apply this to x=q−Dφ and minimize. QED.

**Exact counterexample to arbitrary compactification.** On an oriented triangle with q=(0,0,1) and Σ=I, the cycle sum is 1 with variance 3, and T1 gives 1/6. Recording only two spanning-tree edges yields I_A=0. The single measurement [1,1,1] preserves 1/6. This finite gauge-invariant blind spot connects naturally to [RSITopology](https://github.com/MoralityLabAI/RSITopology) and [Compactification-Theory](https://github.com/MoralityLabAI/Compactification-Theory), subject to those projects' separate interpretation and empirical gates.

**T4 (classical Kolmogorov cycle criterion).** On a connected undirected graph with positive paired rates k_uv,k_vu, a positive detailed-balance distribution π satisfying π_u k_uv=π_v k_vu exists exactly when the rate ratios k_uv/k_vu multiply to 1 along every oriented cycle. Necessity follows by multiplication. For sufficiency, transport π along a spanning tree and use cycle consistency to prove path independence, then normalize. A nontrivial rate-cycle product obstructs reversibility, a finite analogue of stochastic entropy production.

## TOE-02: standard Friedmann polynomial null test

For a conventional FLRW Friedmann background with pressureless matter, radiation, curvature and constant cosmological term, with x=1+z>0,

\[
E(z)^2=\Omega_\Lambda+\Omega_k x^2+\Omega_m x^3+\Omega_r x^4,
\qquad E(z)=H(z)/H_0.
\]

At N distinct redshifts define an N×4 design matrix F with row (1,x²,x³,x⁴). For measured y=E² and positive covariance Σ, use the same quadratic quotient:

\[
I_{\mathrm{FRW}}(y)=\min_\theta\tfrac12(y-F\theta)^\top\Sigma^{-1}(y-F\theta).
\]

**T5 (null-space dimension).** For N distinct z≥0, rank(F)=min(N,4). Every nonzero combination of monomials 1,x²,x³,x⁴ has at most three positive zeros, by Descartes' sign rule; hence every four rows are independent. The number of independent exact null relations is max(N−4,0).

**T6 (observational identification boundary).** Any perturbation in im(F) can be absorbed by changing nuisance coefficients and has zero independent quotient signature. On five synthetic redshifts z=0,1,2,3,4, a linear-in-(1+z) deviation is visible. With unit-variance independent observations, its exact action is **36/60995**. A perturbation proportional to x², x³ or x⁴ is indistinguishable from changes in curvature, matter or radiation coefficients using this null test alone. The test has no observational data and does not make a finding about dark energy.

The standard FLRW parameter normalization E(0)=1 and positivity/prior information can impose additional constraints. Hubble-rate measurements have correlated uncertainties, and transforming H to H² requires a correct covariance treatment. A modified-gravity proposal must first supply its own field equations and H(z) before using this benchmark. It is premature to insert Bianconi's emergent Λ_G into the conventional Friedmann formula without checking the modified equations.

## Research next steps

- Read Bianconi's [ΛGfE extension](https://arxiv.org/abs/2610.34496), extract its background equations, and construct a documented differential prediction for H(z), with model parameters and physical restrictions.
- Compare Ravera's relational field observables and their finite gauge analogues under graph refinement, including topological cycles lost through compression.
- Explore whether Gorard-type discrete geometric structures admit continuum limits that preserve an appropriate action and measurement covariance; specify the refinement map before asserting convergence.
- Build separate predictions for Verlinde and Mannheim, where they are calculable. The finite KL and Friedmann tests supply identification boundaries, while physics validation requires independent observables and data.

## Reproduce

```sh
python -m unittest tests.test_toe_cosmology -v
python -m research.toe.transcript_intake --list
lake build MathCan
lake env lean MathCan/TOEGraph.lean
```

The Python code uses exact Fraction arithmetic. The Lean file establishes graph path/gauge statements, while the general Gaussian matrix and FLRW polynomial theorems retain written proofs and rational regression tests. No full copyrighted transcripts are redistributed.
