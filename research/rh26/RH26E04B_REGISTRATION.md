# RH-26E-04B registration: exact and stable block-scalar transport

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, branch research/rh26-extraction-rubrics-20261123.
**Inspiration:** frozen upstream leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b, NandDIVb.lean:52–57 and SumRepresentations.lean:177–184, traced in RH26B08_RANK_CERTIFICATE.md. No new upstream reads/imports. E04A kernel gate closed 10/10 before this experiment.

## Question and null

Can a finite independent block decomposition plus nonzero scalar forward/backward transport certify injectivity, and what survives when the composition has a bounded residual? The source gives a positive scalar composition on each row and invokes indexed internal decomposition. The independent abstraction uses an explicit resolution of the identity by pairwise-annihilating projections. The quantitative extension uses an actual continuous-linear-map operator norm, with a separate energy identity for orthogonal blocks. The null is that per-block gains alone are insufficient without a genuine decomposition or that a small residual relative to the wrong norm/condition number can still erase directions.

## Eleven frozen public theorem contracts

Namespace RH26E04B. In exact statements use a field K, finite label type, linear projections E_i:V→V satisfying sum_i E_i v=v and E_i E_j v=if j=i then E_i v else 0, linear T:V→W, P:W→V, scalar gains lambda_i, and PT E_i v=lambda_i E_i v.

1. block_scalar_projection: E_i(PT v)=lambda_i E_i v.
2. block_scalar_recovery: if all lambda_i are nonzero, sum_i lambda_i^{-1} E_i(PT v)=v.
3. block_scalar_injective: under the exact decomposition/scalar contracts, T is injective.
4. finite_energy_bound: finite real gains g_i>=a>=0 and real r_i imply a² sum_i r_i²<=sum_i (g_i r_i)².
5. orthogonal_block_gain: real normed space, continuous-linear A, block maps E_i, Pythagorean identity ||v||²=sum_i||E_i v||² for every v, E_i A v=lambda_i E_i v and a<=||lambda_i|| with a>=0 imply a||v||<=||A v||. The energy identity is an explicit hypothesis; no claim that arbitrary algebraic projections are orthogonal.
6. perturbed_composition_gain: continuous linear T,P,A with lower gain a for A and ||P.comp T-A||<=delta imply (a-delta)||v||<=||P(T v)||. Use actual operator norm. No sign hypothesis on v.
7. forward_gain: under the preceding premises and ||P||>0, ((a-delta)/||P||)||v||<=||T v||.
8. perturbed_injective: if delta<a in the preceding premises then T is injective; no additional positive norm assumption on P needed for this conclusion.
9. conditioned_block_gain: on real normed spaces (one common space suffices), continuous-linear A,D,S,Sinv with S(Sinv v)=v, Sinv(A v)=D(Sinv v), D lower gain a>=0, and both coordinate-map norms positive, imply (a/(||S||*||Sinv||))||v||<=||A v||. This makes the nonorthogonal conditioning cost explicit.
10. zero_gain_control: an explicit noninjective scalar-zero transport on the nonzero rational line satisfies the block scalar composition with gain zero (identity projection). Show the actual failure of injectivity.
11. threshold_equality_control: on the real line, explicit continuous-linear T,P,A with A lower gain 1/2, residual operator norm exactly 1/2, and T noninjective. A finite witness at the equality threshold, using the actual operator norm, proves the necessity of the strict gap in the general guarantee.

## Acceptance

All eleven declarations compile in one isolated MathCan Lean 4.35.0/Mathlib v4.35.0 file, with exact eleven-name axiom audit and only propext, Classical.choice, Quot.sound. No sorry, admit, custom axioms or native_decide. Report real norm assumptions, source proof vs independent abstraction, and literal compiler/axiom/SHAs/timing receipt. Pending or failed compilation is not PASS; preserve failures and repair only within the frozen mathematical statements.

Source research/rh26/lean/RH26E04BBlockTransport.lean; one GitHub CPU job per code/workflow change, 25-minute cap, existing experiments/deligne_mathlib pin. No full upstream or Deligne build, GPU/QPU or paid compute. No numerical rank claims. Next E04C weighted capacity dual, combined incidence/kernel defect or separately registered B09 source inventory.
