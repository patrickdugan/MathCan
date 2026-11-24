# ROC-01 Part 2: exact observer mathematics, counterexamples, proofs and Lean scope

Date 2026-11-16. The arguments are specializations of classical finite-dimensional linear algebra, observability and model reduction. Priority is not asserted.

## Counterexamples, checked before positive proofs

| Target | Exact witness in dimension <=6 | Status |
|---|---|---|
| T-A finite states force rank >=2 | Four states in Q², (0,0),(1,0),(0,1),(1,1), have distinct outputs 0,1,2,3 under the rank-one functional x+2y | Fraction checked; Lean finite Bool×Bool encoding |
| T-B closure cost decreases in k | T=diag(1,R90) on R³, G=[1 0 0], R90 a quarter-turn. L*(1)=0, L*(2)=1, L*(3)=0, while rank(O_N)=1 | Four rational unit-vector checks; all-rank-two real argument below |
| T-B observability tail upper-bounds leakage | The same rotation has singular tail zero beyond the first rank but L*(2)=1 | Exact rational counterexample |
| T-C five types are disjoint | A=B=0 and high causal capture s is a latched memory and a closed quotient; low s gives irrelevant behavior with the same A,B | Part-1 cards |
| T-D fixed lambda gives universally best rank | E=0,L=1 and E=1,L=0 exchange winners at lambda=1 | Fraction line-crossing witness |

The Fraction oracle in theory.py checks 540 finite-horizon **Frobenius-norm** inequalities on integer T with dimensions 2..6. The continuum proof is given below; exact witnesses alone are not a proof over all real matrices.

## T-A: conditions forcing observer rank

**Finite separation has no positive floor beyond one.** Given distinct x_1,...,x_N in R^d, the forbidden scalar observers satisfying u·(x_i-x_j)=0 form a finite union of proper hyperplanes. At least one u lies outside them. For rational points, set u_t=(1,t,...,t^(d−1)): for each nonzero pair difference the dot product is a nonzero polynomial of degree at most d−1. A choice from (N choose 2)(d−1)+1 distinct rational t values must separate every point.

**Exact linear decoder.** If the required all-state target is Gh and an observer U with k columns admits a fixed linear decoder W satisfying G=WU^T on all of R^d, then rank(G)≤k. This is sharp: choose the rowspace of G as U and W as its coordinates. NRF's rank-eight target requires k≥8 only under a demonstrated rank-eight full-domain linear target, not simply because the study selected eight dimensions.

**Precision.** If each of k channels has at most 2^b distinguishable levels, at most 2^(bk) codes exist. Injecting N states requires k≥ceil(log2(N)/b). More restrictive margin and Lipschitz conditions require their own packing argument (OLM-03A, PrecisionEntropy, COE-02). A real-valued rank-one projection with unlimited precision can defeat an alleged separation-only lower bound.

SPC-05's eight-phase fixed codebook has a contrast span of dimension **at most** seven. Rank seven becomes necessary for exact linear reconstruction only if the seven anchor contrasts are independent. SPC-08's rank-eight deferred-only choice is a study budget, not a proven universal minimum. TRM's lm_head has an 11D rowspace in 512D: preserving 11 independent logits via a linear decoder needs rank eleven, while preserving only the argmax can have a different floor.

## T-B: exact closure and finite-horizon price

Fix T in R^(d×d), G in R^(q×d), orthonormal U in R^(d×k), P=UU^T, and a complement Q. Require GP=G. Define

\[
L^*(k)=\min_{U^TU=I_k,\,GP=G}\Vert U^T(T-I)Q\Vert_F.
\]

Because U^TQ=0, the block equals U^TTQ. It vanishes exactly when im(U) is invariant under T^T. The smallest such subspace containing im(G^T) is

\[
W=\operatorname{span}\{(T^T)^j\operatorname{im}G^T: 0\le j<d\}
=\operatorname{im}O_d^T,\quad
O_d=[G;GT;\ldots;GT^{d-1}].
\]

Proof: any invariant subspace containing im(G^T) contains all its T^T iterates; Cayley–Hamilton makes this finite span invariant. Therefore W is the unique minimum-dimensional closed observer, with m=rank(O_d). If rank(G)≤k<m, L*(k)>0 by compactness of the readout-containing Grassmannian. When k≥m, zero leakage requires an invariant extension of W of that **exact** dimension. Real matrices do not necessarily admit one.

**Nonmonotonic exact-rank example.** Let T fix e1 and act as a 90-degree rotation on span(e2,e3), and set G=e1^T. Rank one U=e1 is exactly closed. Rank two containing e1 has U=span(e1,v) for a unit planar v and complement q=R90 v. The incoming block has magnitude |v^T R90 q|=1. Hence L*(2)=1, independent of v, while L*(3)=0. A closed observer need not be extendible to every intermediate real rank.

**Interior parity witness.** For T=1⊕R90⊕R90 on R⁵ and G=e₁ᵀ, a closed readout-containing subspace consists of e₁ together with a real invariant subspace of the four-dimensional quarter-turn block. Every such invariant subspace has even real dimension. A rank-three closed observer exists, whereas exact rank two and rank four cannot be closed. Compactness forces L*(2)>0 and L*(4)>0, and orthogonality strengthens these to L*(2)=1, L*(3)=0, L*(4)=1 at interior k<d. A rational canonical witness appears in theory.py.

**Finite-horizon lower bound.** With Q0=I-P, E=PTQ0 and M=||T||op, set Z_j=PT^j Q0. The recurrence is

\[
Z_{j+1}=(PTP)Z_j+E(Q0 T^j Q0),\qquad Z_1=E.
\]

Induction by operator-norm submultiplicativity gives ||Z_j||F≤j M^(j−1)||E||F. Because G=GP, stacking G T^j Q0 for j=0,...,N−1 yields

\[
\Vert O_N Q0\Vert_F^2\le
\Vert G\Vert_F^2\left(\sum_{j=1}^{N-1}j^2M^{2(j-1)}\right)\Vert B\Vert_F^2.
\]

Eckart–Young applied to the rank-k approximation O_N P gives

\[
E_k(O_N)=\sqrt{\sum_{i>k}\sigma_i(O_N)^2}
\le\Vert O_N Q0\Vert_F.
\]

Consequently, for N≥2 and positive denominator,

\[
\boxed{L^*(k)\ge
\frac{E_k(O_N)}
{\Vert G\Vert_F \sqrt{\sum_{j=1}^{N-1}j^2\Vert T\Vert_{op}^{2(j-1)}}}.}
\]

This is a generally loose **lower** bound using singular values of the finite observability matrix. It does not estimate L* from above, nor determine it when k exceeds rank(O_N). The weaker Frobenius-norm denominator is separately checked by 540 exact Fraction instances. The numerical closure sweep uses the stronger operator-norm denominator.

**Literature:** Kalman observability and finite invariant rowspace are classical. Lumpability is a standard observational-quotient concept (also MathCan ObservableQuotient). Moore's 1981 balanced realization and the Enns/Glover 1984 balanced truncation error theorem control transfer-function error using *Hankel singular values* and stable-system assumptions. They are not an automatic bound for the block ||U^TTQ|| or the singular spectrum of O_N. References: https://lall.stanford.edu/engr210a/lectures/lecture11_2001_11_07_01.pdf and https://www.sciencedirect.com/science/article/pii/S0005109814001952 .

The requested numerical L*(k) sweep at k={1,2,3,4,7,8,12,16,32} for NRF d128 and SPC d48 **has not run**: complete source checkpoint weights and observer adapters are absent from public MathCan. The existing per-state block receipts alone cannot optimize over U.

## T-C: interventions identifying types

The following table is an **idealized five-exemplar hypothesis contract**, not neural measurements and not a universal characterization of overlapping diagnostic tags.

| Exemplar | dark→observed | observed→dark | observed→observed | ablate U at readout |
|---|---:|---:|---:|---:|
| closed quotient | 0 | 1 | 1 | 1 |
| invariant subspace | 1 | 0 | 1 | 1 |
| latched memory | 0 | 1 | 0 | 1 |
| output register | 1 | 0 | 0 | 1 |
| irrelevant | 0 | 0 | 0 | 0 |

The frozen `freeze_U` column mistakenly modeled a freeze as selective for A. Freezing U cancels both A and B; the physically corrected freeze signature is (1,1,0,1,0). Under that arm the invariant-subspace and register rows coincide across every original intervention, so the original four-arm design has **no separating set**. Amendment C replaces freeze with a finite-radius observed→observed perturbation. The displayed binary table is a synthetic amended design, not measured evidence.

By EvalMath BPD-01 T1's minimum-pair separating-cover calculation, the exact smallest test collection **for this stipulated table** has size three: dark→observed, observed→dark and observed→observed. Real observer types can overlap or have compensating nonlinear backups; measured outcome tables may have no separating set. Keep an explicit unknown/none-fits hypothesis and record unrouted probes as missing.

Every intervention must have its own norm-matched random arm. When repeated effect distributions with variance sigma_e² are **measured**, one can estimate the Chernoff max-min Gaussian KL allocation

\[
\max_{\lambda\ge0,\;\sum_e\lambda_e=1}\min_{h'\ne h}
\sum_e\lambda_e(\mu_{h,e}-\mu_{h',e})^2/(2\sigma_e^2).
\]

**Exact optimal allocation in the synthetic table.** Write the four intervention weights in table order as \(x,y,z,w\), respectively dark→observed, observed→dark, observed→observed and readout ablation, with nonnegative sum one. Under unit-variance independent Gaussian effects with binary means from the *idealized* table, the minimum pairwise squared-effect distance is

\[
\min\{z,\ x+y,\ x+w,\ y+w\}.
\]

If this minimum is \(t\), then \(5t\le 2z+(x+y)+(x+w)+(y+w)=2\); hence \(t\le2/5\). The allocation \((x,y,z,w)=(1/5,1/5,2/5,1/5)\) attains all four constraints, giving exact max-min Gaussian KL \(t/2=1/5\). Therefore the minimum separating cover uses **three types**, while the max-min effect allocation puts positive weight on **all four**. Exactly three distinct size-three subsets separate all five hypothetical rows. The fourth arm can improve the worst-case information rate even when it is redundant for noiseless identification. This is an elementary linear-program result conditional on the stipulated table and noise model, with a checked Fraction solution in theory.py and an integer-scaled upper-bound certificate in MathCan/ObserverChernoff.lean. It is **not** a measured neural Chernoff optimum.

theory.py implements a deterministic 1/20-resolution four-arm grid with exact rational arithmetic. It supplies **no neural estimates**: the necessary measured effect sizes, variances, and route-conditional probabilities are not in the public receipts. KL allocation is conditional on the Gaussian/equal-variance assumptions; categorical/non-Gaussian outcomes require their measured distributions.

## T-D: tradeoff envelopes and rank surfaces

For each fixed candidate i and seed, report (k_i,E_i,b_i), where E is task MSE and b is the normalized B norm on the common card. For the prospective ROC-02 objective define r_i=b_i/m_{b,i}(k), where the denominator is the registered rank/state/horizon-specific median of 128 Haar null B fractions on training/calibration states. Let J_i(lambda)=E_i+lambda*r_i². Undefined null medians make J_i undefined rather than zero. Candidate pair intersections occur at (E_j−E_i)/(r_i²−r_j²) when slopes differ. Filter to intersections on the **actual lower envelope**; otherwise a pairwise crossing can be invisible. The envelope is concave piecewise affine with nonincreasing selected leakage slope as lambda increases. Retain unsupported nondominated points of the full (rank, task error, B norm) surface.

Raw b_i remains a physical descriptive quantity and is published separately from r_i. The inherited public NRF v0.4 retrospective envelope, using its **old unnormalized per-seed leakage squared**, switches at lambda 0.136474, 0.875804, 1.242665 and 1.391717. Those values cannot be assigned to the new normalized-B objective until checkpoint-backed state measurements exist.

## Per-target Lean scope

| Claim | Exact rational search | Paper proof | Lean kernel |
|---|---|---|---|
| finite rank-one separation | explicit four Q² points | finite union of hyperplanes | finite Bool×Bool injectivity |
| full-domain linear rank floor | exact linear examples | matrix rank(WU^T)≤k | pending general matrix rank |
| rotation obstructs rank-two extension | four rational unit directions | all real unit directions | one concrete rank-two nonclosure and rank-one invariance |
| minimum invariant rowspace | nilpotent shift rank tests | Cayley–Hamilton | pending full matrix/submodule span |
| observability-tail lower bound | 540 exact cases d≤6 | recurrence plus Eckart–Young | pending real Frobenius/σ inequality |
| ideal T-C minimum cover | exhaustive subsets | BPD-01 set cover | pending generic finite formalization |
| four-arm Chernoff allocation | exact 0.05 grid | conditional classical KL | pending probability-optimization formalization |
| objective lower envelope | rational intersection algorithm | affine envelope | pending real convex proof |

The Init-only MathCan/ObserverReportCard.lean proves the finite witnesses and an all-depth fiber-compatibility implication, with per-theorem axiom prints. The broad analytic claims above are **written proofs**, not Lean-verified theorems.
