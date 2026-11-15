# OLM-03: Sharp relational-memory frontiers, exact orbit quotients and precision

Date: 2026-11-15. Continues [OLM-01](ORBIT_LOCK_DUAL_MIXING.md) and [OLM-02](OLM02_COLLISION_SPECTRUM_LIFT.md), motivated by OpenAI Mathematics [#131](https://github.com/openai/math/blob/main/lean/docs/131.md) (degree-preserving graph mixing) and [#238](https://github.com/openai/math/blob/main/lean/docs/238.md) (permutation mixing). The applied companion is [SMC-03](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc01-synchronized-mixing-20261115/research/synchronized_mixing_v1).

**Status:** Self-contained finite-probability proofs and reproducible exact-rational computations. Their combination for this research program is new here; mathematical priority relative to the literature has not been established. In particular, no Lean kernel verification of OLM-03 or pretrained-transformer evaluation is claimed.

## OLM-03A: A universal finite-alphabet dependence ceiling

For arbitrary jointly distributed finite variables X,Z, let p_x=P(X=x), q_z=P(Z=z), with m,r positive-probability states respectively, and write J for their joint law.

**Proposition A.**

\[
\boxed{\operatorname{TV}(J,p\otimes q)
\le1-\max\left\{\sum_x p_x^2,\sum_z q_z^2\right\}
\le1-\frac1{\min(m,r)}.}
\tag{A}
\]

**Proof.** TV is one minus the overlap \(\sum_{xz}\min(J_{xz},p_xq_z)\). Since \(J_{xz}\le q_z\), we have \(p_xq_z\ge p_xJ_{xz}\), and also \(J_{xz}\ge p_xJ_{xz}\). Therefore \(\min(J_{xz},p_xq_z)\ge p_xJ_{xz}\). Summing gives overlap at least \(\sum_xp_x^2\). Interchanging x,z gives overlap at least \(\sum_zq_z^2\). Cauchy-Schwarz implies those collision sums are at least \(1/m\) and \(1/r\). QED.

The last bound uses the *number of distinguishable output symbols*, rather than network width or dimension. Continuous outputs require a precision budget or a distinct finite-code constraint before it applies.

## OLM-03B: Sharp frontier for uniform state and any stochastic encoder

Let X be uniform over m states. An encoder is *any* row-stochastic channel \(K(z\mid x)\), with at most r output symbols, \(1\le r\le m\). Define

\[
D(K)=\operatorname{TV}(\mathcal L(X,Z),\mathcal L(X)\otimes\mathcal L(Z)).
\]

Write \(m=ar+s\), \(0\le s<r\).

**Theorem B (exact finite-memory optimum).**

\[
\boxed{\max_K D(K)
=1-\frac{(r-s)a^2+s(a+1)^2}{m^2}.}
\tag{B}
\]

An encoder that sends each input to one of r bins, with s bins of size a+1 and r-s bins of size a, attains the maximum. This is sharp even allowing randomized encoders.

**Proof.** With uniform X, the signed measure at (x,z) equals \((K(z|x)-q_z)/m\), where \(q_z=m^{-1}\sum_xK(z|x)\). Thus
\(D(K)=(2m)^{-1}\sum_{x,z}|K(z|x)-q_z|\), a convex function of K. Every row-stochastic finite channel is a convex combination of deterministic channels: independently sample a destination for each row, and take the resulting random deterministic function. By convexity, the maximum over all channels is achieved at a deterministic function h.

For Z=h(X), OLM-02A's deterministic-factor collision identity (applied with X as the seed and Z as the factor) gives \(D(h)=1-\sum_zq_z^2=1-m^{-2}\sum_z n_z^2\), where \(n_z=|h^{-1}(z)|\) and \(\sum_z n_z=m\). Replacing two nonnegative counts that differ by at least two with counts one unit closer reduces the sum of squares by \(2(|n_i-n_j|-1)>0\). The minimum is therefore attained by exactly the balanced sizes a and a+1, proving (B). QED.

An independent-noise mixture \(J_\epsilon=(1-\epsilon)J+\epsilon(p\otimes q)\) scales the optimal advantage by \(1-\epsilon\); the maximum balanced classification accuracy with equal class priors is

\[
\boxed{A_{\mathrm{det}}(m,r,\epsilon)
=\frac12\left[1+(1-\epsilon)D_{\max}(m,r)\right].}
\tag{C}
\]

This is an information-theoretic population bound, rather than a prediction about training convergence.

## OLM-03C: Optimal reconstruction requires an almost-full codebook

For any such channel, the optimal Bayes recovery probability of the *entire* X from Z is

\[
P_{\mathrm{MAP}}=\sum_z\max_xP(X=x,Z=z)\le\frac rm.
\tag{D}
\]

**Proof.** Each joint cell is \(m^{-1}K(z|x)\le1/m\), and the decoder can select at most one cell per output z. A deterministic surjection onto r codes attains equality, including the balanced maximizer above. QED.

More strongly, if a deterministic compressed representation \(c(S)\) of a permutation S must answer the compatibility predicate \(G=SM_0\) **for every** permutation S and every matching G, then c requires at least as many distinct outputs as there are matchings. Suppose c(S)=c(T) with SM0≠TM0. A decoder with input \(G=SM_0\) sees the same code for S and T but needs opposite Boolean answers. Contradiction. The quotient map \(c(S)=SM_0\) achieves the lower bound.

For perfect matchings on 2k labeled vertices, the stabilizer of M0 permutes the k edges and independently flips each endpoint pair. It has size \(2^k k!\). Orbit-stabilizer gives

\[
|\Omega|=\frac{(2k)!}{2^k k!}=(2k-1)!!.
\tag{E}
\]

Thus the exact compatibility state needs \(\lceil\log_2( (2k-1)!! )\rceil\) bits, compared with \(\lceil\log_2((2k)!)\rceil\) bits for an unconstrained full permutation ID. At 6 vertices, these are **4 bits versus 10 bits**; at 8 vertices, **7 bits versus 16 bits**.

This is a lossless *task-relative quotient* of the permutation for compatibility queries. Other tasks may require the information discarded by this quotient.

## OLM-03D: Exact numerical frontier at six vertices

There are m=15 matchings. The following values are exact fractions computed by [finite_memory.py](finite_memory.py).

| Distinct codes r | Min binary bits | Maximum TV | Optimal balanced detector accuracy | Exact matching MAP recovery |
|---:|---:|---:|---:|---:|
| 1 | 0 | 0 | 1/2 | 1/15 |
| 2 | 1 | 112/225 | 337/450 | 2/15 |
| 3 | 2 | 2/3 | 5/6 | 1/5 |
| 4 | 2 | 56/75 | 131/150 | 4/15 |
| 5 | 3 | 4/5 | 9/10 | 1/3 |
| 8 | 3 | 196/225 | 421/450 | 8/15 |
| 15 | 4 | 14/15 | 29/30 | 1 |

A one-bit code can preserve about 49.78% joint TV, supporting about 74.89% balanced relational detection, while the optimal *exact matching reconstruction* rate is only 2/15. This distinguishes preserving a low-cost dependence detector from preserving the complete hidden state.

The code exhaustively scans all deterministic encoders up to m=5,r=4 and verifies rational stochastic channels for m=4,r=2. The general optimum follows from the proof, not the finite search.

## OLM-03E: A rank-two code trades dimension for precision

For m≥3, label m matching states by j=0,...,m-1 and assign each a two-dimensional circular code

\[
u_j=(\cos(2\pi j/m),\sin(2\pi j/m)).
\]

The bilinear score \(u_i\cdot u_j\) is 1 for matching labels and at most \(c_m=\cos(2\pi/m)\) for distinct labels. A fixed threshold \(T_m=(1+c_m)/2\) therefore perfectly recognizes compatibility using only **two real-valued coordinates per label**.

For componentwise rounding to b fractional binary bits, each coordinate incurs absolute error at most \(\delta=2^{-b-1}\). Bilinear expansion and \(|u_{j,\ell}|\le1\) show that each dot product changes by at most \(4\delta+2\delta^2\). Hence the following sufficient condition guarantees the same classification for every codeword pair:

\[
\boxed{
2^{1-b}+2^{-2b-1}<
\frac{1-\cos(2\pi/m)}2.
}
\tag{F}
\]

The ideal separation margin is \(\Theta(m^{-2})\); this sufficient bound needs \(b=2\log_2m+O(1)\) fractional bits. Two signed fixed-point coordinates with the representable range [-1,1] require 2(b+2) bits under a straightforward two's-complement storage scheme. The [numeric diagnostic](finite_memory.py) finds a sufficient b=6 for m=15 (16 bits stored), compared with the four-bit indexed orbit quotient. For m=105, it finds b=12. The code uses standard floating-point trigonometry; these integer threshold *evaluations* are numerical checks of the analytic sufficient inequality, not interval-arithmetic certificates for transcendental values.

Low continuous feature dimension is therefore compatible with many discrete labels, at a growing precision cost. A model with finite quantized activations must track both dimensions and actual representable levels. This furnishes a synthetic depth/precision probe target for Compactification-Theory.

**Gauge scope:** the circular code depends on an arbitrary but fixed ordering of matchings. The equality *decision* is invariant under simultaneously relabeling both matching IDs; individual dot-product scores for unequal pairs can change under arbitrary relabeling.

## OLM-03F: Proper-loss obstruction for additive monitors

Consider equal-prior classification of J=Law(X,S) versus U=Law(X)⊗Law(S). Since each coordinate marginal is identical in both classes, the population gradient of binary logistic risk at zero logit vanishes for every additive feature \(a(X)+b(S)+c\). Indeed \(\partial \ell/\partial\theta=\mathbb E[(\sigma(0)-Y)\phi]\), and class-conditional means of every additive \(\phi\) agree. Logistic risk is convex in the additive weights, so the zero-logit model is a global log-loss minimizer and has 50% balanced accuracy at a constant decision threshold.

The statement applies to **population-optimal logistic training within an additive model**. It is not a universal 0-1 accuracy bound for all additive threshold functions: those can exploit some correlation at the cost of a worse log-loss. A multiplicative relational feature such as \(\langle A_G,A_{SM_0}\rangle\) removes this particular obstruction.

## Verification and experimental connection

* [finite_memory.py](finite_memory.py) supplies exact Fraction distributions, exhaustive small encoders, collision and MAP checks, matching stabilizer sizes, and a separate floating-point code-precision diagnostic.
* [tests/test_orbit_memory.py](../../tests/test_orbit_memory.py) contains five independent regression families.
* [SMC-03](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc01-synchronized-mixing-20261115/research/synchronized_mixing_v1) compares a raw 51-input MLP with a structured relational feature under a permutation-fiber-disjoint train/test split. The learned experiment is a synthetic CPU test and makes no pretrained-model claim.

The sharp finite-memory and reconstruction bounds require a **finite output alphabet or explicit quantization**, so a continuous vector representation cannot be treated as an r-symbol code merely because it has r coordinates.
