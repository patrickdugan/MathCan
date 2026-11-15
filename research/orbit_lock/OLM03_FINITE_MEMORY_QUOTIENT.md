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


## OLM-03G: Nonuniform finite-horizon frontier and a one-bit overshoot

The uniform theorem admits an exact nonuniform extension that is especially relevant for Markov states *before mixing*.

Let X have any finite law \(p=(p_1,\ldots,p_m)\), and permit a row-stochastic encoder \(K: X\to[r]\). The same argument used in Theorem B makes TV of the joint relative to its product marginals a convex function of K. Its maximum is therefore achieved at some deterministic partition \(h\). By the deterministic-factor collision identity,

\[
\boxed{D_{\max}(p,r)=
1-\min_{h:\{1,\dots,m\}\to[r]}
\sum_{z=1}^{r}\left(\sum_{x:h(x)=z}p_x\right)^2.}
\tag{G}
\]

**Proof.** For fixed p, both the joint law \(p_x K(z\mid x)\) and product law \(p_x \sum_y p_y K(z\mid y)\) depend linearly on K. Their TV is a convex function of K. Decomposing K as a mixture of deterministic row assignments shows some deterministic h attains at least its value. For each h, X determines Z=h(X), so OLM-02A gives TV \(1-\sum_zP(Z=z)^2\). Minimizing the indicated collision sum over partitions proves (G). QED.

For r=2, write \(q=\sum_{x\in A}p_x\). Then

\[
D_{\max}(p,2)=\max_{A\subseteq[m]}2q(1-q)
=\frac12-2\min_{A\subseteq[m]}(q-\tfrac12)^2.
\tag{H}
\]

Thus the exact optimal one-bit code is a **closest-to-half weighted subset-sum**. This shows where the finite-horizon oracle becomes combinatorial even though its dependence certificate is elementary. It is implemented in the bounded exact-rational [weighted_frontier.py](weighted_frontier.py) for at most 20 input states.

### Application to the actual four-vertex matching-switch chain

For the SMC-02 projected graph chain, start from one fixed matching and let \(c=4^{-t}\). The three matching probabilities at step t are

\[
p_t=(a,b,b),\quad a=\frac{1+2c}{3},\quad b=\frac{1-c}{3}.
\]

A two-code partition has one singleton and one pair. Comparing their collision sums shows that isolating the most likely state a is optimal, because

\[
[a^2+(2b)^2]-[b^2+(a+b)^2]=2b(b-a)\le0.
\]

Consequently

\[
\boxed{D_{\max}(p_t,2)=
\frac49\left(1+4^{-t}-2\cdot16^{-t}\right).}
\tag{I}
\]

Compare the **uncompressed** time-matched relation
\(D_{\mathrm{full}}(t)=\frac23(1-16^{-t})\), which increases strictly in t. The one-bit optimum is nonmonotone. As a function of \(c\in[0,1]\), the derivative of \(\frac49(1+c-2c^2)\) is \(\frac49(1-4c)\), so its maximum is precisely at \(c=1/4\), namely **after one switch**:

| Time | Optimal one-bit joint TV | Optimal detector balanced accuracy | Full relational TV |
|---:|---:|---:|---:|
| 0 | 0 | 1/2 | 0 |
| 1 | 1/2 | 3/4 | 5/8 |
| 2 | 15/32 | 47/64 | 85/128 |
| 3 | 231/512 | 743/1024 | 1365/2048 |
| infinity | 4/9 | 13/18 | 2/3 |

A single fixed encoder isolates the original matching at every t; the comparison above proves it remains optimal throughout the trajectory. The capacity inversion therefore persists even without changing the encoder between depths.

At t=1 the one-bit code can split the graph law into masses 1/2 and 1/2. Later mixing makes three states equiprobable, and no deterministic two-bin partition can achieve that balance. The *information available to a one-bit relational detector* decreases as the underlying graph continues mixing, despite growth in the uncompressed dependence.

The same exact subset-sum computation at six vertices gives one-bit TV = 1/2 at t=1, because the graph occupies the initial matching with probability 1/2 and six alternative matchings with probability 1/12 each. Its stationary one-bit optimum is 112/225. Further time steps are finite-rational optimization questions and are evaluated separately in SMC-03.

This identifies a concrete recurrent-training failure mode: comparing latent probes at unequal loop depths without controlling code capacity can invert the apparent direction of retained relational information. These are finite Markov statements; no general claim about transformer training is inferred.



## OLM-03H: Why a shared-edge neural readout is a complete orbit detector

Let E be the set of all \(N=\binom{2k}{2}\) unordered vertex pairs. For perfect matchings \(G,H\) on 2k vertices, fix **any** local edge score \(\phi:\{0,1\}^2\to\mathbb R\), and define the permutation-pooled readout

\[
S_\phi(G,H)=b+\sum_{e\in E}\phi(\mathbf1_{e\in G},\mathbf1_{e\in H}).
\]

**Theorem H (exact two-parameter reduction and gauge covariance).** Put \(c=|G\cap H|\) and \(\phi_{ab}=\phi(a,b)\). Then

\[
\boxed{S_\phi(G,H)=A+\Delta c,\quad
A=b+k(\phi_{10}+\phi_{01})+(N-2k)\phi_{00},\quad
\Delta=\phi_{11}-\phi_{10}-\phi_{01}+\phi_{00}.}
\tag{J}
\]

For every simultaneous vertex relabeling \(\tau\in S_{2k}\),

\[
\boxed{S_\phi(\tau G,\tau H)=S_\phi(G,H).}
\tag{K}
\]

If \(G\ne H\) then \(c\le k-2\). Therefore whenever \(\Delta>0\), a threshold strictly between \(A+\Delta(k-2)\) and \(A+\Delta k\) recognizes \(G=H\) perfectly. The compatibility and nearest-incompatible scores are separated by **\(2\Delta\)**.

**Proof.** Because each perfect matching has exactly k edges, the four local edge-type counts are

\[
n_{11}=c,\quad n_{10}=k-c,\quad n_{01}=k-c,\quad
n_{00}=N-2k+c.
\]

Substitute them into the edge sum and collect constants and terms in c to obtain (J). A vertex permutation bijects the edge set E and simultaneously preserves both membership indicators, so reindexing the sum proves (K). Finally, if two perfect matchings shared k-1 edges, their only remaining two vertices would have to be paired to each other in both matchings; hence they would share the last edge too. Distinct matchings share at most k-2, giving the gap. QED.

**Consequence for SMC-03c.** The 34-parameter shared-edge model learns \(\phi\) through a nonlinear eight-unit local MLP, but restricted to the matching-pair data manifold its entire output depends on only **two effective real quantities**, A and \(\Delta\). Its excellent unseen-matching accuracy is consistent with this exact structural reduction. The 34 parameters measure the implemented training degrees of freedom, while the orbit-restricted function class is two-dimensional. The transport of the reference matching remains an architectural input. This result makes the trained control interpretable without crediting the model with discovering a hidden group action.

