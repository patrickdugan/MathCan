# OLM-02: Collision entropy, flat relational spectra, and Markov matching lifts

Date: 2026-11-15. Companion: [OLM-01](ORBIT_LOCK_DUAL_MIXING.md) and [SMC-02 executable lift](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc01-synchronized-mixing-20261115/research/synchronized_mixing_v1).

**Epistemic scope.** The mathematics below is a self-contained extension of the earlier orbit-lock work; the algebraic identities use elementary finite probability, conditional expectation, group actions, and spectral theory. The synthesis is new to this research campaign. Independent novelty relative to the mathematical literature is **not established**. Exact rational oracles check specified finite cases. There is no claim of a Lean kernel proof, neural training improvement, or proof of either OpenAI source paper.

## Source motivation

* [OpenAI Math #131](https://github.com/openai/math/blob/main/lean/docs/131.md), *Polynomial mixing of the switch chain for every graphical degree sequence* (September 25, 2026), motivates graph-state switching at fixed degrees.
* [OpenAI Math #238](https://github.com/openai/math/blob/main/lean/docs/238.md), *Optimal-order mixing of the Thorp shuffle* (September 26, 2026), motivates the mixing of entire permutation-valued frames rather than only their pointwise marginals.

The lift below uses its **own** lazy random-transposition kernel on permutations. It is neither the original Thorp shuffle nor an application of the reported 1600d asymptotic bound. Its projection is an actual lazy perfect-matching two-edge-switch kernel.

## OLM-02A: Deterministic-factor collision identity

Let S be a random variable with arbitrary strictly positive finite law q on a set H. Let f:H -> X be a deterministic map and X=f(S), with p_x=Pr(X=x). Let J be the joint law of (X,S), and U=p ⊗ q its independent-marginal product law.

**Theorem A (exact finite-time dependence).**

\[
\boxed{\operatorname{TV}(J,U)=1-\sum_x p_x^2.}\tag{A}
\]

The event E={(x,s):x=f(s)} is an optimal positive signed-measure witness. J(E)=1 and U(E)=sum_x p_x². Consequently any classifier inspecting only S or only X has zero advantage between J and U, whereas the single Boolean relational test 1_E obtains precisely (A). In information-theoretic terms, I(X;S)=H(X).

**Proof.** At each s the joint law has mass q_s on (f(s),s) and zero on all incompatible x. The independent law has mass p_x q_s at (x,s). Every compatible atom has signed difference q_s(1-p_{f(s)})≥0 and every incompatible atom has negative signed difference -p_x q_s. Therefore TV, the sum of the positive signed differences, equals sum_s q_s(1-p_{f(s)})=1-sum_x p_x². The conditional entropy H(X|S) vanishes because X=f(S), so I(X;S)=H(X). QED.

This is the **collision-entropy/Gini-Simpson** functional of p. It applies to nonuniform finite-time distributions without group transitivity. Calling it a fundamentally new information identity would overstate priority.

For 0≤ε≤1, define the independent-noise family J_ε=(1-ε)J+εU. Exact scaling of the signed difference gives

\[
\boxed{\operatorname{TV}(J_\epsilon,U)=(1-\epsilon)(1-\sum_x p_x^2).}\tag{B}
\]

E remains an optimal witness, with J_ε(E)=1-ε+ε sum_x p_x².

## OLM-02B: An exact flat canonical-correlation spectrum

Let m be the number of X states with positive mass. With the same notation, form the joint probability matrix J_ε indexed by x,s. Define the q-weighted Gram matrix

\[
M_{xy}=\sum_s\frac{J_\epsilon(x,s)J_\epsilon(y,s)}{q_s}.
\]

**Theorem B (rational Gram identity).**

\[
\boxed{M=(1-\epsilon)^2\operatorname{diag}(p)
+\big(1-(1-\epsilon)^2\big)pp^\top.}\tag{C}
\]

In particular, the normalized conditional-expectation/canonical-correlation matrix

\[
W=\operatorname{diag}(p)^{-1/2}
J_\epsilon\operatorname{diag}(q)^{-1/2}
\]

has exactly one singular value 1 and exactly m-1 singular values 1-ε, with all remaining singular values zero. After removal of the constant mode, the full spectrum is **flat at 1-ε**, independent of q and of the nonuniform p.

**Proof.** Write J_0(x,s)=q_s 1_{f(s)=x}. Then

\[
\sum_s J_0(x,s)J_0(y,s)/q_s
=\delta_{xy}\sum_{s:f(s)=x}q_s
=\delta_{xy}p_x.
\]

The cross terms between J_0 and U=pqᵀ both equal ppᵀ, and the U-U term also equals ppᵀ. Expanding J_ε=(1-ε)J_0+εU gives (C). Congruence with diag(p)^(-1/2) yields

\[
WW^\top=(1-\epsilon)^2I+
\big(1-(1-\epsilon)^2\big)vv^\top,
\qquad v_x=\sqrt{p_x},\quad \|v\|_2=1.
\]

The constant vector v has eigenvalue 1; its orthogonal complement has eigenvalue (1-ε)², proving the singular-value claim. QED.

**Corollary B1.** For any centered real feature a on X with Var_p(a)=1, define b(s)=a(f(s)). Then both features have zero mean and unit variance, and

\[
\mathbb E_{J_\epsilon}[a(X)b(S)]=1-\epsilon.
\]

A full (m-1)-dimensional family of pairwise orthogonal relational feature directions therefore survives with identical strength despite exact equality of the one-coordinate marginals under J_ε and U. For the uniform matching orbit, m=(2k-1)!!, and the centered correlation rank is m-1.

This is a testable target for cross-feature probes. The rank is a population operator rank; it makes no assertion that a learned SAE realizes those directions.

## OLM-02C: A genuine matching-switch Markov lift

Fix k≥2 and the reference perfect matching M₀={(0,1),(2,3),...,(2k-2,2k-1)}. Let T be the set of transpositions that exchange vertices belonging to distinct edges of M₀. Then

\[
|T|=4\binom{k}{2}=2k(k-1).
\]

Choose a hold probability h in (0,1), draw independent increments Z_t with Pr(Z_t=id)=h and Pr(Z_t=τ)=(1-h)/|T| for τ∈T, and define Π_{t+1}=Π_t Z_t, with Π₀=id. Define G_t=Π_t M₀.

**Theorem C (exact Markov projection and persistent orbit lock).**

1. The permutation chain Π_t is irreducible, aperiodic, symmetric, and has unique uniform stationary distribution on S_{2k}.
2. Its graph projection G_t is a Markov chain on the (2k-1)!! perfect matchings, holding with probability h. For each two-edge pair, each of its two alternative reconnections has probability (1-h)/(2 binom(k,2)). This is a lazy uniform two-edge-switch chain on perfect matchings.
3. G_t has uniform stationary distribution on matchings and is irreducible and aperiodic. The joint state remains perfectly locked: G_t=Π_t M₀ almost surely for every t.
4. Writing p_t=Law(G_t), the exact distinguishing advantage from the product of the *time-matched* marginals is

\[
\boxed{D_t=1-\|p_t\|_2^2,}\qquad
D_t \uparrow 1-\frac1{(2k-1)!!}.
\tag{D}
\]

The mutual information is H(G_t) and approaches log((2k-1)!!).

**Proof.** Cross-edge transpositions on M₀ are precisely the edge transpositions of the complete k-partite graph with two vertices per part. This graph is connected for k≥2. Edge transpositions of any connected graph generate the full symmetric group, proving irreducibility. The hold supplies aperiodicity, and each generator is its own inverse, giving a symmetric doubly stochastic transition matrix and uniform stationary distribution.

For a graph G=πM₀, every chosen τ∈T relabels to πτM₀. Hence its graph image depends on G alone. For each pair of matching edges there are four cross swaps, two realizing each reconnection. The projected transition probabilities stated above follow by counting. The graph switch chain is itself symmetric, lazy, and irreducible as a quotient of the irreducible permutation walk, proving its stationary claim. The defining equality gives the orbit lock. Applying Theorem A at every t gives (D). Because the graph kernel is doubly stochastic, convexity of z↦z² (or Jensen's inequality) gives \|p_{t+1}\|₂²≤\|p_t\|₂². Uniform mixing gives p_t→uniform and completes the limit. QED.

Here both marginals are **genuine Markov processes** and are mixing. The joint coupling remains supported on the strict orbit-compatibility subset of the independent product state space, with the TV separation quantified by (D). Uniform marginals alone cannot certify their independence.

For large k, using (2k-1)!!=(2k)!/(2^k k!) and Stirling,

\[
\log_2((2k-1)!!)=k\log_2(2k/e)+\tfrac12+o(1).
\]

The recoverable alignment information grows as Θ(k log k) bits, although the optimal hypothesis test E has only one Boolean output.

## OLM-02D: Complete four-slot finite-time solution

For k=2 and h=1/2, G has three states and its transition matrix has diagonal 1/2, each off-diagonal 1/4. Its nonconstant eigenvalue is 1/4 (multiplicity two). Starting at a fixed matching,

\[
p_t=(1/3,1/3,1/3)
+4^{-t}(2/3,-1/3,-1/3)
\]

(up to labeling). Thus

\[
\boxed{\operatorname{TV}(p_t,U_G)=\frac23\,4^{-t},\qquad
D_t=\frac23(1-16^{-t}).}\tag{E}
\]

The permutation lift on S₄ is the lazy right walk generated by (0 2), (0 3), (1 2), (1 3). Its 24×24 exact symmetric transition matrix R has spectral multiplicities

| Eigenvalue | Multiplicity |
|---:|---:|
| 1 | 1 |
| 3/4 | 8 |
| 1/2 | 6 |
| 1/4 | 8 |
| 0 | 1 |

An executable **exact rational spectral certificate** checks that R(R-I)(R-(1/4)I)(R-(1/2)I)(R-(3/4)I)=0 on every 24 basis row. It separately checks traces tr(R^j) for j=0..4 as 24, 12, 15/2, 21/4, 63/16, which determine the five multiplicities. Symmetry of R rules out other spectrum and Jordan blocks.

Therefore

\[
\operatorname{TV}(\mathcal L(\Pi_t),U_{S_4})
\le \frac{\sqrt{23}}2(3/4)^t.
\]

The full orbit-locked joint distribution tends to the unique locked law J₀, which differs from the independent uniform product in TV by 2/3. The graph-marginal collision discriminant is already 5/8 after one step and reaches 2/3 in the limit. In the exact four-slot experiment the TV distance of the coupled joint to the *uniform* independent product equals 2/3 from sweep 6 onward (an exact finite-state coincidence checked by enumeration), while the permutation marginal continues converging.


## OLM-02E: Gauge-equivariant interventions and one-sided destruction

Let H act transitively on Ω, fix o, and sample S uniformly from H with X=So. The compatibility indicator C(x,s)=1_{x=so} obeys

\[
\boxed{C(\tau x,\tau s)=C(x,s)\quad\text{for every }\tau\in H.}
\]

This is an **exact joint gauge covariance** of the two-coordinate representation. Changing only one coordinate breaks the relation according to the stabilizer geometry:

\[
\Pr[C(\tau X,S)=1]=\frac{|\operatorname{Fix}_{\Omega}(\tau)|}{|\Omega|}.
\tag{F}
\]

**Proof.** Since τ(so)=(τs)o, the compatibility predicate is unchanged when τ is applied simultaneously. Under graph-only intervention, compatibility requires τX=So=X. The orbit variable X is uniform, so the success rate is exactly the fraction of orbit points fixed by τ. QED.

For Ω the perfect matchings on 2k vertices and τ a **single vertex transposition (a b)**, a matching is fixed precisely when (a,b) already belongs to it. A uniformly random matching pairs vertex a with b with probability 1/(2k-1). Hence

\[
\boxed{\Pr[C(\tau X,S)=1]=\frac1{2k-1}.}
\tag{G}
\]

The simultaneously relabeled control passes with probability 1. A *uniform independent full group relabeling* of the graph makes it conditionally uniform for any given S, giving pass rate 1/(2k-1)!!.

This is a direct mechanistic intervention protocol: a gauge-respecting operation preserves relational state, while a one-channel change exposes the hidden dependence. The formula is a pure finite permutation statement; it does not assume learned neural feature gauges.

## OLM-02F: A permanent TV plateau after finitely many steps

For the four-slot lift with k=2,h=1/2, let q_t be the permutation law and let U denote the fixed independent **uniform** law on three matchings × 24 permutations. On the 24 compatible atoms the joint measure J_t has mass q_t(s), while U has mass 1/72. Off the compatibility set J_t is zero.

Thus, if min_s q_t(s) ≥ 1/72, the compatibility event is an optimal total-variation witness and TV(J_t,U)=2/3 exactly. Exhaustive rational evolution shows

\[
\min_s q_6(s)=65/4096 >1/72.
\]

The permutation transition R is doubly stochastic. For any probability vector q, each coordinate of qR is a convex combination of entries of q, so min(qR)≥min(q). Therefore the sufficient inequality holds for **every t≥6**, proving

\[
\boxed{\operatorname{TV}(J_t,U)=2/3\quad\text{for all integers }t\ge6.}
\tag{H}
\]

The separate time-matched product distance D_t=(2/3)(1-16^{-t}) continues increasing toward 2/3. Its finite-time classifier uses the empirical marginals, while (H) compares with the fixed uniform product.

The certificate consists of an exact enumeration at t=6 plus a universal monotonicity argument, establishing the infinite-time assertion from a finite checked seed.

## Verification boundaries

* [collision_spectrum.py](collision_spectrum.py): independent exact-Fraction oracle for Theorems A and B, including arbitrary nonuniform q and all four/six-vertex matching orbits with noise mixtures.
* [test_collision_spectrum.py](../../tests/test_collision_spectrum.py): four regression-test families.
* [SMC-02 transport_lift.py](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc01-synchronized-mixing-20261115/research/synchronized_mixing_v1/transport_lift.py): the actual finite Markov lift, test and spectral polynomial certificate.
* The full general-k proof is by finite group action and counting. The code enumerates k=2,3 only. It does not claim a full Lean formalization or a general-k spectral mixing rate.

The previous SMC-01 shared-quantile experiment remains an independent example: its joint process has conditional coupling defects and a different limiting distribution. The new Markov lift provides the missing exact projection and permanent correlation mechanism without changing that experiment.
