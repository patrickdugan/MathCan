# OLM-01: Orbit-locked information in two mixing observables

**Date:** November 15, 2026. **Status:** finite theorems with self-contained proofs and exact-rational enumeration. Novelty relative to the wider literature has not been established; this is an original synthesis for the research program. No Lean formalization of these new claims is asserted.

## Source pair and attribution

The two external mathematical inputs are from the October 2026 OpenAI release, at source commit [4eaee875](https://github.com/openai/math/commit/4eaee87548250b2682affda7d05d947c05554bae).

* **#131, Polynomial mixing of the switch chain for every graphical degree sequence** (September 25, 2026): [paper](https://github.com/openai/math/blob/main/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf) and [Lean scope](https://github.com/openai/math/blob/main/lean/docs/131.md). Its selected formalization includes the lazy simple-graph switch chain, connectivity, a TV mixing-time bound of at most \(2n^8\) at TV threshold \(1/4\), and a spectral-gap estimate. The paper's exact sampler lies outside those selected statements.
* **#238, Optimal-order mixing of the Thorp shuffle** (September 26, 2026): [paper](https://github.com/openai/math/blob/main/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf) and [Lean scope](https://github.com/openai/math/blob/main/lean/docs/238.md). It reports full-permutation mixing in \(\Theta(d)\) physical shuffles on \(2^d\) cards. Its selected formalizations include the asymptotic \(1600d\) upper statement and individually scoped auxiliary results.

The present work neither reproduces those lengthy proofs nor transfers their asymptotic constants to a toy experiment.

## OLM-1: sharp orbit-lock and information theorem

Let a finite group \(H\) act transitively on a finite set \(\Omega\) with cardinality \(m\). Fix \(o\in\Omega\), draw \(S\) uniformly from \(H\), and set \(X=S\cdot o\). Write \(J_0=\mathcal L(X,S)\) and \(U=\operatorname{Unif}(\Omega)\otimes\operatorname{Unif}(H)\). With \(0\le\epsilon\le1\), put \(J_\epsilon=(1-\epsilon)J_0+\epsilon U\).

**Proposition OLM-1.** Each coordinate marginal of \(J_\epsilon\) is uniform, while

\[
\operatorname{TV}(J_\epsilon,U)=(1-\epsilon)(1-1/m).
\tag{1}
\]

The joint Boolean observer \(A=\{(x,s):x=s\cdot o\}\) attains the total-variation difference, since \(J_\epsilon(A)=1-\epsilon+\epsilon/m\) and \(U(A)=1/m\). All single-coordinate tests have distinguishing advantage zero.

**Proof.** For every \(x\in\Omega\), the orbit map \(s\mapsto s\cdot o\) has exactly \(|H|/m\) preimages, by transitivity and equal stabilizer cardinality. Thus \(X\) is uniform. The locked law puts mass \(1/|H|\) on each compatible pair and zero on every incompatible pair. The product law puts mass \(1/(m|H|)\) on every pair. Summing the positive signed difference over the \(|H|\) compatible pairs gives \(1-1/m\), which equals total variation. The noisy mixture scales the signed difference by \(1-\epsilon\). The event \(A\) collects exactly the positive part and is an optimal event witness. Equality of marginals completes the proof.

The conditional law of \(X\) given \(S=s\) assigns probability \(a=1-\epsilon+\epsilon/m\) to \(s\cdot o\) and \(b=\epsilon/m\) to each of the \(m-1\) other elements. The unconditional law is uniform, so the mutual information in natural units is

\[
I(X;S)=\log m+a\log a+(m-1)b\log b,
\tag{2}
\]

where \(0\log0=0\). This gives an exact information accounting for a relational feature erased by marginal-only observation.

## OLM-2: the perfect-matching instance

Let \(H=S_{2k}\) act on all perfect matchings of \(2k\) labeled vertices. The action is transitive: any bijection between the \(k\) edge pairs extends to a vertex permutation. Pairing the smallest available vertex leaves \(2k-1\) choices followed by the smaller matching problem, giving

\[
m_0=1,\qquad m_k=(2k-1)m_{k-1}=(2k-1)!!.
\]

Substituting into (1),

\[
\boxed{\operatorname{TV}(J_\epsilon,U)
=(1-\epsilon)\left(1-\frac{1}{(2k-1)!!}\right).}
\tag{3}
\]

With four vertices (\(m=3\)), the locked distance is \(2/3\), dropping to \(1/2\) at \(\epsilon=1/4\). With six vertices (\(m=15\)), it is \(14/15\), dropping to \(7/10\). In every case both marginals have exact TV zero. The compatible-pair observer is one bit of relational information.

**Scope:** (3) describes a family of joint snapshot laws. It does not claim that the orbit-derived graph coordinate runs the exact switch chain or that the card coordinate runs the original Thorp kernel.

## OLM-3: dynamic certificate for synchronized random seeds

Let \(P,Q\) be finite Markov kernels on state spaces \(E,F\) with stationary distributions \(\pi,\sigma\). Let \(L=P\otimes Q\) be their independent product kernel, with stationary \(U=\pi\otimes\sigma\). A joint kernel \(K\) on \(E\times F\) is assumed to have conditional coordinate transition marginals \(P(x,\cdot)\), \(Q(y,\cdot)\) from every current state \((x,y)\). Measure its failure of conditional independence by

\[
\eta=\max_{z\in E\times F}\operatorname{TV}(K(z,\cdot),L(z,\cdot)).
\]

Start at the deterministic \((x_0,y_0)\), and write \(a_t=\operatorname{TV}(P^t(x_0,\cdot),\pi)\) and \(b_t=\operatorname{TV}(Q^t(y_0,\cdot),\sigma)\).

**Proposition OLM-3.** For all \(t\ge0\),

\[
\max(a_t,b_t)\le
\operatorname{TV}(P^t(x_0,\cdot)\otimes Q^t(y_0,\cdot),U)
\le a_t+b_t-a_tb_t
\]

and

\[
\boxed{\operatorname{TV}(\delta_{(x_0,y_0)}K^t,U)
\le\min\{1,a_t+b_t-a_tb_t+t\eta\}.}
\tag{4}
\]

For any block \(b\ge1\), set \(\rho_b=\max_{z,w}\operatorname{TV}(L^b(z,\cdot),L^b(w,\cdot))\). If \(\rho_b<1\), then for \(t=kb+r\), \(0\le r<b\), and \(D_0=\operatorname{TV}(\delta_{(x_0,y_0)},U)\),

\[
\boxed{\operatorname{TV}(\delta_{(x_0,y_0)}K^t,U)
\le \min\left\{1,\rho_b^kD_0+
b\eta\sum_{j=0}^{k-1}\rho_b^j+r\eta\right\}.}
\tag{5}
\]

**Proof.** Coordinate projection contracts TV, which gives the lower product bound. Take independent optimal couplings of the two coordinate distributions to their respective stationary laws. Both coordinate couplings succeed with probability \((1-a_t)(1-b_t)\), yielding the upper product bound. The conditional marginal property of \(K\) preserves the correct marginal laws at every step. A telescoping replacement of each occurrence of \(K\) by \(L\), using contraction of TV under a Markov kernel, gives \(\operatorname{TV}(\delta_zK^t,\delta_zL^t)\le t\eta\). The triangle inequality proves (4). Over a block of \(b\) steps, the same replacement costs at most \(b\eta\). Dobrushin contraction of \(L^b\) towards \(U\) gives \(D_{(j+1)b}\le\rho_b D_{jb}+b\eta\). Solving this recurrence and treating the remaining \(r\) steps by nonexpansiveness yields (5). QED.

This separates individual mixing (as in #131 and #238) from the *joint independence* premise required for a product-mixing conclusion. The proof uses standard coupling and contraction ingredients in an orbit-lock application; no new universal mixing exponent is claimed.

## Exact verification and continuation

Run from the MathCan root:

    python research/orbit_lock/oracle.py
    python -m unittest discover -s tests -p 'test_orbit_lock.py' -v

The pure oracle enumerates all \(24\) permutations and \(3\) matchings at four vertices, and all \(720\) permutations and \(15\) matchings at six vertices. It checks all joint entries, both marginals, the optimal distinguishing event and noisy cases \(\epsilon=0,1/4,1/2,1\). Four unit tests passed locally.

The applied companion in [Compactification-Theory](https://github.com/MoralityLabAI/Compactification-Theory) instantiates (4)-(5) with a four-vertex lazy switch kernel, a toy binary-cube permutation sweep, and exact shared-quantile coupling. It has its own runnable tests and results. Future formal work can encode OLM-1 through OLM-3 in Lean and audit their axiom inventory. A trained-model SAE implementation remains an experimental question.
