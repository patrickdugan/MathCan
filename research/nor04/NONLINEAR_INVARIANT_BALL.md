# NOR-04: an all-depth nonlinear compactification from a validated invariant ball

**Date:** November 15, 2026. **Status:** Banach fixed-point and finite \(L_p\) compactification theorem with a complete written proof, plus a **passed exact-rational trained-GRU invariant-ball certificate** from [GitHub Actions run 43691939525](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43691939525). The analytic Banach and Gaussian arguments remain paper-level. Literature priority is unverified. The external mathematical inputs are OpenAI Math #094 and #325, pinned in NOR-01/02.

## The validated-ball theorem

Let \(F:U\to U\) be \(C^1\) on an open subset of a real Hilbert space \(\mathbb R^n\). Fix \(L\ge1\), write \(G=F^L\), and suppose the closed Euclidean ball
\[
B=B(c,R)\subseteq U,\qquad R>0,
\]
is convex. Assume a **uniform, independently certified** operator-norm bound
\[
\sup_{h\in B}\|DG(h)\|_2\le K<1,
\]
and a center residual \(s\ge\|G(c)-c\|_2\) satisfying
\[
\boxed{s+KR\le R.}\tag{1}
\]

**Theorem 1 (true nonlinear infinite-horizon contraction).** The full nonlinear block map \(G\) sends \(B\) into itself, has a unique fixed point \(p\in B\), and for all \(x,y\in B\) and \(m\ge0\),
\[
\|G^m x-G^m y\|_2\le K^m\|x-y\|_2,\qquad
\|G^m x-p\|_2\le K^m\|x-p\|_2.
\]
Moreover \(\|p-c\|_2\le s/(1-K)\). These conclusions hold for arbitrarily many blocks of the *actual nonlinear map*. The point \(p\) is a fixed point of \(F^L\); it may be a periodic point of \(F\) with period dividing \(L\).

*Proof.* For \(x\in B\), the mean value integral along the segment \([c,x]\) yields \(\|G(x)-G(c)\|\le K\|x-c\|\). Thus \(\|G(x)-c\|\le KR+s\le R\). For \(x,y\in B\), the same mean value formula along \([x,y]\) gives \(\|G(x)-G(y)\|\le K\|x-y\|\). Since the closed Euclidean ball is complete, Banach's contraction theorem provides a unique fixed point \(p\in B\), and iteration of the inequality gives the asserted estimates. At the fixed point, \(\|p-c\|\le K\|p-c\|+s\); rearrange because \(K<1\). \(\square\)

### Interval source of the hypotheses

Suppose an exact rational box \(I_0=\prod_i[c_i-R,c_i+R]\) encloses \(B\). Propagate this box through all \(L\) GRU steps using real-analytic outward-rounded rational interval arithmetic, and compute interval enclosures \(\mathbf J_j\) for each derivative \(DF\) on the resulting state box. Then the interval matrix product
\[
\mathbf A=\mathbf J_{L-1}\cdots\mathbf J_0
\]
contains \(DG(x)\) entrywise **for every** \(x\in B\). Let \(C_{ik}=\max(|\underline{\mathbf A}_{ik}|,|\overline{\mathbf A}_{ik}|)\). Then
\[
\boxed{\sup_{x\in B}\|DG(x)\|_2
\le\left(\sum_{ik}C_{ik}^2\right)^{1/2}.}\tag{2}
\]
The same uniform bound may be obtained from a midpoint rational matrix product with a validated telescoping error. Taking the smaller of two independently sufficient bounds preserves validity. Evaluating \(G(c)\) with a separate rational interval trace produces a validated upper bound \(s\) and closes the arithmetic obligations (1)–(2). The proof covers actual trained-decimal real weights and **all initial points in the stated ball**. The real-valued analytic model is specified separately from finite-precision floating inference.

### Novel nonlinear finite-history \(L_p\) corollary

Fix \(1<p_0<\infty\), \(p_0\ne2\), \(D>1\), \(T\ge1\), and \(x\in B\). By Theorem 1, for every \(m\ge T\),
\[
\|G^m x-p\|_2\le 2RK^T.
\]
Use the normalized Gaussian isometry from a real finite-dimensional Hilbert space into real \(L_{p_0}\), then apply OpenAI Math #094 to the \(T+1\) points
\[
\{p,x,Gx,\ldots,G^{T-1}x\}.
\]
There exist images in \(\ell_{p_0}^d\) of distortion at most \(D\), with
\[
d\le\exp\!\big(C_{p_0,D}(\log(T+1))^{\gamma(p_0)}\big),\qquad
\gamma(p_0)=\begin{cases}2-p_0,&1<p_0<2,\\1-2/p_0,&p_0>2.\end{cases}
\]
Translate the image of \(p\) to zero and use it to encode every unobserved block state at time \(m\ge T\). Let \(E_T\) be the maximum additive distance error among the first \(T\) points and anchor \(p\). The exact NOR-01 stitching argument now gives
\[
\boxed{
\sup_{i,j\ge0}
\left|
\|\hat x_i-\hat x_j\|_{p_0}
-
\|G^i x-G^j x\|_2
\right|
\le E_T+4RK^T .
}\tag{3}
\]
This is an **infinite-horizon result for an actual nonlinear recurrent system** restricted to its certified invariant ball. The point \(p\) and the low-dimensional embedding in (3) are existential; the computational experiment certifies a rational ball around \(p\) and does not construct the #094 optimal embedding.

For the explicitly known center \(c\) as the clipping anchor, the recurrence also yields
\[
\|G^m x-c\|_2
\le K^m\|x-c\|_2+s\frac{1-K^m}{1-K}.
\]
This gives a computable center-relative approximation with an irreducible residual floor \(s/(1-K)\) if the unknown fixed point is replaced by \(c\).

### Connection to complete Crouzeix

OpenAI Math #325 supplies the sharp constant-2 matrix-valued polynomial bound for the frozen derivative \(DG(p)\). When an enclosing numerical-range disk \(D(a,b)\) has \(a,b>0\), \(q=a+b<1\), NOR-02's exposed-point filter yields a stronger \(q^t t^{-r/2}\) estimate on the *linearized* orbit and noncommuting readout channels. The new invariant-ball argument is what upgrades stability to the **actual repeatedly applied nonlinear block**; the uniform \(K<1\) in Theorem 1 is a sufficient, independently checked norm condition. Merely verifying \(w(DG(c))<1\) at the center cannot replace it.

## Applied candidate and verification boundaries

Companion implementation in [Compactification-Theory NOR-04](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor01-numerical-orbit-sketch-20261115/research/nor01_numerical_orbit_sketch):

- Original source-locked 1,000-parameter, 12-hidden-coordinate RRC-25 GRU, zero-input transition.
- Proposed center: a twelve-vector of 17-decimal rational coordinates obtained by a long nominal zero-input replay and Newton polishing. It is **a supplied candidate**, independent of the interval proof.
- Proposed radius \(R=10^{-11}\), 12 zero-input GRU transitions per block. All exact interval decisions use rational inequalities and a separate norm bound on the whole ball.
- The independent [NOR-04 GitHub Actions audit](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43691939525) passed. It certified \(K\le928242792263/10^{12}=0.928242792263\) and \(s\le237277631/(2\cdot10^{23})=1.186388155\times10^{-15}\) at \(R=10^{-11}\). The exact invariance margin is \(143277137843/(2\cdot10^{23})=7.16385689215\times10^{-13}>0\). The pointwise block numerical-range disk has upper radial value \(q=0.937877390996\). Every stated bound is specific to the frozen checkpoint and real-valued rational-lift model. Four focused regression tests passed. The machine-readable receipt is [committed with the gym](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/nor01-numerical-orbit-sketch-20261115/research/nor01_numerical_orbit_sketch/results/nor04_invariant_ball.json).
- The interval proof establishes a local basin of radius \(10^{-11}\); no input-conditioned held-out GRU state is presumed to enter that ball. The certified fixed point is for \(F^{12}\), with period-one status requiring an additional argument.

The pure-math theorem has a human-readable proof. The user's Init-only Lean modules NOR-01/02/03 establish finite arithmetic stitching and shadowing lemmas, while general Banach fixed-point and infinite-dimensional Gaussian \(L_p\) statements remain paper-level mathematics.
