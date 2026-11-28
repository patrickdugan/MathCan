# NOR-01: numerical-range orbit stitching across finite \(L_p\) sketches

**Status:** new mathematical derivation with a written proof; priority relative to the literature has not been established. The finite stitching lemma is formalized over integer-valued metrics in `MathCan/OrbitStitching.lean`. The analytic statements are conditional on the two cited OpenAI results. Their theorems and Gaussian analysis are outside the MathCan kernel-checking scope.

## Source pair, frozen at openai/math `4eaee87548250b2682affda7d05d947c05554bae`

- OpenAI Math **#094**, *Subpolynomial dimension reduction in Lp* (September 23, 2026), [LaTeX source](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Subpolynomial-dimension-reduction-in-Lp-September-23-2026/build/paper.tex). For fixed \(1<p<\infty\), \(p\ne2\), \(D>1\) and \(N\ge2\), every \(N\)-point subset of real \(L_p\) has a distortion-\(D\) embedding into \(\ell_p^d\) with \(d\le\exp(C_{p,D}(\log N)^{\gamma(p)})\), where \(\gamma(p)=2-p\) for \(p<2\) and \(\gamma(p)=1-2/p\) for \(p>2\). The theorem is existential; its constant depends on \(D\).
- OpenAI Math **#325**, *A direct proof of the complete Crouzeix inequality* (September 26, 2026), [LaTeX source](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex). For \(A\in M_m(\mathbb C)\) and a scalar polynomial \(P\), \(\|P(A)\|\le2\max_{z\in W(A)}|P(z)|\).

The two results have different domains: the operator theorem uses a Hilbert norm, while the dimension theorem reduces finite sets of real \(L_p\). The Gaussian bridge below addresses this precisely.

## Numerical-range orbit stitching theorem

Let \(A\in M_m(\mathbb R)\) satisfy \(W_{\mathbb C}(A)\subseteq\{z:|z|\le q\}\) for \(0\le q<1\). Fix \(x\in\mathbb R^m\), \(T\ge1\), \(1<p<\infty\), \(p\ne2\), and \(D>1\). Put \(x_t=A^t x\) and \(N=T+1\).

**Theorem (NOR-01).** There are vectors \(y_0,\ldots,y_{T-1}\in\ell_p^d\) with a common zero anchor, for

\[
d\le \exp\left(C_{p,D}(\log(T+1))^{\gamma(p)}\right),
\]

such that the time-indexed clipped observation \(z_t=y_t\) when \(t<T\) and \(z_t=0\) when \(t\ge T\) satisfies, for every pair of times,

\[
\boxed{\left|\|z_s-z_t\|_p-\|x_s-x_t\|_2\right|
\le4(D-1+q^T)\|x\|_2.}
\]

A finer a posteriori bound is \(E_T+4q^T\|x\|_2\), with

\[
E_T=\max_{u,v\in\{0,x_0,\ldots,x_{T-1}\}}
\left|\|f(u)-f(v)\|_p-\|u-v\|_2\right|,
\]

where \(f\) maps the observed points into \(\ell_p^d\), \(f(0)=0\), and each mapped distance lies between the original distance and \(D\) times it.

### Proof

1. For standard Gaussian \(g\in\mathbb R^m\), let \(c_p=(\mathbb E|G|^p)^{1/p}\) for \(G\sim N(0,1)\). The map \(J(v)(g)=c_p^{-1}\langle g,v\rangle\) is in real \(L_p\) and satisfies \(\|J(u)-J(v)\|_{L_p}=\|u-v\|_2\). Apply paper #094 to \(\{0,x_0,\ldots,x_{T-1}\}\) and rescale its images by the positive scale in the distortion definition. Translate so \(f(0)=0\). Then \(\|u-v\|_2\le\|f(u)-f(v)\|_p\le D\|u-v\|_2\).
2. Apply paper #325 to \(P(z)=z^t\). Its numerical-range estimate yields \(\|A^t\|_2\le2q^t\). Every unobserved \(x_t\) with \(t\ge T\) lies within \(B=2q^T\|x\|_2\) of the zero anchor.
3. Let \(E_T\) be the worst additive distance error on the observed finite set including zero. Observed pairs incur at most \(E_T\). Cross pairs have error at most \(E_T+B\), from the triangle and reverse-triangle inequalities. Two clipped points have true distance at most \(2B\). Thus all time pairs have error at most \(E_T+2B=E_T+4q^T\|x\|_2\). `MathCan/OrbitStitching.lean` kernel-checks the underlying three-case integer-metric lemma.
4. Since \(\|x_t\|_2\le2\|x\|_2\), the original distance between any two observed states is at most \(4\|x\|_2\). Consequently \(E_T\le4(D-1)\|x\|_2\). This proves the displayed estimate. For \(x=0\), use the zero sketch.

**Scale interpretation.** At fixed \(p,D,q\), choosing \(T\asymp\log(1/\delta)\) makes the tail term at most \(4\delta\|x\|_2\), and \(d\le\exp(O_{p,D}((\log\log(1/\delta))^{\gamma(p)}))\). A fixed \(D>1\) leaves the additive floor \(4(D-1)\|x\|\). The unknown \(C_{p,D}\) varies when \(D\downarrow1\), so the fixed-distortion bound alone gives no vanishing-error dimension rate.

**Sharp tail multiplier.** The abstract radius-only assumption permits two late points at \(Be_1\) and \(-Be_1\). Both are within \(B\) of zero and mapping both to zero incurs error \(2B\). The abstract stitching factor two is therefore optimal, without asserting its attainability on a particular contractive orbit.

## Exact rational block-Jordan certificate

For \(J(a,b)=\begin{pmatrix}a&b\\0&a\end{pmatrix}\) with nonnegative rational \(a,b\), the complex numerical range is a disk centered at \(a\) with radius \(b/2\): if \(\|u\|_2=1\), then \(u^*Ju=a+b\overline{u_1}u_2\). The latter product fills a disk of radius \(1/2\). The numerical radius of a block diagonal matrix equals the maximum of its blocks' numerical radii.

The applied benchmark takes \(a_i=3/8-i/1024\) and \(b_i=1-((5i)\bmod7)/256\), \(0\le i<32\). Thus \(w(A)=7/8\), \(\rho(A)=3/8\), and \(\|A\|_2=9/8\), all through rational block formulas.

There is also a direct elementary proof of the power decay for these blocks, independent of the imported Crouzeix theorem. If \(N^2=0\), then \(J^t=a^t I+tba^{t-1}N\). Its operator norm is at most \(a^t+tba^{t-1}\le2(a+b/2)^t\), using the first two nonnegative terms in the binomial expansion. The case \(t=0\) is immediate.

## Verification scope and next gate

- **Lean:** \(E+2B\) stitching and \(2B\) tail-pair bound for integer-valued metrics. The CI build plus `#print axioms` establish the local kernel result.
- **Written analytic mathematics:** Gaussian isometric embedding, imported #094 and #325, and the new infinite-horizon deduction. This is paper-level, not Lean formalization.
- **Applied finite controls:** rational numerical-radius gate; Jordan amplification; analytic power formula; spectral-only negative control; measured \(p=2\) and \(p=4\) sketch distortions. The reported empirical prefix discrepancy uses ordinary floating point, without outward interval rounding.
- **Next experiment:** extract a Jacobian at a trained recurrent model's fixed trajectory and independently enclose its numerical range. Nonlinear hidden-state trajectories need a separate perturbation or Jacobian-variation bound before applying this linear theorem.

Applied implementation: [Compactification-Theory NOR-01](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor01-numerical-orbit-sketch-20261115/research/nor01_numerical_orbit_sketch).
