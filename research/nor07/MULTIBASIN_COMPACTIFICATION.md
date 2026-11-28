# NOR-07: multibasin compactification and a late-history label obstruction

**Research status (November 15, 2026):** new analytic finite-metric deduction based on NOR-04/05 and OpenAI Math #094/#325. A second trained-GRU attractor is currently a numerical candidate from NOR-06's squared input. Its existence, period-one status, and distinctness remain subject to a separate source-locked interval CI receipt. The formal disjoint-ball and collapsed-code obstruction are Lean-checked in MathCan/MultiBasin.lean, pending CI. Priority beyond our program is unverified.

## Two local nonlinear basins

Let \(F:U\to U\) be a \(C^1\) map on an invariant convex set in \(\mathbb R^n\). Suppose there are two closed Euclidean balls
\[
B_i=\overline B(c_i,R_i), \qquad i=1,2,
\]
with certified block lengths \(L_i\), block maps \(G_i=F^{L_i}\), uniform derivative bounds \(K_i<1\), and point residual bounds \(s_i\) such that
\[
\sup_{h\in B_i}\|DG_i(h)\|_2\le K_i,\qquad
\|G_i(c_i)-c_i\|_2\le s_i,\qquad
s_i+K_iR_i\le R_i.
\]
Banach's theorem provides a unique fixed point \(p_i\in B_i\) for each block map. If the NOR-05 one-step return criterion
\[
\sup_{h\in B_i}\|DF(h)\|_2\,
\frac{s_i}{1-K_i}+\|F(c_i)-c_i\|_2<R_i
\]
holds, then \(F(p_i)=p_i\).

**Theorem 1 (certified bistability).** If
\[
\boxed{\|c_1-c_2\|_2>R_1+R_2,}\tag{1}
\]
then \(p_1\ne p_2\) are distinct locally attracting fixed points of the same nonlinear one-step map \(F\). Each attracts every input that is certified to enter its respective invariant ball.

*Proof.* The triangle inequality forces \(\|p_1-p_2\|\ge\|c_1-c_2\|-R_1-R_2>0\). Local contraction of the appropriate \(F^{L_i}\), combined with period-one status and bounded intervening one-step derivatives, gives convergence at all integer depths. \(\square\)

This is a local statement: two attractors do not establish their relative basin volumes, natural-input frequencies, or semantic labels.

## A lower bound on collapsed-basin histories

Assume two initial states \(x_i\) have each entered \(B_i\) and converge to \(p_i\). Let \(u_t=F^t(x_1)\), \(v_t=F^t(x_2)\), and suppose for all sufficiently late times \(\|u_t-p_1\|\le b_1(t)\), \(\|v_t-p_2\|\le b_2(t)\), with \(b_i(t)\to0\).

**Theorem 2 (two-basin code-collapse obstruction).** If a history representation maps both sufficiently late state streams to the **same** terminal code \(z\), then any additive pairwise distortion budget \(E_t\) for the cross-pair \((u_t,v_t)\) satisfies
\[
\boxed{E_t\ge \|p_1-p_2\|_2-b_1(t)-b_2(t).}\tag{2}
\]
Consequently
\[
\liminf_{t\to\infty}E_t\ge\|p_1-p_2\|_2
\ge\|c_1-c_2\|_2-R_1-R_2>0.
\]

*Proof.* True cross-basin distance obeys \(\|u_t-v_t\|\ge\|p_1-p_2\|-b_1(t)-b_2(t)\). If the common terminal code has cross-distance zero, pairwise additive error is the entire true cross-distance. Taking lower limits proves the claim. \(\square\)

This is the geometric reason a compact history code must retain an **attractor/basin distinction**, even when all within-basin tails are individually compressible to one point. The finite Nat-metric skeleton and two-ball disjointness are checked in MathCan/MultiBasin.lean.

## Lp history construction with one anchor per basin

Fix a horizon \(T\) after both state streams have suitable bounded tails, with bounds \(b_1(T)\) and \(b_2(T)\). Apply the normalized Gaussian Hilbert-to-real-\(L_p\) isometry and OpenAI Math #094 to the pooled finite set of \(2T+2\) points
\[
\{p_1,p_2,u_0,\ldots,u_{T-1},v_0,\ldots,v_{T-1}\}.
\]
The theorem gives an existential distortion-\(D\) embedding into \(\ell_p^d\), for \(1<p<\infty\), \(p\ne2\), with
\[
d\le \exp\left(C_{p,D}(\log(2T+2))^{\gamma(p)}\right).
\]
At each time \(t\ge T\), clip stream \(i\) to its own anchor image \(p_i\). If \(E_T\) is the worst finite observed-pair additive error including both anchors, then the triangle and reverse-triangle inequalities imply an all-time pairwise error bound
\[
\boxed{E_T+2\max\{b_1(T),b_2(T)\}.}\tag{3}
\]
Thus two distinct terminal anchors preserve cross-basin geometry with no ambient-dimensional dependence in the formal existence statement. OpenAI Math #325 remains available to control matrix-valued filters on frozen derivatives whose numerical ranges admit a certified disk enclosure. These analytic imports are paper-level.

## Candidate applied instantiation

The original RRC-25 1,000-parameter trained GRU has a certified first period-one fixed point in the NOR-04/05 radius-\(10^{-11}\) ball centered at
\[
c_1=(-0.46412196023,\ 0.93954570430,\ldots).
\]
A public squared-family source case, zero-input continued for 4,800 steps in a separately locked FP64 survey, numerically converged to a stationary vector
\[
c_2=(0.14515780418,\ -0.89936969686,\ldots),
\]
at distance approximately \(5.0209123358\) from \(c_1\). The independent [NOR-07 interval audit](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor07-rrc25-two-attractors-20261115/research/nor01_numerical_orbit_sketch) now Newton-refines \(c_2\) at high decimal precision, tries to certify a 24-step nonlinear contraction ball around it, checks the one-step return condition, and proves the two certified balls disjoint using a single rational coordinate gap.

A successful validation would establish **two distinct locally attracting real-analytic fixed points in one trained GRU**. Whether the originally sampled squared-family source input can be rigorously shown to enter the second small ball remains a separate finite-entry obligation, as in NOR-06.
