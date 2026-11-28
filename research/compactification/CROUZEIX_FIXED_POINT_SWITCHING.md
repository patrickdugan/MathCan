# NRF-01: Cyclewise numerical-range contraction with approximate fixed-point certificates

**Date:** November 15, 2026. **Status:** newly derived theorem for the research program with written proof and finite exact-rational checks. External novelty has not been established; this theorem may have precedents.

## Input pair

OpenAI family 325, *A direct proof of the complete Crouzeix inequality* (September 26, 2026), https://github.com/openai/math/tree/main/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026. The mathematical input is its claimed constant-two complete bound

\[
\left\|\sum_{k=0}^{d} A^k\otimes B_k\right\|
 \le 2\max_{z\in W(A)}\left\|\sum_{k=0}^{d}z^k B_k\right\|.
\]

OpenAI family 328, *Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces* (September 24, 2026), https://github.com/openai/math/tree/main/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026. Its proposed fixed-point result motivates the nonexpansive backbone and zero-regularization limit. The new theorem proves the needed finite-dimensional result directly by a contraction argument. It does not depend on the general reflexive-space assertion.

The mathematical release is research data with varying verification status. This proof is **conditional on the cited Crouzeix inequality** in the general matrix-valued case. The worked Jordan specialization is also certified by a separate elementary norm bound, independent of the source proof.

## Theorem NRF-01

Let \(H=\mathbb C^{nh}\), viewed as a real Hilbert space, and let \(C\subset H\) be nonempty, closed, bounded, and convex. Fix an \(m\)-phase schedule. For each phase \(i\), let \(F_i:C\to C\) be nonexpansive. Take \(A_i\in M_n(\mathbb C)\), compatible coefficient matrices \(B_{ik}\in M_h(\mathbb C)\), the polynomial matrix
\[
L_i=\sum_{k=0}^{d_i}A_i^k\otimes B_{ik},
\]
an affine offset \(b_i\in H\), a nonexpansive map \(G_i:H\to C\) (for example metric projection onto \(C\)), and \(\eta_i\in[0,1]\). Choose a *certified upper bound* \(q_i\) such that
\[
q_i\ge\max_{z\in W(A_i)}\left\|\sum_{k=0}^{d_i}z^k B_{ik}\right\|.
\]
Set
\[
K_i(x)=(1-\eta_i)F_i(x)+\eta_i G_i(L_ix+b_i),\quad
r_i=1-\eta_i+2\eta_iq_i,\quad
\Gamma=\prod_{i=0}^{m-1}r_i.
\]
If \(\Gamma<1\), the following assertions hold even if some \(r_i>1\).

**Unique periodic orbit and convergence.** The full cycle \(Q=K_{m-1}\circ\cdots\circ K_0\) has one fixed point \(x_0^*\). Its phase images \(x^*_{j+1}=K_j(x^*_j)\) are the unique periodic orbit with the prescribed phase order. An arbitrary seed converges at the phase-resolved rate
\[
\|y_{tm+j}-x_j^*\|
\le\left(\prod_{i=0}^{j-1}r_i\right)
\Gamma^t\|y_0-x_0^*\|,\quad 0\le j<m.
\]

**Error transport, including expansive steps.** If an observed trajectory follows the same externally fixed schedule and each local update differs by at most \(\delta_j\), then after one cycle its error is at most
\[
D=\sum_{j=0}^{m-1}\delta_j\prod_{\ell=j+1}^{m-1}r_\ell.
\]
For a common initial state, after \(t\) cycles the difference is at most \(D(1-\Gamma^t)/(1-\Gamma)\). For arbitrary preselected, time-varying nonnegative rates \(r_j\) and errors \(\delta_j\), the sharper finite-time identity is
\[
e_T\le \left(\prod_{i=0}^{T-1}r_i\right)e_0
       +\sum_{j=0}^{T-1}\delta_j\prod_{\ell=j+1}^{T-1}r_\ell.
\]

**A posteriori orbit enclosure.** For any \(y\in C\),
\[
\|y-x_0^*\|\le \frac{\|Q(y)-y\|}{1-\Gamma},
\quad
\|Q^t(y)-x_0^*\|\le
\frac{\Gamma^t\|Q(y)-y\|}{1-\Gamma}.
\]

**Unregularized residual and limit.** Let \(D_C=\operatorname{diam}(C)\). At every phase of the stabilized orbit,
\[
\|x_{i+1}^*-F_i(x_i^*)\|\le\eta_iD_C.
\]
If a sequence of valid contractive regularizations satisfies every \(\eta_i^{(k)}\to0\), any accumulation point of the resulting periodic orbit vectors is an exact periodic orbit of the original family \(F_i\). This last assertion uses finite-dimensional compactness.

## Proof

The complete Crouzeix bound gives \(\|L_i\|\le2q_i\). Nonexpansiveness of \(G_i\) and translation invariance of differences make \(x\mapsto G_i(L_ix+b_i)\) Lipschitz with constant at most \(2q_i\). Hence the convex blend \(K_i\) maps \(C\) into \(C\) with Lipschitz bound \(r_i\). The composition has constant at most \(\Gamma<1\). A closed subset of finite-dimensional Hilbert space is complete, so Banach's contraction principle gives exactly one fixed point of the cycle. Applying the intermediate phase bounds proves the convergence formula.

For perturbed trajectories, set \(e_t=\|\widehat y_t-y_t\|\). The triangle inequality yields \(e_{t+1}\le r_t e_t+\delta_t\). Substitute successively, without assuming \(r_t\le1\), to obtain the finite weighted product formula. Periodic repetition gives \(e_{(t+1)m}\le\Gamma e_{tm}+D\), whose geometric sum yields the displayed cycle budget.

For any \(y\), \(\|y-x_0^*\|\le\|y-Q(y)\|+\Gamma\|y-x_0^*\|\); rearrange and then contract \(t\) times. Finally,
\[
x_{i+1}^*-F_i(x_i^*)
=\eta_i(G_i(L_i x_i^*+b_i)-F_i(x_i^*)).
\]
Both points on the right lie in \(C\), so the residual is at most \(\eta_iD_C\). Along a sequence with \(\eta_i^{(k)}\to0\), compactness of \(C^m\) provides a convergent subsequence. The continuous maps \(F_i\) pass to the limit in the residual identities, yielding a period-\(m\) orbit. This completes the proof.

## Exact Jordan witness and sharp obstruction

Take \(A=cI+uE_{12}\in M_2(\mathbb C)\). Its numerical range is the exact disk \(\{z:|z-c|\le|u|/2\}\): for every unit vector \(v\), \(|\overline v_1v_2|\le1/2\), and equal-magnitude coordinates realize the boundary with arbitrary phase. If
\(p(z)=\sum_{k=0}^d a_k(z-c)^k\), then \(E_{12}^2=0\) implies
\[
p(A)=a_0I+a_1uE_{12},\qquad
q_{\rm disk}=\sum_k |a_k|(|u|/2)^k.
\]
This disk sum is a rigorous upper bound on \(\max_{W(A)}|p|\). An independent direct proof in this restricted setting is
\[
\|p(A)\|\le |a_0|+|a_1u|\le2q_{\rm disk}.
\]
For \(c=0,u=2,p(z)=z\), the matrix has spectrum \(\{0\}\) yet operator norm \(2\), while \(2\max_{W(A)}|p|=2\). A spectral-radius-only contraction test fails on this matrix.

An explicit expanding-phase schedule uses \((\eta_0,q_0)=(1,1)\) and \((\eta_1,q_1)=(3/4,0)\). These yield bounds \(r_0=2\), \(r_1=1/4\), and \(\Gamma=1/2\). The cycle is certified even though its first phase may expand distances.

## Checks and research boundary

The separate exact-rational module research/compactification/crouzeix_switching.py and tests/test_crouzeix_switching.py check 54 polynomial matrix identities, 584 weighted-error recurrences, expansive-phase compensation, and the nonnormal obstruction. MathCan/NumericalRangeSwitching.lean contains a small Init-only comparison proof for natural-valued error recurrence; it does not formalize the real/complex norm theorems. Its CI compilation and axiom inventory must be inspected independently.

The LoopedTransformers application is a two-dimensional algebraic toy with a rigorously known numerical-range disk and nonexpansive gates. Actual neural weights require certified numerical-range *upper enclosures*, and a state-dependent switching policy needs a separate coupled-policy Lipschitz analysis. This theorem gives no empirical neural capability or safety result. Published mathematical novelty and precedence remain to be audited.
