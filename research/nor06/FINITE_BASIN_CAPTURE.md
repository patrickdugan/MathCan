# NOR-06: certified finite capture as the missing bridge to natural recurrent histories

**Status (November 15, 2026):** new capture-to-compactification deduction with a written proof. The discrete orbit, enclosure and counterexample lemmas are independently Lean-checked in MathCan/BasinCapture.lean, pending CI. The trained-input experiment is exploratory and its first survey uses FP64; source-locked basin entry must be established with a separate interval certificate.

## Imported NOR-04/05 premise

Let \(F:\mathbb R^n\to\mathbb R^n\) be a \(C^1\) recurrent transition on an invariant convex cube. For a fixed block length \(L\), put \(G=F^L\). Suppose there is a closed Euclidean ball \(B(c,R)\) such that
\[
\sup_{z\in B}\|DG(z)\|_2\le K<1,\qquad
\|G(c)-c\|_2\le s,\qquad s+KR\le R.
\]
NOR-04 proves this has a unique \(G\)-fixed point \(p\in B\) satisfying \(\|p-c\|\le s/(1-K)\). NOR-05 supplies the additional one-step criterion forcing \(F(p)=p\). It also computes a uniform global cube Lipschitz constant \(L_{\rm cube}\) for \(F\). These are already established for the frozen RRC-25 model on a radius-\(10^{-11}\) ball, with \(L=12\).

A **pointwise block derivative certificate** at an observed trajectory state has separate scope. Its disk upper bound can be less than one while that state lies far outside \(B\). Such a disk neither establishes basin membership nor uniform derivative control along a long path.

## Theorem 1: finite source capture and all-depth convergence

Let \(x_0\) be any source-generated state. Select a finite, explicitly observed time \(T_0\), usually divisible by \(L\), and supply a rational reference vector \(y\) with a validated error
\[
\|F^{T_0}(x_0)-y\|_2\le\epsilon.
\]
Suppose an independent rational arithmetic check establishes
\[
\boxed{\|y-c\|_2+\epsilon\le R.}\tag{1}
\]

Then the *true* recurrent state \(F^{T_0}(x_0)\) belongs to \(B(c,R)\). For every \(m\ge0\) and \(0\le j<L\),
\[
\boxed{
\|F^{T_0+Lm+j}(x_0)-p\|_2
\le L_{\rm cube}^j K^m
\left(\|y-c\|_2+\epsilon+\frac{s}{1-K}\right).
}\tag{2}
\]
Thus the actual source-generated orbit converges to the trained nonlinear fixed point at all integer depths after finite capture.

*Proof.* The triangle inequality gives \(\|F^{T_0}(x_0)-c\|\le\epsilon+\|y-c\|\le R\). The invariant-ball theorem applies to every subsequent \(G\)-iterate, giving \(K^m\|F^{T_0}(x_0)-p\|\). NOR-05's one-step fixed point status and global cube Lipschitz constant transport this bound through the remaining \(j\) steps. The final factor follows from \(\|p-c\|\le s/(1-K)\). \(\square\)

Importantly, (1) uses an **upper bound on a genuine state-error enclosure**, which is independent of how close a floating-point trajectory appears to the center.

## Theorem 2: all-time finite-history Lp capture

Let \(T>T_0\), let \(H=\max(1,L_{\rm cube}^{L-1})\), and set
\[
Q=\|y-c\|_2+\epsilon+s/(1-K),\qquad
B_T=H K^{\lfloor (T-T_0)/L\rfloor}Q.
\]
For every \(t\ge T\), equation (2) shows \(\|F^t(x_0)-p\|\le B_T\). Apply the normalized Gaussian isometry from the real Euclidean space into \(L_{p_0}\) and OpenAI Math #094 finite-set dimension reduction to the \(T+1\) points
\[
\{p,x_0,F(x_0),\ldots,F^{T-1}(x_0)\}.
\]
At fixed \(1<p_0<\infty\), \(p_0\ne2\), \(D>1\), an existential distortion-\(D\) map has coordinate count at most
\[
d\le\exp(C_{p_0,D}(\log(T+1))^{\gamma(p_0)}).
\]
After translating the image of \(p\) to zero, replace every time \(t\ge T\) by that anchor. The exact NOR-01 stitching argument gives
\[
\boxed{\sup_{i,j\ge0}\left|
\|\hat x_i-\hat x_j\|_{p_0}
-\|F^i(x_0)-F^j(x_0)\|_2
\right|\le E_T+2B_T,}\tag{3}
\]
where \(E_T\) is the largest observed finite-window additive error including \(p\). The bound is for the actual nonlinear input-conditioned orbit after a finite capture proof. An efficient constructive embedding remains an additional question.

## The missing verification gate: recentered interval shadowing

For a source-generated hidden state, a useful finite proof may consist of rational approximate states \(c_0,\ldots,c_M\) and radii \(\rho_0,\ldots,\rho_M\) with
\[
\|x_0-c_0\|\le\rho_0,\qquad
\|G(c_k)-c_{k+1}\|\le e_k,\qquad
\sup_{z\in B(c_k,\rho_k)}\|DG(z)\|\le K_k,
\]
and
\[
\boxed{\rho_{k+1}\ge e_k+K_k\rho_k.}\tag{4}
\]
Induction proves \(\|G^k(x_0)-c_k\|\le\rho_k\), provided each source-state ball lies in the declared domain and the derivative bound holds throughout it. A rational final clearance \(\|c_M-c\|+\rho_M\le R\) then supplies (1).

This method differs from repeatedly propagating raw axis-aligned interval boxes: it recenters each step and records a norm-bound on its *actual derivative product*. A numerically measured contraction ratio is not a replacement for a uniform interval product on the current tube.

The separate [NOR-06 input survey](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor06-trained-gru-basin-entry-20261115/research/nor01_numerical_orbit_sketch) freezes the source cohort, original model SHA, first measured basin crossings, and diagnostic thresholds, explicitly marking all FP64 hits as **uncertified** until a valid recurrence of form (4) is executed.

## A formal obstruction

Even two maps with exactly the same transition on a fully certified invariant singleton basin can have opposite behavior on an external initial state. On \(\{false,true\}\), define \(F_{\rm good}(x)=false\) and \(F_{\rm bad}(x)=x\). Both agree on the invariant basin \(\{false\}\). From \(true\), the good map enters in one step while the bad map remains outside forever. Lean checks their internal agreement and both external trajectories.

Thus a source-specific finite-entry witness is an essential mathematical premise. No inference about the external basin follows from the NOR-04 ball alone.
