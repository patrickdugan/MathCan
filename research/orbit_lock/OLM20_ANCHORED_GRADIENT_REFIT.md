# OLM-20: Difference-sensitive task-gradient transport between SAE refit erasures

**November 16, 2026.** Pure-mathematics companion to the prospective [SMC-20 anchored-gradient refit protocol](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc20-anchored-gradient-refit-20261116/research/real_recurrence_sae_v1/SMC20_PROTOCOL.md). Extends the OLM-14–19 native erasure and representation-gauge line. Statements are written finite-dimensional theorems with exact Fraction witnesses, **not Lean-kernel certified** and with no priority claim for standard multivariable Taylor calculus.

## Setup

Fix a recurrent teacher, a single clean hidden state \(h\in\mathbb R^d\), and a scalar clean task-margin functional \(m:\mathbb R^d\to\mathbb R\) obtained by fixing the correct Sudoku digit and its highest *clean* competing digit and continuing the teacher for the registered number of recurrent steps. Different SAE refits on the **same frozen teacher** yield native physical decoder-erasure edits \(a,b\in\mathbb R^d\). Define the observed source/reference erasure \(E_a=m(h)-m(h-a)\), the unknown new refit target \(E_b=m(h)-m(h-b)\), and the clean task gradient \(g=\nabla m(h)\).

SMC-20's parameter-free anchored prediction uses the *observed* reference erasure and the *clean* first-order correction:
\[
\boxed{\widehat E_b=E_a+g^\top(b-a).}\tag{1}
\]
Every term in the prediction can be evaluated before the target refit erasure \(E_b\) is observed. The source anchor is a legitimate first-party intervention measurement and cannot be interpreted as an intervention-free causal claim.

## OLM-20A. Difference-sensitive anchored-gradient remainder

Let \(m\in C^2\) on a convex region containing the triangle with vertices \(h,h-a,h-b\). Suppose \(\|D^2m(x)\|_{\rm op}\le M\) on that region, for some \(M\ge0\).

**Theorem.** The anchored prediction obeys
\[
\boxed{\big|E_b-\widehat E_b\big|
 \le M\,\|b-a\|_2\int_0^1\|(1-t)a+tb\|_2\,dt
 \le \frac{M}{2}(\|a\|_2+\|b\|_2)\|b-a\|_2.}\tag{2}
\]
For equal-norm edits \(\|a\|=\|b\|=r\), the final upper bound becomes \(Mr\|b-a\|\). The bound is a **difference-sensitive** estimate, vanishing when the physical contributions coincide even if each individual erasure dose is large.

**Proof.** The source/target erasure difference is
\[
E_b-E_a=m(h-a)-m(h-b)
       =\int_0^1\nabla m(h-a-t(b-a))^\top(b-a)\,dt.
\]
Subtract \(g^\top(b-a)\). A Hessian operator-norm bound on the line from \(h\) to each point in the triangle gives
\(\|\nabla m(h-a-t(b-a))-g\|\le M\|(1-t)a+tb\|\).
Integrate, apply Cauchy–Schwarz, then use convexity of Euclidean norm
\(\|(1-t)a+tb\|\le(1-t)\|a\|+t\|b\|\).
Integrating \(t\) from zero to one gives (2). QED.

**Sharpness.** In one physical dimension let \(h=0,a=0,b=r\) with \(r>0\), \(m(x)=M x^2/2\). Then \(g=0,\widehat E_b=0\), \(E_b=-Mr^2/2\), attaining equality in **both** inequalities of (2). More generally, the exact integral geometry factor in (2) can be sharper than its simple endpoint norm bound.

## OLM-20B. Conditional finite-erasure sign certificate

Write \(\varepsilon=M(\|a\|+\|b\|)\|b-a\|/2\).

**Corollary.** If \(|\widehat E_b|>\varepsilon\), then the true finite target erasure \(E_b\) is nonzero and
\[
\boxed{\operatorname{sgn}(E_b)=\operatorname{sgn}(\widehat E_b).}\tag{3}
\]

**Proof.** By (2), \(|E_b-\widehat E_b|\le\varepsilon\). To have \(E_b=0\) or the opposite sign would require \(|E_b-\widehat E_b|\ge|\widehat E_b|\), contradicting the strict premise. QED.

The claim **requires a genuine, independently verified bound \(M\) over the full convex triangle**, including all recurrent nonlinear regions encountered. A small local finite-difference curvature estimate is not a certified bound. SMC-20 therefore uses the gradient prediction as a numerical test and does not label its neural cases as theorem-certified.

## OLM-20C. Identical native decoder directions can still have different causal magnitudes

**Proposition.** Cosine similarity \(1\) between two physical decoder contribution vectors, even for a linear task margin and a perfectly stable SAE feature label, need not imply equal erasure effects.

Take \(h=0\), \(a=(1,0)\), \(b=(2,0)\), and \(m(x,y)=10+3x\). Then
\[
\cos(a,b)=1,\quad E_a=3,\quad E_b=6,\quad
\widehat E_b=E_a+(3,0)^\top(b-a)=6.
\]
Thus full physical **dose** and clean task gradient matter in addition to decoder direction. A measured cosine or matched coactivation alone cannot predict the signed magnitude. The anchored linear formula happens to be exact in this linear case.

## OLM-20D. Same clean gradient and source erasure can mask a reversed finite target sign

Set \(h=0\), \(a=0\), \(b=1\), \(m(x)=10+x+2x^2\). The clean task margin and gradient are \(m(0)=10\) and \(g=1\). The source effect is \(E_a=0\), so (1) predicts \(\widehat E_b=1\). Yet \(m(-1)=11\) and the true target effect is \(E_b=-1\), opposite in sign. The Hessian norm is \(M=4\); the bound in (2) equals \(2\), exactly the observed absolute prediction error. The strict sign premise (3) correctly fails: \(1>2\) is false. This counterexample uses one unchanged smooth task and retains positive margins at clean and edited states.

## OLM-20E. Orthogonal hidden-state gauge covariance of anchored prediction

Transport the hidden-state row-coordinate basis by an orthogonal matrix \(Q\), as in OLM-19: \(h_Q=hQ\), \(a_Q=aQ\), \(b_Q=bQ\), \(m_Q(v)=m(vQ^\top)\). Then \(E_{a,Q}=E_a\), \(E_{b,Q}=E_b\), and the transported row gradient satisfies \(g_Q=gQ\). Consequently
\[
\boxed{\widehat E_{b,Q}=E_a+(gQ)^\top((b-a)Q)=\widehat E_b.}\tag{4}
\]
Both the discrepancy and the difference-sensitive bound (2) are invariant under orthogonal transport. This physical estimate is robust to the exact basis rewrite that SMC-19 used as a software control, although independently refitted SAE dictionaries need not transform as such.

## Experimental falsifiability

SMC-20 reuses four exactly frozen SMC-19 refitted SAE checkpoints and the unchanged B501/B701 teachers. On two new 64-puzzle noncanonical Sudoku families it predicts each refit native decoder-erasure margin loss from the same original reference SAE71 erasure plus the clean task-gradient difference in physical edits. The control predictions use the original source erasure alone and the same-dose gradient projection along a different naturally active target SAE decoder. A preregistered two-family pass requires paired puzzle-cluster confidence bounds for both improvements, a predeclared relative absolute error reduction, and sign accuracy no lower than the reference-only predictor.

This is an **outcome-predictive operational comparison between two learned SAE decompositions**. Even a positive result cannot identify an intrinsic feature semantic basis. The explicit OLM-19 reconstruction/coactivation alias and OLM-18 full-rank inactive-feature dual remain relevant, independently of physical-gradient predictor quality.
