# OLM-15: Native SAE erasure, curvature and local selection

November 16, 2026. Pure mathematics accompanying [SMC-15 active-feature native erasure](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc15-active-feature-erasure-20261116/research/real_recurrence_sae_v1/SMC15_PROTOCOL.md), continuing merged [OLM-14](OLM14_CROSS_CHECKPOINT_CAUSAL.md). The elementary calculus and linear algebra below are classical. The useful research contribution is the exact experimental distinction between symmetric *injection* responses and full native SAE *contribution erasure*, with a counterexample and a falsifiable finite bound. This document contains written proofs and exact-Fraction regression witnesses, not Lean verification.

## 15A. A central causal response can agree while native erasures have opposite signs

Let the clean scalar hidden state be `h=1`, the common one-feature ReLU SAE encoder `z(h)=max(h,0)`, and the common physical decoder `d=1`. Let `C=10`, `K>1` and define the two clean task margins

\[
m_A(x)=C+x,\qquad m_B(x)=C+x+K(x-1)^2.
\]

Both models have the **same** clean activation `z(1)=1`, clean margin `C+1` and task classification. For every `r>0` their central finite responses equal:

\[
\frac{m_A(1+r)-m_A(1-r)}{2r}
=\frac{m_B(1+r)-m_B(1-r)}{2r}=1.
\]

The common full native SAE erasure replaces `h=1` by `h-z(h)d=0`, however, giving

\[
\boxed{m_A(1)-m_A(0)=1,\qquad m_B(1)-m_B(0)=1-K<0.}
\]

The quadratic term is even around the clean state, so symmetric sampling cancels it, while a one-sided, amplitude-sized erasure retains the quadratic contribution. **Thus perfect observational alignment together with perfect central finite-response agreement at every radius fails to identify the sign of full native SAE erasure.** The obstruction survives even when both margins are positive throughout the erasure segment. The executable `Fraction` witness sets `K=3`.

## 15B. A finite-radius native-erasure bound

Let `m: R^d → R` be twice differentiable along the segment `h - t z d`, `t∈[0,1]`, where `z>0` is the **frozen clean SAE coefficient** and `d` is its physical decoder column. Assume `||D²m||op≤M` on that entire line segment. The native decoder-contribution erasure is `A(h)=h-zd`, and its clean task-margin drop is `E=m(h)-m(A(h))`.

**Theorem OLM-15B.**
\[
\boxed{|E-z\,Dm(h)[d]|\le\frac{M}{2}z^2\|d\|_2^2.}\tag{1}
\]
By Taylor's theorem, `m(h-zd)=m(h)-z Dm(h)[d]+R` with `|R|≤Mz²||d||²/2`, proving (1).

This bound is *sharp*: for a scalar quadratic `m(x)=a x+ b x²/2`, `h=z=d=1`, the discrepancy from the clean-point derivative is `|b|/2=M/2`.

For teachers A and B, `s∈{±1}`, `α≥0`, and independently certified segment-Hessian bounds `M_A,M_B`, the triangle inequality gives

\[
\boxed{|E_B-s\alpha E_A|\le
|z_B Dm_B(h_B)[d_B]-s\alpha z_A Dm_A(h_A)[d_A]|
+\frac12(M_B z_B^2\|d_B\|^2+\alpha M_A z_A^2\|d_A\|^2).}\tag{2}
\]

A central finite-difference correlation by itself certifies neither the first term nor the curvature terms. SMC-15 reports FP64 intervention observations and does not claim either derivative or Hessian bound has been certified for the recurrent checkpoints.

## 15C. Physical subtraction need not silence a selected SAE feature

Use a standard top-k ReLU encoder, with normalized input `(h-μ)⊘scale`, encoder row `w_j`, bias `b_j`, and physical decoder column `d_j=scale⊙D_j`. For a clean positive selected coefficient `z_j`, define its **same-fit feedback gain**

\[
g_j=w_j^T(d_j\oslash scale)=w_j^T D_j.
\]

Under the explicit assumption that the same feature remains selected and its ReLU is linear along the open erasure segment,

\[
\boxed{z_j(h-z_jd_j)=z_j(h)(1-g_j).}\tag{3}
\]

This follows by substituting `h-z_j d_j` into the same encoder affine form, then using its clean coefficient `z_j(h)`. Complete re-encoded silencing requires `g_j=1` under that stable-selection hypothesis. At an endpoint where the feature leaves the active top-k set, (3) is no longer the applicable formula. For `g_j>1` the linear formula would be negative, so the assumed selection regime cannot persist all the way to the endpoint. This is why SMC-15 measures **post-erasure re-encoded activations** separately from output-margin effects.

## 15D. Activity does not establish task necessity

Take `h=(1,1)`, SAE `z(h)=ReLU(h_1)=1`, physical column `d=(1,0)`, and task margin `m(h)=10+h_2`. The selected atom is strongly active and its native erasure changes the hidden state to `(0,1)`, while `m(h)-m(h-zd)=0`. This exact witness shows the need for a task-functional intervention in addition to observing that an atom is encoded.

## Experiment-to-theorem contract

SMC-15 fixes each `z_j` and `d_j` from the original clean checkpoint/SAE, subtracts the physical contribution from one 48-dimensional stage-one Sudoku goal token, continues the unchanged recurrence for three FP64 steps, and holds the correct digit/clean competitor pair fixed. It compares an SMC-13C calibration-frozen *naturally active* target atom against a **dose-matched different active atom**, with both global response orientations chosen only on calibration. Two fresh, solution-disjoint 64-puzzle cohorts constitute heldout evaluation. A success is an empirical operational feature-erasure correspondence conditional on the declared choice of intervention and controls.
