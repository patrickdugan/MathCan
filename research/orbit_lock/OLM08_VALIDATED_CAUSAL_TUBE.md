# OLM-08: Exact-real recurrent curvature tubes and causal-direction ranking

Date: November 15, 2026. Continuation of [OLM-07 causal Gram quotients](OLM07_CAUSAL_GRAM_QUOTIENT.md), applied by [SMC-08 to the independently pretrained 44K Sudoku recurrence](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc08-curvature-20261115/research/real_recurrence_sae_v1). The motivation from OpenAI Mathematics #131 and #238 is the distinction between marginally mixed representations and informative joint relational modes. The results here are finite-dimensional derivative and composition inequalities with established prior art; mathematical priority is not claimed.

## 1. Interventions through a fixed recurrent continuation

Let \(F:\mathbb R^d\to\mathbb R^q\) be the exact-real continuation of a frozen recurrent model from a specified hidden-state interface to a fixed set of logits. The intervention replaces \(h\) by \(h+ru\), with \(\|u\|_2=1\) and radius \(r\ge0\). Define \(J=DF(h)\) and the finite-radius displacement
\(\Delta_F(r,u)=F(h+ru)-F(h)\).

**Theorem OLM-08A (norm interval and causal ordering).** Suppose \(\|D^2F(x)\|_{\rm bilinear}\le M\) throughout the closed Euclidean ball \(\|x-h\|\le r\). Then

\[
\|\Delta_F(r,u)-rJu\|_2\le\tfrac12Mr^2,
\tag{1}
\]

and therefore

\[
\boxed{\max(0,r\|Ju\|_2-\tfrac12Mr^2)
\le \|\Delta_F(r,u)\|_2
\le r\|Ju\|_2+\tfrac12Mr^2.}
\tag{2}
\]

For two unit directions \(u,v\), the sufficient inequality

\[
\boxed{\|Ju\|_2-\|Jv\|_2>Mr}
\tag{3}
\]

certifies that the finite-radius displacement along \(u\) strictly exceeds that along \(v\) (same radius and site). If \(Ju=0\), its displacement norm is at most \(Mr^2/2\).

**Proof.** Taylor's integral remainder yields
\(F(h+ru)=F(h)+rJu+\int_0^r(r-t)D^2F(h+tu)[u,u]\,dt\).
Bounding the remainder norm by \(\int_0^r(r-t)Mdt=Mr^2/2\) proves (1). Apply the reverse and ordinary triangle inequalities to obtain (2). Compare \(r\|Ju\|-Mr^2/2\) with \(r\|Jv\|+Mr^2/2\) to obtain (3). QED.

A measured second derivative only at \(h\), or the largest Hessian value at a finite grid of t, **does not establish** the uniform premise. An exact-real global curvature bound does.

## 2. Composition of global derivative bounds

For each differentiable elementary layer \(f_i\), suppose its Jacobian and Hessian bilinear operator norms are uniformly bounded over all possible inputs by \(a_i\ge0\) and \(b_i\ge0\). Let \(T_i=f_i\circ\cdots\circ f_1\), and initialize \(A_0=1, B_0=0\).

**Theorem OLM-08B (computable global Hessian certificate).**

\[
\boxed{
A_i=a_iA_{i-1},\qquad
B_i=b_iA_{i-1}^2+a_iB_{i-1}.
}
\tag{4}
\]

For any linear readout \(W\),

\[
\boxed{\|D(WT_L)\|_{\rm op}\le\|W\|_{\rm op}A_L,\quad
\|D^2(WT_L)\|_{\rm bilinear}\le\|W\|_{\rm op}B_L.}
\tag{5}
\]

**Proof.** Use \(D(f\circ g)=Df(g)Dg\) and
\(D^2(f\circ g)[u,v]=D^2f(g)[Dg\,u,Dg\,v]+Df(g)D^2g[u,v]\).
Taking operator norms yields (4) inductively. Composition with W gives (5). QED.

This theorem applies to the *entire recurrence* as a composition of actual named layers, with no assumption that a small training perturbation remains small after every layer. Its global bounds can consequently be very conservative.

## 3. Certified layer coefficients for the frozen TRM-inspired block

The source-locked model in SMC-07 has an 81-token by 48-channel hidden state, a two-linear-layer GELU token residual mixer, a population LayerNorm, a two-linear-layer GELU channel residual mixer, and a second LayerNorm, repeated for three continuation steps after stage one. The output at a chosen goal token is a ten-logit affine head. The following coefficients apply to the **exact-real function whose weights equal the exact stored binary FP32 parameters**, including the embedded residual identities.

### Residual GELU mixer

For \(R(x)=x+W_2\mathrm{GELU}(W_1x+b_1)+b_2\), with exact erf-GELU, the scalar bounds
\(\sup|\mathrm{GELU}'|\le5/4\) and \(\sup|\mathrm{GELU}''|\le4/5\) give

\[
a_R=1+\tfrac54\|W_2\|_2\|W_1\|_2,\qquad
b_R=\tfrac45\|W_2\|_2\|W_1\|_2^2.
\tag{6}
\]

The same constants apply when the mixer is repeated independently across other channels or tokens, using Euclidean norms on the flattened hidden state. Every spectral norm is upper bounded by a rational dyadic ceiling of its exact Frobenius norm, computed from the exact binary parameters. This replacement is conservative and sound.

### Population LayerNorm

For \(N(x)=\gamma\odot (Px)/\sqrt{\varepsilon+\|Px\|^2/d}+\beta\), \(P=I-\mathbf1\mathbf1^\top/d\), the local norm estimates from the existing [Arb-validated LayerNorm curvature analysis](https://github.com/MoralityLabAI/Compactification-Theory/blob/main/research/levin_sieve_v1/goal_taylor_v1/README.md) imply the global bounds

\[
a_N=\|\gamma\|_\infty/\sqrt{\varepsilon},\qquad
b_N=2\|\gamma\|_\infty/(\sqrt{3d}\,\varepsilon).
\tag{7}
\]

For d=48, \(\sqrt{3d}=12\). The exact validator replaces the irrational square-root coefficients with dyadic rational upper ceilings; it reads the actual stored \(\gamma\) entries and the exact binary value of the module's eps parameter (nominally \(10^{-5}\)). These bounds apply for all possible hidden states and every intervention radius.

The resulting 12-stage chain yields a mathematically valid, state-independent \(M_{\rm global}\) and \(L_{\rm global}\) for the complete three-step continuation. The source-locked receipt must include the explicit rational coefficients so they can be independently replayed. No floating SVD value alone qualifies as an upper certificate.

**Limit:** Squashing every LayerNorm denominator to its global \(\sqrt{\varepsilon}\) floor after each of twelve layers may make \(M_{\rm global}\) astronomically large. The outcome then certifies only an uninformative outer envelope. Reporting it as a successful radius-0.2 causal ordering would be a substantive error. The existing Arb Taylor implementation can provide a more localized upper bound if its local clean-state denominators and transported perturbation radii remain controlled.

## 4. The causal singular direction as a control

For a single heldout puzzle and a fixed goal token, let \(J\in\mathbb R^{10\times48}\) be the first-order Jacobian of its ten final logits with respect to the 48 channels of the stage-one goal token. Its maximal first-order output norm is

\[
\max_{\|u\|=1}\|Ju\|=\sigma_{\max}(J).
\tag{8}
\]

The top right singular vector provides an **oracle directional sensitivity control**. An SAE decoder atom \(u_j\) satisfies

\[
\boxed{0\le\eta_j=\|Ju_j\|/\sigma_{\max}(J)\le1.}
\tag{9}
\]

The ten-logit Jacobian has rank at most 10, so at least 38 directions of the 48-channel goal-token state lie in its first-order kernel (possibly more). Those Jacobian-null directions can be visible at finite radius through curvature, as OLM-07 already shows.

**Interpretability warning:** Larger equal-norm output effects along active SAE atoms than isotropic directions can arise from ordinary alignment with \(J\)'s high-singular-value subspace. The ratio in (9) measures that alignment without assigning any semantic meaning or claiming a new model capability.

## 5. Verification contract

- [validated_causal_tube.py](validated_causal_tube.py) computes Frobenius/square-root ceilings using exact Fractions and integer square roots, and recursively builds exact rational \(L,M\) envelopes from the frozen network's weights.
- [test_validated_causal_tube.py](../../tests/test_validated_causal_tube.py) verifies exact arithmetic, layer coefficient bounds, composition identities and finite-radius ordering.
- SMC-08 evaluates the actual source-locked pretrained checkpoint, computes FP64 Jacobians for 16 heldout puzzle IDs, compares SAE active/inactive/isotropic directions and the Jacobian-optimal singular vector, measures finite-radius Taylor discrepancies, and exports a separate exact rational upper certificate.
- Numerical Hessian point estimates and finite-grid maxima remain labeled **empirical**; certified bounds refer to exact-real functions with the stored weight values. FP64 hardware roundoff, learned SAE optimization and generalization outside the source-pinned roster are separately outside the analytic certificate.

The new mathematical contribution is the task-specific combination of these established derivative identities into an auditable certificate interface for a learned decoder's intervention directions. Literature priority beyond this synthesis is not claimed.
