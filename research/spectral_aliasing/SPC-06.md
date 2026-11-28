# SPC-06: Temporal observability beyond the instantaneous readout

**Date:** 2026-11-15. Independent continuation of the SPC-01 to SPC-05
mathematical synthesis. This is a local contribution to a research program;
independent literature-priority review has not been performed. OpenAI Math
families #129 (future-context state distinguishability) and #130 (exact
Fourier/tensor representations) motivate the questions. The theorems below
follow from elementary linear algebra and explicit constructions rather than
asserting new consequences of either source paper.

## 1. Recurrence, readout, and a finite observation window

Let `F : R^d -> R^d` be differentiable and `R : R^d -> R^c` a readout.
Starting from `x`, define the finite-window observation vector

\[
  \mathcal O_T(x)=(R(x),R(F(x)),\ldots,R(F^T(x))) . \tag{1}
\]

At a fixed orbit point `x_t`, set `A_t=DF(x_t)` and `C_t=DR(x_t)`.
The derivative of (1) with respect to the initial state is the block
matrix

\[
D\mathcal O_T(x_0)=
\begin{pmatrix}
C_0 \\
C_1A_0 \\
C_2A_1A_0 \\
\vdots\\
C_TA_{T-1}\cdots A_0
\end{pmatrix}. \tag{2}
\]

The row space of each prefix is nested in that of each extension. A state
perturbation in `ker C_0` is invisible to the current output to first
order; it may become observable at later times when
`C_t A_{t-1}...A_0 v != 0`.

**Theorem 1 (finite-horizon rank budget).** For every such system,

\[
 \operatorname{rank}D\mathcal O_T
 \le \min\{d,(T+1)c\},\qquad
 \operatorname{rank}D\mathcal O_{T+1}\ge
 \operatorname{rank}D\mathcal O_T. \tag{3}
\]

The bounds follow from matrix size and inclusion of preceding block rows.
They are sharp. On the cyclic coordinate shift `F(x)_i=x_{(i+c) mod d}`
with `R` returning coordinates `0,...,c-1`, (2) is a stack of coordinate
selection matrices with selected indices `(tc+i) mod d`. Its rows cover
exactly `min(d,(T+1)c)` distinct standard basis coordinates. Thus its
rank equals the upper bound at every `T`. `MathCan/PhaseObservability.lean`
certifies exact injectivity in the four-coordinate, one-output example.
The standard-library exact rational oracle checks the rank identity for
several other dimensions.

**Proposition 2 (hidden-now, visible-later).** Let
`F(c,a)=(0,c+a)` and `R(c,a)=a` on two real coordinates. For every
`c != 0`, states `(c,0)` and `(0,0)` share the current output, and their
next outputs differ by `c`. Lean proves the same statement over integers,
with the nonzero hypothesis explicit. It is a concrete witness for
`ker DR` being larger than `ker D(R o F)`.

## 2. Exact fibers of a LayerNorm followed by a linear readout

Let an answer-state vector `x` have `d` channels, with mean `mu` and
centered vector `u=x-mu*1`. Write LayerNorm and the linear head as

\[
 R(x)=W\left(\Gamma\frac{u}{\sqrt{\|u\|^2/d+\epsilon}}+
 \beta\right)+b.\tag{4}
\]

Set `H=I-11^T/d`, `A=W Gamma H`, and decompose the centered vector
`u=r+w`, where `r` is its orthogonal projection onto the row space of
`A`, while `w` is orthogonal to that space. Both terms have zero mean.
Take any `w'` satisfying

\[
 w'\in\ker A\cap1^\perp,\qquad \|w'\|=\|w\| .\tag{5}
\]

**Theorem 3 (exact readout fiber).** The state
`x'=mu*1+r+w'` satisfies **all** logit equalities `R(x')=R(x)`.

**Proof.** The centered vector of `x'` is `r+w'`, with the same squared
norm as `u` because `r` is orthogonal to both null vectors. The numerator
of (4) changes by `Gamma(w'-w)`, and the normalization denominator is
unchanged. Applying `W` annihilates the change because `A(w'-w)=0` and
both vectors are centered. The additive bias is unchanged. This covers
all channels of the readout, not only the chosen predicted class, and
holds for the actual nonzero LayerNorm epsilon.

A useful parameterization chooses a desired hidden-state increment
`delta`, projects its centered part into `ker A cap 1^perp`, and uses a
spherical retraction:

\[
 w'=\|w\|\frac{w+\alpha\,\mathrm{Proj}_{\ker A\cap 1^\perp}
 (\delta)}{\|w+\alpha\,\mathrm{Proj}_{\ker A\cap 1^\perp}(
 \delta)\|}.\tag{6}
\]

This gives an exact-logit-invariant perturbation for all `alpha` at
which the denominator is nonzero. The CPU implementation independently
verifies equality of the eight logit values to about `3e-14` absolute.

**Proposition 4 (equal-chord fiber control).** Fix the angle `theta`
between `w` and a target `w'`. Take any unit vector `g` perpendicular
to `w` within `ker A cap 1^perp`, and put
`w_random=cos(theta)*w+sin(theta)*||w||*g`.
Then `||w_random||=||w||`, and
`||w_random-w||=||w'-w||`. Therefore the control preserves the entire
readout while matching the norm of the targeted intervention exactly.
This avoids comparing directional effects with substantially different
perturbation sizes. The direction is random, and the experiment must
report its variability.

## 3. Causal necessity of phase changes

If an update `F` acts on state `(a,c)` and a controller freezes the key
coordinate `a` at each step while allowing `c` to evolve, then an output
function depending only on `a` remains constant for every number of
iterations. This follows by induction regardless of `F`'s context
update. The `PhaseObservability.lean` theorem
`frozen_readout_at_all_depths` formalizes the statement for arbitrary
types, and SPC-05's `PhaseLatch.lean` contains a parallel host-owned
suppression result.

Consequently, correct deep pointer-chase readouts in this control are
possible only when the required hop equals the frozen initial answer,
which can happen naturally when graph-cycle periods divide the number
of remaining steps. The experiment compares the exact all-channel freeze
to suppressing the train-only SVD subspace of answer-token increments.

## 4. Finite results and epistemic boundary

The numerical details and SHA-256 receipts are in `LoopedTransformers`'s
SPC-06 companion folder. It loads the two immutable SPC-04 48-channel
checkpoints; no additional training was done. Two model seeds and three
held-out prompt seeds contribute 384 inputs to the ablation and exact
readout-fiber experiments. The instantaneous margin Jacobian has seven
rows. A separate local observability experiment uses two prompt seeds and
two finite-difference step sizes per model, comparing trained and untrained
weights. The quantitative rank is a *numerical rank* at a stated relative
singular-value threshold, and does not certify an exact neural Jacobian
rank. Full/partial phase intervention classification uses the previously
registered cycle criteria and future-state oracle references.

These experiments distinguish the empirical questions of current readout
invariance and later output recoverability. They establish no generic
capability or safety property of larger models. The analytic readout-fiber
and rank-budget results are paper proofs, while the Lean module covers the
finite algebraic examples and key-freeze induction; no claim of complete
Lean formalization of the real analytic theorems is made.
