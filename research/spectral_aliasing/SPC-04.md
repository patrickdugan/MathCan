# SPC-04: superattracting computation, monodromy, and exponential phase memory

Date: 15 November 2026. New bounded mathematical synthesis developed while extending
`LoopedTransformers`' SPC-03/J to a native trained-checkpoint experiment.

The motivational source pair remains OpenAI Math 2026 [#129](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026) (future-query state distinctions) and [#130](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026) (exact Fourier/tensor-coordinate constructions).
The source papers' headline theorems are neither required nor attributed to
this experiment. The results below follow by direct algebra and elementary
finite-state reasoning. No external priority audit has been conducted.

## 1. Empirical question

SPC-03/J found that an **untrained** native `LoopedChase` recurrent map
`h_{t+1}=F_e(h_t)` converges to a fixed point. Does supervised pointer-chase
training eliminate the phase structure, or can successive recurrent loops
carry distinct computational states while *all local Jacobians contract*?

Train only at loops 1, 2 and 3, with target the corresponding hop of an
8-node random permutation. For fair extrapolation, at evaluation loop `t`
compare the readout with the **t-th hop**, as well as separately recording
whether the readout retains the third-hop answer. The latter measures a
different problem, answer retention, and must never be described as
continued pointer-computation accuracy.

See the pinned `LoopedTransformers` SPC-04 receipt. Training uses two seeds,
1,200 AdamW steps, 64 samples per update, a native 48-wide one-layer model,
and three disjoint held-out seeds with 512 samples each. Float64 full-state
Jacobian probes are taken after training, and the same initial weights are
used for untrained controls.

## 2. Full-period Jacobian and why one-step radii do not suffice

For a differentiable map `F` with a p-cycle `x_0,...,x_{p-1}` satisfying
`F(x_i)=x_{(i+1) mod p}`, set `A_i=D F(x_i)`. The derivative of its
p-step return map is

\[
M=D(F^p)(x_0)=A_{p-1}\cdots A_1 A_0.
\tag{1}
\]

This order follows from the chain rule and is essential: the matrices need
not commute. The eigenvalues of `M` are the Floquet multipliers. If their
moduli are all less than one, the periodic orbit is locally attracting for
an exactly periodic `C^1` map. A numerical experiment on an approximate
periodic orbit supplies an estimate, not an exact certification.

**Exact counterexample (one-step spectral radii can deceive).** For any
real `q>1`, put

\[
 A_q=\begin{pmatrix}0&q\\0&0\end{pmatrix},\qquad
 B_q=\begin{pmatrix}0&0\\q&0\end{pmatrix}.
\]

Both square to zero and have spectral radius zero, while

\[
 B_q A_q=\begin{pmatrix}0&0\\0&q^2\end{pmatrix},
 \qquad \rho(B_q A_q)=q^2>1.
\tag{2}
\]

Thus the individual spectral radii `rho(A_i)<1` cannot certify contraction
of the product. The SPC-04 gym explicitly differentiates every constituent
loop before estimating the product's leading eigenvalues. This is a standard
noncommutative-matrix phenomenon; its role here is an exact falsification
control for single-Jacobian interpretations.

## 3. A full-dimensional phase-memory theorem with vanishing tangents

**Theorem (superattracting phase memory).** For every integer `p>=2` and
`m>=1`, there is a real polynomial map `F:R^m -> R^m` possessing an invariant
set `S` of `p^m` distinct points such that

* each point of `S` belongs to an exact orbit of least period `p`;
* the Jacobian `D F` vanishes at **every** point of `S`, so every orbit's
  monodromy matrix is the zero matrix;
* an identity readout on `S` has `p^m` distinguishable values, requiring at
  least `p^m` distinct exact internal memory states in any deterministic
  encoder-decoder that reproduces the whole readout.

**Construction and proof.** Pick distinct real node values
`a_0,...,a_{p-1}`. Let

\[
 L_i(x)=\prod_{j\ne i}\frac{x-a_j}{a_i-a_j},\qquad
 H_i(x)=\bigl[1-2L_i'(a_i)(x-a_i)\bigr]L_i(x)^2.
\]

Hermite cardinal interpolation gives
`H_i(a_j)=1_{i=j}` and `H_i'(a_j)=0` for every `i,j`.
Define

\[
 f(x)=\sum_{i=0}^{p-1} a_{(i+1)\bmod p}H_i(x).
\tag{3}
\]

It follows that `f(a_i)=a_{i+1 mod p}` and `f'(a_i)=0`.
Now set `F(x_1,...,x_m)=(f(x_1),...,f(x_m))` and
`S={a_0,...,a_{p-1}}^m`. Every application simultaneously advances all
coordinate phases by one, giving an orbit of least period `p` at each
state. There are `p^m` points partitioned into `p^(m-1)` distinct cycles.
All entries of `D F` are zero on `S`, hence every monodromy is zero.
Finally, if a deterministic exact monitor `encode:S->M` and decoder
`decode:M->S` satisfy `decode(encode(s))=s`, then `encode` is injective;
thus `|M|>=p^m`, requiring at least `ceil(m log_2 p)` bits for fixed-length
binary encoding. This completes the proof.

For `p=2`, choose nodes `0,1`. Equation (3) simplifies to

\[
 f(x)=1-3x^2+2x^3,\qquad f'(x)=-6x+6x^2.
\tag{4}
\]

Direct substitution gives `f(0)=1`, `f(1)=0`, `f'(0)=f'(1)=0`.
An `m`-coordinate product has `2^m` pairwise distinct attracting
period-two phase states, each with a **zero** one-step Jacobian.

**Interpretive consequence.** Vanishing tangent rank near a recurrent
attractor gives no upper bound on the number of globally distinguishable
computational phases. In particular, local Jacobian compression, local
contraction, and low-dimensional linear probes must be interpreted
alongside global phase-distinction tests and cycle-aware readouts.

This construction uses elementary Hermite interpolation and a product of
finite cycles. The combined separation theorem and its use in looped
activation diagnostics are recorded here as part of SPC-04; no claim of
being the first to observe these classical ingredients is made.

## 4. Sampled observations and true task periods

Suppose a trajectory `x_t` has exact least period `p`. Observing it every
`d` loops visits exactly `p/gcd(p,d)` distinct phases, since the additive
subgroup generated by `d` in `Z/pZ` has that cardinality. For a synthetic
pointer orbit, the sequence `x_t` advances the start node through one
cycle of the input permutation; thus its target-answer period is exactly
that component's cycle length. The full transformer hidden state may have
an equal, shorter, longer, or transiently unstable period, and must be
measured independently. SPC-04 evaluates all candidate lags 1..8.

The native experiment finds a separate issue: after training on hops 1..3,
a model can continue executing the pointer transition, so its readout at
loop 42 may correctly predict hop 42 while differing from hop 3. Returning
to hop-3 labels at late depth creates a false appearance of lost capability.

## 5. Verification boundaries

`MathCan/PhaseMemory.lean` kernel-checks the exact polynomial two-cycle,
its zero first derivative at the two nodes, the nilpotent-matrix
counterexample for `q=2`, finite Boolean-phase toggle, and a generic
injectivity lemma. It does **not** formalize arbitrary-dimensional real
Hermite interpolation, spectral-radius convergence, or the trained-model
measurements. `tests/test_phase_memory.py` independently evaluates exact
rational Hermite interpolants for multiple periods and several products.

An observed tiny `||F^p(x_t)-x_t||` supports an approximate periodic orbit;
only an exact invariant equality would qualify for the theorem's Floquet
hypothesis. Numerical Ritz eigenvalues from Arnoldi are annotated as
estimates, with convergence flags and an independent measure of period
closure. The trained experiment is restricted to tiny synthetic pointer
graphs and two initialization seeds. Training and testing a serious
looped-transformer checkpoint remains a separate, larger experiment.
