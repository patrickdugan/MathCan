# SPC-08: a deferred-observability quotient for recurrent state and phase memory

**15 November 2026.** Mathematical continuation of SPC-01 through SPC-07, paired
with the frozen two-checkpoint intervention campaign in
`MoralityLabAI/LoopedTransformers/experiments/spectral_state_cost_v0/`.

The original inspiration remains two OpenAI mathematics preprints (source snapshot
`openai/math@4eaee87548250b2682affda7d05d947c05554bae`):

- [*An exponential two-way deterministic state lower bound for one-way liveness*](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026): deferred-context distinguishability.
- [*Finite tensor savings and exact Fourier circuits*](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026): exact coordinate decompositions and gauge changes.

The propositions here are ordinary finite-dimensional linear algebra applied to a
new experimental separation. We make **no claim of mathematical priority** for
the rank identity, classical observability Gramian, or cyclic-register example;
the experimentally testable synthesis and its scoped implementation are new to
this research campaign. The source papers' automaton bounds and nonuniform FFT
circuit-size results are not imported as theorems about neural networks.

## 1. Exact deferred-observability rank budget

Let `V` be a finite-dimensional vector space over any field. Let
`A: V→V` be linear, and `C: V→Y` be a linear readout into `Y` of
finite dimension `c`. Define the horizon-`T` observation map

\[
\mathcal O_T(v) = (Cv, CAv,\ldots, CA^Tv),\qquad
D_T(v)=(CAv,\ldots,CA^Tv),\quad K=\ker C.
\]

**Theorem A (deferred rank quotient).** For every nonnegative integer `T`,

\[
\boxed{\operatorname{rank}\mathcal O_T
=\operatorname{rank}C+\operatorname{rank}(D_T|_K).} \tag{A}
\]

**Proof.** Projection from `im O_T` onto the first output slot has image
`im C`, while its kernel is exactly `{0}×D_T(K)`. Therefore the resulting
short exact sequence

\[
0\to D_T(K)\to\operatorname{im}\mathcal O_T\to\operatorname{im}C\to0
\]

has additive dimensions, giving (A). This proof works over any field.
The second term counts state directions hidden from the present readout
that become distinguishable within `T` future observations.

**Sharp capacity corollary.** Let `r=rank C`. Then

\[
0\le\operatorname{rank}(D_T|_K)\le\min\{\dim V-r,\;T\,\dim Y\}.
\]

For any `d=dim V`, the cyclic shift register on `d` coordinates with
scalar readout of the first coordinate attains
`rank O_T = min(d,T+1)` at **every** `T`. It follows that the bound is
sharp for scalar readout, including the newly revealed dimension
`min(d-1,T)`. This is a useful exact benchmark for linearized neural
readout probes.

## 2. A deferred-only Gramian

For Euclidean `V`, let `N` be the orthogonal projector onto `K=ker C`.
Define the future-output Gramian conditional on present invisibility:

\[
\boxed{G_{\mathrm{defer},T}=N\left[\sum_{t=1}^T
(A^t)^*C^*CA^t\right]N.} \tag{B}
\]

**Proposition B.** The Gramian (B) is positive semidefinite. Its image is
contained in `K`; the quadratic form on `K` is exactly
`||D_T v||²`. Its kernel on `K` is `K∩ker D_T`. Consequently

\[
\operatorname{rank}G_{\mathrm{defer},T}
=\operatorname{rank}(D_T|_K)=\operatorname{rank}\mathcal O_T-\operatorname{rank}C.
\]

**Proof.** Write `G_defer = (D_T N)^*(D_T N)`. For real or complex
inner-product spaces, `ker(M*M)=ker M`; `N` acts identically on `K`,
and `D_TN` has image `D_T(K)`. All assertions follow.

**Proposition C (orthogonal gauge covariance).** For an orthogonal or
unitary `Q`, transform `A'=QAQ*`, `C'=CQ*`, and `N'=QNQ*`. Then

\[
G'_{\mathrm{defer},T}=QG_{\mathrm{defer},T}Q^*.
\]

The eigenvalues and invariant-subspace angles are therefore intrinsic to
an actual coordinate conjugacy. A fitted Procrustes alignment between
independently trained models is only an approximate empirical relation;
these models are not assumed to be exact gauge conjugates.

## 3. The noncommuting problem in trained nonlinear systems

For differentiable recurrence `F`, immediate output `H`, and a fixed
state `x`, use

\[
J_0=D H(x),\qquad
J_t=D(H\circ F^t)(x),\qquad
N_x=I-J_0^\dagger J_0.
\]

The local deferred Gramian is

\[
G_{x,T}^{\rm defer}=\sum_{t=1}^{T}(J_tN_x)^*(J_tN_x).
\]

The empirical training implementation divides by the total finite-horizon
Jacobian Frobenius-squared norm at each training input before averaging.
**Important:** `N_x` varies with `x`, so the pooled Gramian's leading
eigenvectors need not lie in the instantaneous kernel at any given *test*
state. A separate local projection at evaluation time is needed to make
an intervention instantaneously invisible to first order. The nonlinear
LayerNorm head can change current logits at second order after a large
such perturbation.

For a fixed phase-step `δ` at state `x`, write
`δ_row=(I-N_x)δ` and `δ_null=N_xδ`. Then

\[
\|\delta\|_2^2=\|\delta_{\rm row}\|_2^2+\|\delta_{\rm null}\|_2^2.
\]

The phase-transition behavior of these pieces is **not** additive:
`F^T(x+δ)` may enter a different discrete phase basin while both
`F^T(x+δ_row)` and `F^T(x+δ_null)` fail to do so. This explains why a
rank or energy budget alone cannot certify causal phase transfer.

## 4. Exact finite witness and the meaning of delayed information

Take `V = R²`, `A(a,b)=(b,a)`, `C(a,b)=a`. Presently hidden perturbations
are `(0,b)`, which leave `C` unchanged, while

\[
CA(0,b)=b,\qquad C(a,0)=a,\qquad CA(a,0)=0.
\]

The first and second observations therefore recover the whole state,
`O_1(a,b)=(a,b)`. Here `G_defer=diag(0,1)`: the future-visible direction
is exactly orthogonal to the immediate readout direction. The
three-cell cyclic register similarly requires three scalar outputs.

`MathCan/DeferredObservability.lean` formally certifies these concrete
witnesses over arbitrary natural-number coordinates, including future-only
distinguishability and two-/three-observation injectivity. The general
field-independent rank proof and real/complex Gramian identities above
are paper arguments. `tests/test_deferred_observability.py` independently
checks rank (A) over exact rationals on 450 seeded small matrices, all
small cyclic-register horizons, and gauge invariance under coordinate
permutations. The Lean target imports only `Init`, with `#print axioms`
for the new named theorems.

## 5. Implications for computational phase control

SPC-07's finite-horizon Gramian mixes immediate and delayed sensitivity.
SPC-08 fits a second Gramian after removing immediate-output directions
**for each training input**. The phase basis and deferred-only basis occupy
nearly orthogonal rank-eight subspaces in the frozen 48-channel trained
pointer models. An eight-dimensional phase projection produces a near-
perfect phase transplant; projecting the same natural phase step into
the deferred-only subspace produces few phase transplants. Equal-
norm interventions remain much less effective in the deferred-only
subspace, with the caveat that they amplify small projections and are
out-of-distribution modifications.

The empirical effect is scoped to two independently trained synthetic
checkpoint seeds. It is not a theorem about generic models. Readout-
null directions still influence future outputs, and some exactly
readout-preserving interventions change the recurrent phase. These
features make the interpretation a decomposition of **what the probe
measures**, not a claim that neural computation has cleanly separated
semantic modules.
