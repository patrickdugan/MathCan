# SPC-07: gauge-covariant temporal observability and cross-checkpoint phase transfer

**Date:** 15 November 2026. **Status:** new research synthesis with scoped mathematical proofs and finite Lean specializations. Independent mathematical priority has not been established.

This continues SPC-01 to SPC-06, including the two trained SPC-04 LoopedChase checkpoints, without any new model training. It combines a deferred-state-distinguishability perspective from OpenAI Math family #129, *An exponential two-way deterministic state lower bound for one-way liveness*, with exact linear/Fourier coordinate methods motivated by OpenAI Math family #130, *Finite tensor savings and exact Fourier circuits*. Source: [`openai/math@4eaee875`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints). Neither source paper is asserted to prove a claim about transformers.

## Problem: a raw cross-checkpoint subspace is coordinate-dependent

Let a differentiable recurrent model have hidden column state `x` in `R^d`, evolution `x_{t+1}=F(x_t)`, and a c-output observation `h(x_t)`. At a fixed prompt, depth, and future horizon H, form the stacked **local temporal observability operator**

\[
\mathcal O_H(x)=\begin{bmatrix}Dh(x)\\Dh(Fx)DF(x)\\\vdots\\D(h\circ F^H)(x)\end{bmatrix}\in\mathbb R^{(H+1)c\times d},\qquad G_H(x)=\mathcal O_H(x)^\top\mathcal O_H(x).
\]

For multiple training prompts, normalize each observed Gramian by its squared Frobenius energy before averaging. This fixes the contribution of each training prompt. Let `P_s` and `P_t` denote the top-r orthogonal projectors of source and target averaged Gramians. With independently trained checkpoints, matching hidden neuron indices is a particular coordinate choice and has no reason to preserve `P_s=P_t`.

### Theorem 1: finite-horizon gauge equivariance

Let `g` be any bijection of hidden state space and define

\[
F_g=g\circ F\circ g^{-1},\qquad h_g=h\circ g^{-1}.
\]

Then, for every nonnegative integer n,

\[
\boxed{ F_g^{\circ n}(g x)=g(F^{\circ n}(x)),\qquad h_g(F_g^{\circ n}(g x))=h(F^{\circ n}(x)). }
\]

**Proof.** At n=0 the identity is immediate. If it holds at n, compose `g F g^{-1}` with both sides, cancel `g^{-1}g`, and obtain the case n+1. Apply `h g^{-1}` to the resulting state identity. This proof holds for arbitrary state spaces and exact deterministic recurrences. The whole recursion and observer have to be transported consistently. `MathCan/GramianTransfer.lean` formalizes this theorem with a core `StateGauge` structure (two inverse maps and explicit inverse proofs) and a separately defined finite iterate.

If `g(x)=Q^T x` with Q orthogonal and we write source-to-target **row** vectors as `x_s^T Q=x_t^T`, then the output Jacobians and Gramians transform as

\[
\mathcal O_{H,t}=\mathcal O_{H,s}Q,\qquad G_{H,t}=Q^TG_{H,s}Q.\tag{1}
\]

Thus the right transfer object is a **conjugacy class of Gramians**, and the transported rank-r projector is `Q^T P_s Q`. A raw principal-angle comparison between independently learned hidden bases is gauge-sensitive.

### Theorem 2: sharp spectral transfer-regret bound

For real symmetric positive-semidefinite matrices `G_s,G_t`, let `P_s` maximize `tr(PG_s)` over rank-r orthogonal projectors P. Choose any orthogonal Q and put

\[
A=Q^TG_sQ,\quad P_a=Q^TP_sQ,\quad E=G_t-A.
\]

Let `P_t` maximize `tr(PG_t)` over such projectors. Then

\[
\boxed{0\le\mathrm{tr}(P_tG_t)-\mathrm{tr}(P_aG_t)
\le 2r\|E\|_{op}.}\tag{2}
\]

**Proof.** `P_a` maximizes `tr(PA)` by orthogonal conjugation and the Ky Fan variational principle. Expand the target regret:

\[
\mathrm{tr}((P_t-P_a)G_t)
=\mathrm{tr}(P_tE)+\big[\mathrm{tr}(P_tA)-\mathrm{tr}(P_aA)\big]-\mathrm{tr}(P_aE).
\]

The bracket is nonpositive. Each of the remaining traces has absolute value at most `r ||E||op`, since P has exactly r unit eigenvalues. Nonnegativity follows from optimality of `P_t`. The coefficient two is sharp, already in dimension two: take `G_s=diag(1,1)`, break the tie toward its first axis, choose `G_t=diag(0,2)` and Q=I. Then the target regret is 2 while `r||E||op=1`. The Lean module certifies the generic integer diagonal two-feature case. The higher-dimensional spectral theorem argument is a written proof, not a kernel-checked theorem.

The bound explains both transfer successes and limitations. It requires a small **aligned Gramian difference**; an alignment fitted from phase increments alone need not align every temporally observable direction.

### Theorem 3: phase-margin certificate after compressed intervention

Let `F_t^T` be L-Lipschitz between `x+delta` and `x+P delta`. Write `y=F_t^T(x+delta)` and fix reference states `r_j`. Suppose `c` is the unique nearest reference to `y` and define its **classification margin** `m=min_{j≠c}(||y-r_j||-||y-r_c||)>0`. The triangle inequality gives

\[
\|F_t^T(x+P\delta)-F_t^T(x+\delta)\|
\le L\|(I-P)\delta\|.
\]

The distance to each reference changes by at most the output displacement. Thus a sufficient condition for nearest-reference phase preservation is `2L ||(I-P)delta|| < m`. It is enough to establish an appropriate local Lipschitz constant on the two selected trajectories. In SPC-07, phase agreement is measured empirically; a certified L for the nonlinear transformer is not claimed.

## Experiment: frozen transfer across two separately trained LoopedChase models

Saved checkpoints from SPC-04 are loaded using `torch.load(...,weights_only=True)`, with model-weight SHA256 verified internally. Both have eight pointer nodes, one tied layer, 48 answer-token channels, and 1,200 updates of three-hop supervision. No weights are modified in SPC-07.

- **Temporal observable directions:** at depth 32, collect central-difference gradients of all seven output-logit margins through eight future loops, with 48 answer-state perturbation directions. Form a Frobenius-normalized Gramian per prompt and average over 16 frozen source-only prompts (`920731`). Top-eight eigenvectors define the observable subspace. The same estimator on the target checkpoint is a within-model comparison.
- **Phase subspace:** use SPC-05's uncentered answer-token phase-increment SVD from 256 prompts seeded `904001`, with training-only depths 32, 48, and 64. Eight directions were selected in the prior SPC-05 work.
- **Cross-model alignment:** build 768 paired phase-increment vectors from the same 256 training prompts, then solve orthogonal Procrustes `min_{Q^TQ=I} ||X_s Q-X_t||_F`. Fit a negative control after shuffling the target rows before Procrustes. Apply both Qs unchanged to source subspaces. The target's phase-increment SVD remains a separate fitted reference.
- **Held-out:** use eight seeds `910701` through `910708`, with 64 fresh input graphs each per target checkpoint (1,024 inputs total). Phase is evaluated at depth 64, following an answer-token-only intervention for 12 native recurrence steps. The 790 stable nonfixed task cycles satisfy the preregistered ground-truth pointer period, `relative_cycle_error<1e-4`, `relative_one_step>0.05`, and nonzero phase separation. The other 234 inputs are retained in total-count accounting and excluded from phase-rate denominators.
- **Controls:** source raw basis, paired-aligned source, shuffled-pair-aligned source, target-trained basis, four-to-eight random orthonormal bases, full phase update, and zero update. Both raw projection magnitude and full-update-norm-matched variants are recorded. Cross-checkpoint states themselves are never transplanted.

The native analytic instantaneous readout derivatives and two central-difference step sizes agree at relative errors of order `1e-10`. Train/heldout exact prompt-hash overlap is zero.

### Results: full-displacement phase-change subspaces (r=8, unscaled projection)

| Intervention | Source 41522 → target 41523 (406 cycles) | Source 41523 → target 41522 (384 cycles) | Combined |
| --- | ---: | ---: | ---: |
| Raw source phase basis | 16 | 27 | 43/790 |
| Shuffled-pair Procrustes phase basis | 318 | 294 | 612/790 |
| Properly paired Procrustes phase basis | **404** | **382** | **786/790** |
| Target-fitted phase basis | 405 | 383 | 788/790 |

The paired-alignment advantage over shuffled pairing is 174/790 = 22.0 percentage points. The paired, 16-batch cluster bootstrap (4,000 resamples, seed 771407) yields a 95% interval of 20.5–23.5 points. The paired contingency table has 175 gains and one loss. These are empirical observations on frozen synthetic models.

### Results: temporal-observability subspaces (r=8)

| Intervention | Source→41523 | Source→41522 | Combined |
| --- | ---: | ---: | ---: |
| Raw source temporal basis | 14 | 6 | 20/790 |
| Shuffled-pair aligned temporal basis | 126 | 229 | 355/790 |
| Paired-aligned temporal basis | **192** | **326** | **518/790** |
| Target-fitted temporal basis | 369 | 212 | 581/790 |

With the projected updates rescaled to match the norm of the natural full phase step, the aligned temporal basis shifts 624/790, the shuffled-pair basis 511/790, and the target-fitted basis 638/790. The paired alignment beats shuffled alignment by 14.3 percentage points (95% cluster bootstrap interval 10.3–18.3 points). This norm matching can magnify small projected updates and is labeled as a distinct intervention.

The two raw top-eight temporal subspaces have projector overlap 0.187 in the common hidden-neuron indexing. Paired alignment raises it to 0.453; raw phase-subspace overlap 0.200 rises to 0.876 after alignment. Aligned source temporal directions capture 49.3% of the target Gramian in the 41522→41523 direction and 43.6% in the other, compared with 79.7% and 71.1% for each target's own temporal subspace. A positive causal phase-transfer result can coexist with imperfect temporal-observability transfer.

### Statistical scope and falsifiers

The two trained checkpoints use the same architecture and synthetic task. The paired alignment accesses target hidden activations on unlabeled calibration graphs. Consequently the 786/790 result is **calibrated transfer**, not zero-shot transfer of raw neurons, and it is not evidence about general language-model reasoning or safety. The shuffled-pair control itself performs well, showing that part of the geometry is population-level. To establish stronger task-specific transfer, add distinct task families, independently trained widths, graph perturbations, and held-out calibration distributions. The source paper's automaton lower bound is used only as motivation for deferred distinguishability, not as a theorem about these learned models.

## Reproduction and trust boundary

Run from the repository root after providing the exact SPC-04 checkpoint files:

```bash
python -m experiments.spectral_state_cost_v0.spc07_transfer \
  --checkpoint-dir /path/to/spc04/checkpoints \
  --out /tmp/spc07_full.json \
  --summary-out /tmp/spc07_summary.json
```

The 1.2 MB per-condition audit receipt is preserved separately in the downloadable SPC-07 reproducibility archive. The source repository contains the compact summary and deterministic unit tests. The repository-wide MathCan tests need only the Python standard library; the new applied unit tests use CPU NumPy and PyTorch. Lean checks `MathCan/GramianTransfer.lean` with the pinned project toolchain. `#print axioms` is executed on its named theorems.
