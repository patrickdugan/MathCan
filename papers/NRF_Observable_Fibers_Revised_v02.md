---
title: "Task-Conditioned Observable Fibers in Short-Trained Tied Residual Networks"
subtitle: "Readout regularization, dark-state Jacobian coupling, and exact quotient limits (NRF-01–11 with post-review diagnostics)"
author: "Morality Lab — research working draft"
date: "15 November 2026 · Revised working draft v0.2"
lang: en
abstract: |
  A task-optimized readout of a recurrent network can suppress task error while retaining sensitivity to hidden coordinates. We analyze this problem in 128-dimensional tied residual MLP loopers trained for only 16 or 32 AdamW updates on a synthetic signed-permutation task. Our main empirical comparison matches 80 readout-optimizer updates while keeping the recurrent weights fixed. At depth 32, a task-only readout attains mean held-out task MSE 0.1493, Jacobian leakage 0.5122 and J=MSE+leakage² of 0.4117. A leakage-aware readout attains MSE 0.2476, leakage 0.3184 and J=0.3526. It therefore reduces leakage by 37.8% relative to the equal-budget control while increasing task MSE by 65.8%; the joint objective improves by 14.4% at a previously selected penalty weight. The original supervised readout is a weaker comparator. The preregistered depth-32 gate passes in five of six model seeds and repeats on fresh draws from the same distribution. Post-review exploratory controls show substantial leakage at zero model-training steps, and a scale-normalized coupling ratio of 0.733 for task-only versus 0.439 for leakage-aware readouts at depth 32. We also establish a written, classical-style one-step full-domain obstruction to proper exact linear quotients under full-support assumptions, with a strictly positive global differential leakage floor. This neither rules out an exact quotient of an iterate nor guarantees generalization to new models or language tasks. NRF records the campaign's historical numerical-range/fixed-point starting point; later results are mathematically independent of those preprints.
keywords:
  - mechanistic interpretability
  - recurrent networks
  - observability
  - low-rank projections
  - nonnormal dynamics
  - Jacobian leakage
  - model reduction
---

**Working manuscript, v0.2 after substantive review.** Empirical source: MoralityLabAI/LoopedTransformers; mathematical source: patrickdugan/MathCan. The experiment archive contains the merged NRF-01–11 campaign as of 15 November 2026. Post-review measurements are explicitly exploratory, were calculated after inspecting earlier outcomes, and have separate local CSV and source-code receipts. Formalization claims apply to the listed Lean lemmas rather than the complete real-analytic theorems. This draft is intended for technical review.

# 1. Introduction

A recurrent computation can encode a useful task answer in a small set of directions while continuing to exchange information with much larger hidden coordinates. A decoder that predicts the correct target can therefore conceal a dynamic dependence on unobserved state. This matters for compact-model design and mechanistic interpretation, because the same low-rank representation may perform well on a task and respond strongly to perturbations outside the representation.

The model's readout can ignore directions that remain active in its recurrent transition. Sharma and Vu describe a closely related readout blind spot for hidden-state scale under normalized outputs in looped language models [15]. Our experiment focuses on a different finite-dimensional question: how much do local recurrent Jacobians map discarded rank-eight directions into an observed subspace, and how much task performance must a readout trade away to reduce that coupling? The relevant antecedents include exact dynamical lumpability and invariant-subspace methods [16,17].

We primarily report an *observer-training* intervention. Across six frozen depth-32 models, 80 optimizer updates without a leakage penalty already improve the task and reduce absolute leakage substantially. Adding an explicit leakage term reduces leakage further and improves a chosen combined score, while sacrificing task accuracy relative to that equal-budget control. The numerical-range and fixed-point constructions that began this project are retained as historical context. The later full-domain obstruction and low-rank observer experiments do not rely on either of the two OpenAI preprints as proof inputs.

Our contributions are a precisely scoped full-domain **one-step** linear-quotient obstruction with a positive global differential leakage floor; finite-depth tangent transport and projector identities; controlled, short-training synthetic model measurements; and a post-review audit of normalization, initialization and the penalty frontier. We attribute these specializations to established invariance and model-reduction mathematics and make no claim of universal mathematical priority.

# 2. Model and observable-fiber measurements

## 2.1 Tied residual recurrence

The trained toy architecture has state dimension $d=128$ and a shared residual block

$$
F(h)=\alpha h+\beta\bigl[W_2\tanh(W_1h+b_1)+b_2\bigr],
\qquad \alpha=1,\quad\beta=0.25.
$$

The same map is applied $R\in\{16,32\}$ times. Each $W_i$ is $128\times128$. Training uses AdamW (learning rate $10^{-3}$, zero weight decay) and batch size eight, with only **16 or 32 optimizer updates** in the matched-step cohort. The models therefore see **128 or 256 stochastic training examples**, with a signed-permutation teacher of Gaussian input features. State-visit exposure counts multiply optimizer steps by batch size and recurrent depth; they are not distinct training examples. The task evaluation asks for the first eight signed, tanh-transformed teacher features. This is a tied residual multilayer-perceptron looper, **not a full attention-based transformer**.

For each model, we inspect the midpoint state $h_{R/2}$ and the tangent of the remaining $R/2$ visits, $T_R(h)=D(F^{R/2})(h)$. A rank-eight observation is represented by an orthonormal $U\in\mathbb R^{128\times8}$ and its orthogonal projector $P=UU^\top$; the discarded subspace has projector $Q=I-P$. A linear ridge head predicts the task from $U^\top h_{R/2}$, with ridge coefficient one and training labels restricted to the designated training fold.

## 2.2 Error and leakage

For held-out task labels $y_i$ and predictions $\hat y_i(U)$, define

$$
E(U)=\frac1{8n}\sum_{i=1}^n\|\hat y_i(U)-y_i\|_2^2.
$$

The local dark-to-observed Jacobian coupling at a midpoint state $h$ is

$$
\ell_R(U;h)=\frac1{\sqrt8}\|U^\top T_R(h)(I-UU^\top)\|_F.
$$

The reported leakage is the **mean local norm** $L(U)=m^{-1}\sum_{j=1}^{m}\ell_R(U;\tilde h_j)$ over $m=12$ independently generated shadow states. The combined score is

$$
\mathcal J_\lambda(U)=E(U)+\lambda L(U)^2,
\qquad \lambda=1.
$$


A scale-normalized diagnostic decomposes the observer's total write gain at each shadow state:

$$
W_R(U;h)=\frac{\|U^\top T_R(h)\|_F}{\sqrt8},\quad
G_R(U;h)=\frac{\|U^\top T_R(h)U\|_F}{\sqrt8},\quad
\rho_R(U;h)=\frac{\ell_R(U;h)}{W_R(U;h)}.
$$

For nonzero $W_R$, $\rho_R\in[0,1]$ is invariant under global rescaling of the Jacobian and measures the fraction of *observed write energy* entering from discarded directions. We report means of per-state ratios, alongside mean $W_R$ and $G_R$. A small $W_R$ can still make the ratio unstable, so these accompanying gains matter. The identity $W_R^2=G_R^2+\ell_R^2$ holds per state.

The value $\lambda=1$ was chosen after inspecting NRF-04. Later preregistrations hold it fixed but remain **exploratory with respect to the penalty choice**. All held-out statements use their registered fold and model cohort.

## 2.3 Controls and independent units

The initial task-supervised basis is obtained from train-only state/teacher cross-covariance followed by orthonormalization. Each checkpoint also receives eight independently sampled equal-rank random bases, a shifted-label null, and a first-eight-coordinate observation. The random comparator is

$$
\operatorname{median}_{i=1}^{8}\bigl[E(U_i)+\lambda L(U_i)^2\bigr].
$$

We take the median **after** forming each complete random-arm objective. Computing separate medians of $E$ and $L$ would change the comparison. The signed margin is $m=\mathcal J_\lambda(U_{\rm sup})-\operatorname{median}_i\mathcal J_\lambda(U_i)$; a negative margin favors the supervised readout. The independent empirical units are training seeds, rather than the individual shadow states or reused input folds.

# 3. Exact mathematics and its scope

## 3.1 Historical numerical-range and fixed-point motivation

NRF initially meant Numerical Range Fixed-Point. Its NRF-01/02 exercises used Jordan-block numerical ranges and finite-dimensional contraction cycles. The archive cites OpenAI's September 2026 preprints on the *complete* Crouzeix inequality [1] and nonexpansive maps in reflexive Banach spaces [2]. Both documents are present in OpenAI's official Math release list as families 325 and 328. Their global claims belong to the original authors and require independent mathematical review. For the classical scalar Crouzeix conjecture, Jin's July 27 manuscript preceded those documents, and Lorist and Schwenninger posted an independent argument on August 4 [13,14]. The chronology and scalar-versus-complete distinction are explicit here.

The only fixed-point claim used in NRF-01's toy certificate is the standard finite-dimensional contraction principle: if a periodic composition has phasewise Lipschitz bounds $r_i$ satisfying $\prod_i r_i<1$, it has a unique attracting orbit. Its proof and associated disturbance bounds are self-contained [5,6]. Neither this claim nor the following exact-quotient result depends on the correctness of the general OpenAI preprints. The **NRF label is historical**, and the remainder of this manuscript is about observable fibers and trained low-rank readouts.

## 3.2 Factorization and the full-domain obstruction

A linear observation $C$ gives an exact deterministic quotient if there is a map $f$ with $CF(x)=f(Cx)$ throughout the state space. This is equivalent to preserving the fibers of $C$: whenever $Cx=Cy$, one has $CF(x)=CF(y)$. For smooth $F$, exact factorization requires the observation rowspace $S=\operatorname{row}(C)$ to remain invariant under every Jacobian of $F$.

**Proposition 1 (full-domain linear quotient obstruction; written proof).** Assume $W_1,W_2$ are invertible, $\beta\ne0$, and every entry of $W_1W_2$ is nonzero. For the tanh residual map in Section 2 on all of $\mathbb R^{128}$, an exact deterministic quotient through any nonzero linear $C$ must have full rank 128.

*Argument.* Write

$$
DF(x)=\alpha I+\beta W_2D(x)W_1,
\quad D(x)=\operatorname{diag}\bigl(\operatorname{sech}^2(W_1x+b_1)\bigr).
$$

Invertibility of $W_1$ and the full real domain let the diagonal gates vary independently. Invariance under their differences therefore forces rowspace invariance under every rank-one matrix $(W_2e_j)(e_j^\top W_1)$. If $S$ contains a nonzero row $s$, invertibility of $W_2$ supplies some $j$ with $sW_2e_j\ne0$, forcing row $e_j^\top W_1$ into $S$. Full nonzero support of $W_1W_2$ propagates this inclusion to all rows $e_\ell^\top W_1$. Those rows span the full state space. The complete proof and a positive global differential leakage floor are in the paired MathCan analysis [7]. The assumptions are generic for independently and continuously sampled square weight matrices: invertibility and nonzero entries of the matrix product each fail on proper polynomial zero sets, hence on a set of Lebesgue measure zero. The finite-field witnesses show that these exact stored checkpoint matrices satisfy the hypotheses; they do not establish an unusual architecture property.

For a proper rank-$k$ orthogonal projector $P$, write $a_j=W_2e_j$, $b_j=W_1^\top e_j$, $h_*=\min_{j,\ell}|(W_1W_2)_{j\ell}|>0$, $A=\max_j\|a_j\|_2$, $B=\max_j\|b_j\|_2$, $\sigma_i=\sigma_{\min}(W_i)$, and $n=128$. The written global bound states

$$
\max_j \|Pa_j\|_2\,\|(I-P)b_j\|_2
\;\ge\; \frac{h_*}{2\sqrt n}\min\!\left(\frac{\sigma_2}{A},\frac{\sigma_1}{B}\right)>0,
\qquad
\sup_{x\in\mathbb R^n}\|P\,DF(x)(I-P)\|_{op}\;\ge\;|\beta|\max_j\|Pa_j\|_2\,\|(I-P)b_j\|_2.
$$

This is a **uniform one-step, all-states lower bound**. Its numerical value can be very small, and it is not a bound on the finite-sample, $R/2$-step leakage used in the experiments. The lack of a one-step factorization through $C$ also does not rule out a factorization of $F^m$ through $C$: a planar quarter-turn has no real invariant rank-one observation, while its square $-I$ factors through every linear observation. Accordingly the full-domain theorem supplies no impossibility statement for the measured iterated tangents. The exact-quotient formulation is a specialization of classical nonlinear lumpability and invariant-subspace criteria [16,17].

The premise was checked on twelve original binary32 checkpoints (three seeds $101,103,107$, depths 16/32, two exposures). Exact integer scalings of the stored weights yield nonzero modular determinants for both matrices and **16,384 nonzero product residues per checkpoint**, or 196,608 supported matrix-product entries across all twelve. A nonzero modular determinant certifies nonsingularity of the original rational matrix. The Lean files prove selected family-closure and support-propagation lemmas; the full real-matrix analytic theorem remains a written proof with arithmetic checks.

This is an obstruction to *global, exact, proper, linear* quotients. It permits approximate low-rank observations on a restricted data distribution, a finite time horizon, or a nonlinear observation map. The empirical intervention below addresses precisely such a restricted objective.

## 3.3 Jordan shear depth crossover

For $N=E_{12}$ with $N^2=0$ and $J=aI+bN$,

$$
J^R=a^RI+Ra^{R-1}bN.
$$

For a rank-one projection at angle $\theta$ to the first coordinate, an isotropic target with projection error $E=\sin^2\theta$ has coupling magnitude $L_R=R|a|^{R-1}|b|(1-E)$. Comparing two fixed projections with $E_A<E_B$ gives the crossover

$$
\lambda_*(R)=\frac{1}{R^2|a|^{2R-2}b^2(2-E_A-E_B)}.
$$

At $a=1$, doubling depth quarters the crossover penalty. The formula isolates a simple nonnormal mechanism; the learned projections and nonlinear tangent products in the experiments change with depth, so the Jordan law is an explanatory baseline rather than a fitted model of the empirical curves [7].

## 3.4 Transport of hidden-to-visible sensitivity

For the first $s$ tangent steps $T_s$ and the following $u$ steps $S_u$, the full tangent is $S_uT_s$. The cross-fiber block decomposes exactly as

$$
PS_uT_sQ=(PS_uP)(PT_sQ)+(PS_uQ)(QT_sQ).
$$

Its squared Frobenius norm contains the two component energies and twice their inner product. The first component transports preexisting leakage; the second injects influence arriving from the discarded sector during the added suffix. The interference term may be positive or negative, so increased recurrence depth alone does **not** imply monotonically increasing leakage. A planar rotation supplies an elementary cancellation example. This identity was used for an exploratory frozen-midpoint diagnostic in NRF-08X [5,7].

## 3.5 Geometry of a trainable observation subspace

For $U^\top U=I_8$, $P=UU^\top$ and any Jacobian $T$, orthogonal decomposition gives

$$
8\ell_T(U)^2=\|U^\top T\|_F^2-\|U^\top TU\|_F^2.
$$

It avoids constructing an explicit basis for the 120-dimensional complement. For two rank-eight orthogonal projectors $P,P'$, the finite-dimensional motion bound is

$$
|\ell_T(P')-\ell_T(P)|\le
\frac{2\|T\|_{\rm op}}{\sqrt8}\|P'-P\|_F.
$$

NRF-10 optimizes the smooth calibration penalty $m^{-1}\sum_j\ell_T(U;h_j)^2$, while evaluation uses $\bigl(m^{-1}\sum_j\ell_T(U;h_j)\bigr)^2$. Their difference is the sample variance of the local leakage values and is nonnegative. The Gram and projector-motion identities have written proofs and exact-rational oracles; the corresponding Lean module formalizes smaller semiring interference fragments, **not the full real-analytic bounds** [8].

# 4. Depth effects before observer optimization

## 4.1 Readout utility versus coupling (NRF-04–07)

The original NRF-04 experiment used twelve saved tied-loop checkpoints. Task-supervised rank-eight projections beat equal-rank random controls on held-out task MSE in all 12 cells and showed greater local shadow-state coupling in all 12. At the final exposure, median relative MSE improvement was 32.4%, paired with a 14.4% increase in leakage. Under the originally registered joint utility/leakage gate, the leakage condition failed. NRF-05's exact full-domain obstruction explains why zero leakage should not be expected from a proper rank-eight *global* quotient, although it does not predict the observed local leakage magnitudes.

NRF-06 froze the original model weights and decoders while replacing task and shadow evaluation inputs with fresh folds. NRF-07 then trained new models at three previously unused seeds, fixing $\lambda=1$ and the evaluation procedure. Table 1 records means over final checkpoints; the control value is the per-checkpoint median of eight complete random-arm objectives, averaged over seeds.

| Study | Trained visits | Supervised mean $\mathcal J$ | Random-control mean median $\mathcal J$ | Supervised wins |
|:--|--:|--:|--:|:--|
| NRF-06, fresh inputs | 16 | 0.4253 | 0.5731 | 3/3 |
| NRF-06, fresh inputs | 32 | 1.3459 | 1.0498 | 0/3 |
| NRF-07, new model seeds | 16 | 0.4064 | 0.5712 | 3/3 |
| NRF-07, new model seeds | 32 | 1.2962 | 1.0595 | 0/3 |

**Table 1.** Fresh-fold and new-seed results at 4,096 state-visit exposures, comparing the frozen supervised observation with eight random observations. The new-seed replication remains within the same architecture and teacher family [5].

## 4.2 Suffix-only intervention (NRF-08X)

NRF-08 registered a strict checkpoint-byte match before an intervention that extends only the Jacobian suffix while keeping the learned model, midpoint representation, observer, ridge head, and task MSE fixed. The regenerated checkpoint `.pt` files **did not reproduce the archived byte-level SHA-256 hashes**. Their baseline numerical results matched within $5\times10^{-15}$, and an independent dense-tangent audit matched reverse-JVP leakage within $10^{-9}$. The preregistered strict replay gate therefore remained blocked; the resulting **NRF-08X** measurements are treated as exploratory reconstruction evidence.

Within those reconstructions, increasing the suffix from eight to sixteen visits changed the random-versus-supervised ranking for all three depth-32-trained models. Their mean signed margin moved from $-0.0351$ to $+0.2367$ with unchanged task predictions. The block-interference term was positive in all 72 sampled shadow states, accounting for roughly 45.5–46.2% of the final mean squared leakage across six reconstructed models. These measurements motivate a causal mechanism in this toy family while retaining the byte-identity caveat.

## 4.3 Matching optimizer updates (NRF-09)

The depth-16 model at 4,096 visits had received 32 AdamW steps (256 input examples), while depth 32 had received only 16 (128 examples). NRF-09 trained six fresh paired task/model seeds (131, 137, 139, 149, 151, 157) at both depths and evaluated after equal counts of 16 and 32 optimizer updates. Within each seed, both depths consumed the same ordered minibatches; new task and shadow folds were reserved for evaluation.

| Depth | AdamW steps | State visits | Supervised wins | Mean supervised $\mathcal J$ | Mean random median $\mathcal J$ |
|:--|--:|--:|:--|--:|--:|
| 16 | 16 | 2,048 | 6/6 | 0.4612 | 0.5926 |
| 16 | 32 | 4,096 | 6/6 | 0.4020 | 0.5616 |
| 32 | 16 | 4,096 | 0/6 | 1.2821 | 1.0463 |
| 32 | 32 | 8,192 | 1/6 | 0.9696 | 0.9136 |

**Table 2.** NRF-09 matched-optimizer study. At 32 steps, both registered directional cohort gates passed, with one depth-32 seed (157) favoring the supervised decoder [9].

Let $m(R,u)$ denote the signed margin for depth $R$ after $u$ optimizer steps. The exact accounting identity

$$
\underbrace{m(32,16)-m(16,32)}_{0.395476}
=\underbrace{m(32,32)-m(16,32)}_{0.215683}
+\underbrace{m(32,16)-m(32,32)}_{0.179793}
$$

shows that an additional sixteen updates to depth 32 account for 45.46% of the original equal-visit contrast **along this comparison path**. This is an arithmetic decomposition of measured margins, not a path-independent causal attribution. An exact median-Lipschitz drift bound certifies retrospective winner persistence for all six depth-16 models and none of the six depth-32 models [9,10].

# 5. Leakage-aware rank-eight observers (NRF-10)

NRF-10 keeps all recurrent weights frozen at their NRF-09 32-update values. It optimizes a rank-eight observation basis using QR retraction and 80 Adam steps ($\mathrm{lr}=0.02$). The task-only control receives the same optimizer budget and initial supervised basis. The joint arm minimizes train-fold task loss plus $\gamma$ times mean *squared local leakage* over twelve calibration states. Candidate $\gamma\in\{0.05,0.2,1\}$ is chosen on calibration fold 9, requiring calibration MSE no greater than $1.10$ times the original supervised baseline. Task MSE on fold 10 and shadow leakage on fold 11 are evaluated once following selection.

| Depth | Observer | Held-out MSE | Mean local leakage | Mean $\mathcal J$ |
|:--|:--|--:|--:|--:|
| 16 | Supervised baseline | 0.2379 | 0.4169 | 0.4118 |
| 16 | Task-only, 80 updates | 0.1262 | 0.3759 | 0.2676 |
| 16 | Joint leakage-aware, 80 updates | 0.1540 | 0.3158 | **0.2544** |
| 32 | Supervised baseline | 0.2761 | 0.8381 | 0.9788 |
| 32 | Task-only, 80 updates | 0.1493 | 0.5122 | 0.4117 |
| 32 | Joint leakage-aware, 80 updates | 0.2476 | 0.3184 | **0.3526** |

**Table 3.** Frozen-weight NRF-10 readout results. Each cell aggregates six model seeds. The group mean of $\mathcal J$ is not obtained by squaring the group mean leakage [11].

The **equal-budget task-only arm is the principal comparator**. At depth 32, its task MSE of $0.1493$, leakage $0.5122$, and joint score $0.4117$ become task MSE $0.2476$, leakage $0.3184$, and score $0.3526$ under leakage-aware optimization. Thus the penalty reduces leakage by **37.8% relative to task-only** and improves the combined score by **14.4%**, while task MSE increases by **65.8% relative to task-only**. Across six seeds, the joint observer improves the chosen score over task-only in all six depth-32 models and all six depth-16 models.

The weaker, unoptimized supervised baseline has leakage $0.8381$. Task-only optimization already explains roughly **62.7% of the absolute leakage reduction** from this baseline to the joint arm; the explicit penalty explains the remaining 37.3% on that additive accounting path. The preregistered task budget was anchored to **1.10 times this unoptimized baseline**, so it permits substantial regression from the much better task-only readout. The gamma penalty remains selected from a fixed post-NRF-04 objective with $\lambda=1$. The depth-32 preregistered compound gate passes **5/6** models against the required threshold of at least 4/6, but that compound gate compares task error with the weak supervised baseline. Seed 149 is a counted failure: its held-out task-error ratio was $1.1011$ against the maximum $1.10$. Depth 16 passes 6/6. The optimized observer retains strictly positive measured leakage, consistent with the distinction between a useful local readout and an exact global quotient.

# 6. Unchanged-observer transfer (NRF-11)

NRF-11 reconstructs the selected NRF-10 bases using the original training and calibration data and checks their selected $\gamma$ and scores against sealed receipts. It then freezes their bases and ridge heads *before* opening fresh task fold 12 and shadow fold 13. Twelve saved adapter files retain basis coefficients, heads, selected penalties, and source checkpoint hashes. The transfer tests only **sampling stability within an unchanged synthetic teacher family**, using the same models, learned projectors, and task seeds. It provides no new model/task cohort and should not be described as cross-distribution generalization.

| Depth | Observer | Mean held-out $\mathcal J$ on folds 12/13 | Mean leakage |
|:--|:--|--:|--:|
| 16 | Supervised baseline | 0.4192 | 0.4165 |
| 16 | Task-only | 0.2698 | — |
| 16 | Frozen leakage-aware | **0.2540** | 0.3154 |
| 32 | Supervised baseline | 0.9841 | 0.8364 |
| 32 | Task-only | 0.4202 | — |
| 32 | Frozen leakage-aware | **0.3515** | 0.3176 |

**Table 4.** Fresh-fold NRF-11 scores, with no readout refit after the original NRF-10 selection. A dash indicates an omitted table statistic, not a zero measurement [12].

The depth-32 compound gate again passes 5/6, with seed 149 missing the task-error budget (ratio $1.1139$). The depth-16 cohort passes 6/6. For all twelve frozen observers, the joint score beats the original supervised readout, the equal-budget task-only control, and the median of eight random controls. Mean depth-32 joint $\mathcal J$ changes from $0.3526$ (NRF-10) to $0.3515$ (NRF-11), consistent with stable sampling from the same synthetic Gaussian distribution. The change is descriptive rather than evidence of generalization to another task family.

A repository-native replay bug discovered during publication review is also documented: NRF-10 initially imported the NRF-09 generator that intentionally rejected folds outside 1/7/8. The NRF-11 integration repaired the fold contract for 9–13 using the identical registered Gaussian stream and teacher, with parity tests and an independent saved-adapter replay. The fix changes admitted fold indices and leaves the generated data formula and selection settings intact [12].

# 7. Post-review exploratory controls: initialization, normalization, and the penalty frontier

The original protocol measured absolute dark-to-observed coupling, but it did not distinguish a readout that suppresses coupling from one whose overall observed gain is small. The following diagnostic was run after the first manuscript review using the **same six model seeds**, saved NRF-11 observers, and already exposed folds 12/13. It is a retrospective sensitivity analysis and is excluded from the NRF-10 preregistered gate.

## 7.1 Step-zero baseline and gain decomposition

We reconstructed model weights at **zero optimizer steps** from each of the six NRF-09 initialization seeds for each depth. The network weights had seen no training examples; we still fitted the rank-eight supervised projection and ridge head on fold 1, as in the later readout protocol. The task error was measured on fold 12 and tangent leakage on shadow fold 13. For trained models we loaded the original hash-verified checkpoint and the saved NRF-11 observer adapter, comparing their recomputed shadow leakage with the recorded results to $10^{-8}$.

| Depth | Observer | Absolute leakage $L$ | Normalized fraction $\bar\rho$ | Write gain $\bar W$ | Within gain $\bar G$ |
|:--|:--|--:|--:|--:|--:|
| 16 | Step-zero supervised | 0.5792 | 0.4305 | 1.3444 | 1.2130 |
| 16 | After 32 training steps, supervised | 0.4165 | 0.3841 | 1.0842 | 1.0009 |
| 16 | Task-only readout, 80 further steps | 0.3759 | 0.4555 | 0.8256 | 0.7350 |
| 16 | Leakage-aware readout, 80 further steps | 0.3154 | 0.3808 | 0.8299 | 0.7668 |
| 32 | Step-zero supervised | 1.2678 | 0.6322 | 2.0009 | 1.5468 |
| 32 | After 32 training steps, supervised | 0.8364 | 0.6383 | 1.3101 | 1.0082 |
| 32 | Task-only readout, 80 further steps | 0.5128 | 0.7328 | 0.7003 | 0.4764 |
| 32 | Leakage-aware readout, 80 further steps | 0.3176 | 0.4390 | 0.7526 | 0.6737 |

**Table 5.** New post-review diagnostic means over six seeds. The normalized fraction is the *mean per-state ratio* $\rho=\ell/W$, and the write and within gains are mean per-state Frobenius norms. The zero-step model is randomly initialized, while its readout is fitted on train labels.

Depth-32 absolute leakage is already 1.2678 at random initialization; training reduces it, while the normalized dark fraction changes from 0.6322 to 0.6383. The task-only observer lowers absolute leakage partly by selecting directions with lower total gain and has a *higher* normalized dark fraction (0.7328). The leakage-aware observer reduces both absolute coupling and normalized coupling (0.4390); its within-subspace gain (0.6737) also exceeds task-only's 0.4764. These results help separate a lower observed write scale from an improvement in the observed/dark partition.

The zero-step exercise remains a post-hoc reconstruction. The task is still synthetic and its readout is optimized even for untrained weights. It shows that the original depth effect cannot be attributed entirely to model training.

## 7.2 Reconstructed penalty frontier and task-free minima

For each of the six depth-32 checkpoints, we reran 80 QR-retracted Adam updates from the common supervised initialization at each frozen $\gamma\in\{0,0.05,0.2,1\}$. We used the original fold-9 shadow states for optimization and existing folds 12/13 for evaluation. The originally chosen candidate's objective was checked against its NRF-11 receipt. We also fitted two **task-free local minima** of mean calibration leakage squared, one starting from the supervised basis and one from a task-independent random basis, with the same optimizer-update budget. These are local search outcomes, not a certificate of a global minimum over the Grassmannian.

| Observer / penalty | Held-out MSE | Leakage | Normalized fraction | Combined $\mathcal J$ |
|:--|--:|--:|--:|--:|
| Task-only, $\gamma=0$ | 0.1571 | 0.5128 | 0.7328 | 0.4202 |
| $\gamma=0.05$ | 0.1672 | 0.4348 | 0.6608 | 0.3564 |
| $\gamma=0.2$ | 0.2208 | 0.3577 | 0.5206 | **0.3488** |
| $\gamma=1$ | 0.3121 | 0.2334 | 0.2660 | 0.3666 |
| Task-free leakage-only, supervised start | 0.3711 | 0.1099 | 0.1119 | 0.3832 |
| Task-free leakage-only, random start | 0.3959 | 0.1135 | 0.1278 | 0.4088 |

**Table 6.** Post-hoc full four-point penalty sweep over depth-32 models, with two task-free starts. The table reports means of six per-seed scores on previously exposed evaluation folds, rather than fresh confirmation. The task-free supervised-start observer has mean observed write gain $0.9817$ and within gain $0.9755$; the very low coupling is not solely an almost-zero write-gain solution.

Increasing the penalty traces a task-versus-coupling frontier in these models. At $\gamma=1$, the task MSE exceeds that of the unoptimized baseline even as leakage drops. Thus the combined-score improvement depends on the penalty convention. A stronger confirmatory design should set its MSE ceiling relative to a fully optimized **task-only readout**, report the complete scale-normalized frontier, and repeat the experiment with independently trained model families.

## 7.3 Inference and reproducibility scope

The diagnostic source and per-seed CSVs are supplied separately from the original NRF studies. These computations reuse NRF-11 input folds and the training cohort; their estimates are correlated with the published results. The historical NRF-01/02 numerical-range preprints are unrelated to the derivation of the optimized-observer objective. The fixed-point problem in arbitrary reflexive Banach spaces remains attributed to its cited research preprint rather than treated here as a settled theorem.

# 8. Interpretation, related work, and limits

The experimental and mathematical results operate at different quantifiers and distinct computational depths. Proposition 1 asserts that every proper nonzero **global exact linear** quotient fails under the specified full-support hypotheses. NRF-10 and NRF-11 measure finite-sample, **distribution-conditioned local coupling** over $R/2$ recurrent visits after optimizing the readout itself. A one-step obstruction does not preclude an iterate-level quotient. A low average shadow-state leakage can coexist with a positive global floor. The former concerns a task-useful observer on sampled states; the latter concerns all real states and all proper linear projections.

The Jordan and suffix identities explain why finite recurrent depth can amplify or cancel dark-to-visible influence depending on the ordered tangent products and observation geometry. They motivate the penalty used in NRF-10. They do not prove that the learned decoder has recovered a stable semantic mechanism, nor that the same penalty will generalize across architectures. Training with task-only refinement already produces a strong improvement, making its equal-budget control essential when interpreting the additional value from leakage regularization.

Nonlinear observability via variational dynamics, Lyapunov exponents, and empirical Gramians [3] is a natural comparison for the present finite-sample Jacobian metric. Dynamics-aware oblique reduction [4] points to extensions beyond the orthogonal rank-eight subspaces considered here. The numerical-range and fixed-point papers that launched NRF [1,2] appear as historical motivation. Earlier scalar Crouzeix proofs [13,14], the looped-model readout blind spot [15], and classical lumpability [16,17] supply crucial related context. The later exact quotient theorem and numerical observer optimization have independent derivations.

The following limitations materially bound the claims:

- All measured models are 128-dimensional tied residual MLP loopers trained for only 16 or 32 optimizer steps on 128 or 256 stochastic input examples from one Gaussian signed-permutation family. They are not attention transformers or language models. There is no Lean proof-search or downstream reasoning evaluation here.
- The observation is low rank, and its decoding quality is task-specific. A reduction in local Jacobian leakage is **not evidence of improved model safety**, consciousness, or causal interpretability without additional interventions and checks.
- The original absolute leakage metric depends on observation rank and observed write gain. Its scale-normalized ratio and the within/total gains in Section 7 are retrospective controls; a global projector minimum is not certified. The reported combined score depends on the chosen task label, shadow distribution, and $\lambda$. The shared $\lambda=1$ was chosen after earlier outcomes. Registration of later folds and seeds limits new opportunities for tuning, but does not restore a completely independent confirmatory design.
- The original comparison budget of 1.10 times the *unoptimized baseline* permits larger task regression than a task-only-normalized budget. Sample sizes of three or six independent model seeds per depth are small. Reused cohorts and multiple follow-up studies are correlated. We emphasize descriptive effects and gate counts rather than treating nominal binomial probabilities as confirmatory significance.
- NRF-08's original binary checkpoint identity gate failed. Its suffix experiment is **NRF-08X exploratory**, and must not be pooled into a strict preregistered success count.
- The exact global nonlinear quotient proof relies on invertibility, independent full-domain tanh gates, and full nonzero support of $W_1W_2$. Its finite-field certificates establish those hypotheses for twelve particular stored checkpoints. The theorem is written and tested with rational examples; only smaller algebraic pieces have Lean proofs.
- MathCan's Lean status is module-specific. Its NRF exact-arithmetic and fragment checks do not certify the entire real matrix analysis. Private LoopedTransformers GitHub Actions had repeated runner/log failures; locally validated receipts and independent exact arithmetic checks have separate evidential status.

The next experiment should register a distinct task family or architecture before any data are generated. A stronger task ceiling should be anchored to the fully optimized task-only observer, and the candidate set should include a task-free leakage local optimum, scale-normalized gain diagnostics, and a full penalty frontier. Compare orthogonal and oblique projections only after this measurement protocol is fixed. A meaningful capability-and-safety claim would require measurements on tasks and behavior well beyond this toy data distribution.

# 9. Conclusion

The NRF campaign reveals a useful division of labor. Exact global observability can be obstructed even when a small task-oriented readout is effective. Across a staged series of experiments, deeper tied recurrence increased the cost of hidden-to-observed coupling in ordinary supervised projections, with part of the apparent contrast explained by unequal optimizer-update budgets. Training a rank-eight observer against a local Jacobian-leakage surrogate improved the chosen held-out joint objective over an equal-update task-only readout, at a substantial cost in task MSE. Post-review gain-normalized analysis shows that the explicit penalty reduces relative dark-to-observed coupling beyond the write-scale reduction already induced by task-only optimization. The selected observers retained the same within-family ranking on newly generated input samples. This provides a tractable target for compact-model mechanistic interpretation while leaving cross-task, cross-architecture, and real-language-model validation open.

# Reproducibility appendix

Every empirical result is backed by merged experiment receipts and a separately identified source protocol. The mathematical statements and the experiment campaigns are linked in the numbered references. The source collection includes:

- **NRF-01–05:** finite-dimensional numerical-range certificates, exact observation closure, and finite-field full-support witnesses.
- **NRF-06–08X:** input and model-seed transfer receipts, plus the blocked original byte-identity gate for the exploratory suffix intervention.
- **NRF-09:** six paired seeds with matched optimizer-update budgets and complete random-control score comparisons.
- **NRF-10–11:** calibration choices, frozen observer parameters, twelve saved adapter hashes, and independent fresh-input measurements.
- **Post-review controls:** zero-step model reconstructions, gain-normalized leakage diagnostics, the full four-penalty sweep, and two task-free local optimizations. These are retrospective and reproducible from the accompanying CSV and Python scripts.

The applied receipts are available in the [LoopedTransformers experiment collection](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/numerical_range_fixed_point_v1). Written proofs and exact-rational oracles are available in [MathCan](https://github.com/patrickdugan/MathCan/tree/main/research/compactification). Source campaign PRs are [LoopedTransformers #56](https://github.com/MoralityLabAI/LoopedTransformers/pull/56), [#88](https://github.com/MoralityLabAI/LoopedTransformers/pull/88), [#95](https://github.com/MoralityLabAI/LoopedTransformers/pull/95), [#98](https://github.com/MoralityLabAI/LoopedTransformers/pull/98) and [MathCan #46](https://github.com/patrickdugan/MathCan/pull/46), [#75](https://github.com/patrickdugan/MathCan/pull/75), [#81](https://github.com/patrickdugan/MathCan/pull/81). Experimental checkpoint binaries and full eleven-arm receipts for certain campaigns were distributed as conversation reproduction archives, rather than committed binary assets; the public receipts alone are not a full model-weight archive.

# References

[1] OpenAI (2026). *A direct proof of the complete Crouzeix inequality*. OpenAI Math release #325, 26 September 2026. [Preprint](https://github.com/openai/math/tree/main/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026).

[2] OpenAI (2026). *Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces*. OpenAI Math release #328, 24 September 2026. [Preprint](https://github.com/openai/math/tree/main/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026).

[3] Kazma, M. H., and Taha, A. F. (2026). *Observability for Nonlinear Systems: Connecting Variational Dynamics, Lyapunov Exponents, and Empirical Gramians*. IEEE Transactions on Control of Network Systems, early access. [doi:10.1109/TCNS.2026.3721959](https://doi.org/10.1109/TCNS.2026.3721959).

[4] Padovan, A. (2026). *Non-Intrusive Balancing for Data-Driven Model Reduction with Oblique Projections*. [arXiv:2610.15219](https://arxiv.org/abs/2610.15219).

[5] Morality Lab (2026). *NRF-01–08X: Numerical Range Fixed-Point experiment collection*, LoopedTransformers, merged [PR #56](https://github.com/MoralityLabAI/LoopedTransformers/pull/56).

[6] Morality Lab (2026). *Crouzeix fixed-point switching and graph certificates*, MathCan, merged [PR #46](https://github.com/patrickdugan/MathCan/pull/46).

[7] Morality Lab (2026). *Full Linear Gate Collapse, Jordan Depth Leakage Scaling, and Suffix Dark Transport*, MathCan, in [PR #46](https://github.com/patrickdugan/MathCan/pull/46), especially [`FULL_LINEAR_GATE_COLLAPSE.md`](https://github.com/patrickdugan/MathCan/blob/main/research/compactification/FULL_LINEAR_GATE_COLLAPSE.md).

[8] Morality Lab (2026). *Projector Leakage Geometry*, MathCan, merged [PR #81](https://github.com/patrickdugan/MathCan/pull/81).

[9] Morality Lab (2026). *NRF-09: Matched Optimizer Steps*, LoopedTransformers, merged [PR #88](https://github.com/MoralityLabAI/LoopedTransformers/pull/88).

[10] Morality Lab (2026). *Matched-Step Margin Stability*, MathCan, merged [PR #75](https://github.com/patrickdugan/MathCan/pull/75).

[11] Morality Lab (2026). *NRF-10: Leakage-Aware Frozen-Weight Observers*, LoopedTransformers, merged [PR #95](https://github.com/MoralityLabAI/LoopedTransformers/pull/95).

[12] Morality Lab (2026). *NRF-11: Frozen-Observer Fresh-Fold Transfer*, LoopedTransformers, merged [PR #98](https://github.com/MoralityLabAI/LoopedTransformers/pull/98).

[13] Jin, S. (2026). *The Numerical Range Is a 2-Spectral Set*. First posted 27 July 2026. [Preprint](https://www.preprints.org/manuscript/202607.1919).

[14] Lorist, E., and Schwenninger, F. (2026). *A solution to Crouzeix's conjecture*. [arXiv:2608.03841](https://arxiv.org/abs/2608.03841).

[15] Sharma, R., and Vu, T. (2026). *Dense Supervision Is Not Enough: The Readout Blind Spot in Looped Language Models*. [arXiv:2606.24898](https://arxiv.org/abs/2606.24898).

[16] Horstmeyer, L., and Atay, F. M. (2015). *Characterization of Exact Lumpability of Smooth Dynamics on Manifolds*. [Max Planck Institute preprint](https://www.mis.mpg.de/publications/preprint-repository/article/2015/issue-70).

[17] Atay, F. M., and Ŗoncoroni, L. (2017). *Lumpability of linear evolution equations in Banach spaces*. Evolution Equations and Control Theory. [DOI:10.3934/eect.2017002](https://www.aimsciences.org/article/doi/10.3934/eect.2017002).