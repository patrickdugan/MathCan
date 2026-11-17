---
title: "Task-Conditioned Observable Fibers in Short-Trained Tied Residual Networks"
subtitle: "Readout regularization, dark-state Jacobian coupling, and exact quotient limits (NRF-01–11 with post-review diagnostics)"
author: "Morality Lab — research working draft"
date: "16 November 2026 · Revised working draft v0.5"
lang: en
abstract: |
  We study rank-eight observable readouts of 128-dimensional tied residual MLP loopers trained for only 16 or 32 AdamW steps on one synthetic signed-permutation task. The main frozen-weight comparison gives task-only and leakage-aware readouts 80 equal-budget updates. At depth 32, task-only task MSE and dark-to-observed Jacobian coupling are 0.1493 and 0.5122; leakage-aware readout MSE rises to 0.2476 as coupling falls to 0.3184. The 14.4% reduction in the previously selected joint objective requires an evaluation penalty greater than the empirical 0.6242 crossing. A retrospective directional audit on D=T-I changes the mechanism interpretation. Relative to the mean of eight random rank-eight controls, the supervised readout has 1.17 times incoming dark-to-observed coupling, 0.83 times outgoing observed-to-dark coupling, and 0.55 times within-subspace change. Task-only refinement shifts those ratios to 0.71, 1.08, and 1.79; leakage-aware selection yields 0.44, 1.07, and 1.30. The reverse channel remains approximately at the random reference level. Most of the additional absolute leakage reduction accompanies a reduction in total observed computed-change gain, and the incoming fraction improves beyond task-only in five of six selected depth-32 models. Two high-penalty selections lose within-subspace change and incur especially large task-MSE costs. The fixed-penalty pooled lower envelope switches at evaluation weights 0.1365, 0.8758, 1.2427, and 1.3917. All new directional controls are retrospective on a single synthetic model/task family. The separate full-domain one-step exact quotient obstruction and positive global leakage floor do not establish an iterate-level no-go; only narrower algebraic fragments are Lean-checked.
keywords:
  - mechanistic interpretability
  - recurrent networks
  - observability
  - low-rank projections
  - nonnormal dynamics
  - Jacobian leakage
  - model reduction
---

**Working manuscript, v0.5 after four substantive technical reviews.** Empirical source: MoralityLabAI/LoopedTransformers; mathematical source: patrickdugan/MathCan. The experiment archive contains the merged NRF-01–11 campaign as of 15 November 2026. Post-review measurements are explicitly exploratory, were calculated after inspecting earlier outcomes, and have separate local CSV and source-code receipts. Formalization claims apply to the listed Lean lemmas rather than the complete real-analytic theorems. This draft is intended for technical review.

# 1. Introduction

A recurrent computation can encode a useful task answer in a small set of directions while continuing to exchange information with much larger hidden coordinates. A decoder that predicts the correct target can therefore conceal a dynamic dependence on unobserved state. This matters for compact-model design and mechanistic interpretation, because the same low-rank representation may perform well on a task and respond strongly to perturbations outside the representation.

The model's readout can ignore directions that remain active in its recurrent transition. Sharma and Vu describe a related blind spot for hidden-state scale under normalized outputs in looped language models [15]. Our question concerns task-prediction quality and the Jacobian mapping of discarded coordinates into the rank-eight observed subspace. Because these residual loopers include an identity skip path, we measure both the full tangent and the *computed change* after subtracting the identity. Classical dynamical lumpability and invariant-subspace theory provide antecedents [16,17].

We primarily report an *observer-training* intervention. Across six frozen depth-32 models, 80 optimizer updates without a leakage penalty already improve the task and reduce absolute leakage substantially. Adding an explicit leakage term reduces leakage further and improves a chosen combined score, while sacrificing task accuracy relative to that equal-budget control. The numerical-range and fixed-point constructions that began this project are retained as historical context. The later full-domain obstruction and low-rank observer experiments do not rely on either of the two OpenAI preprints as proof inputs.

The mathematical contribution is a precisely scoped full-domain **one-step** linear-quotient obstruction with a positive global differential leakage floor, alongside tractable tangent-transport and projector identities. The experiment compares equal-budget observers and quantifies the exchange rate between task accuracy and leakage. Post-review diagnostics measure the two directions of computed-change coupling; the penalty appears to favor directions receiving less state change, and substantial observed-to-hidden influence remains. These are project-specific specializations of established invariance and model-reduction mathematics.

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


For a residual map with $\alpha=1$, let $D_R(h)=T_R(h)-I$ denote the **computed-change tangent**. Its dark-to-observed block is exactly the original leakage block, since $U^\top I(I-UU^\top)=0$:

$$
\ell_{\Delta}(U;h)=\frac{\|U^\top D_R(h)Q\|_F}{\sqrt8}=\ell_R(U;h).
$$

The normalizing gain and within-subspace gain change:

$$
W_{\Delta}=\frac{\|U^\top (T_R-I)\|_F}{\sqrt8},\qquad
G_{\Delta}=\frac{\|U^\top (T_R-I)U\|_F}{\sqrt8},\qquad
\rho_{\Delta}=\frac{\ell_R}{W_{\Delta}}.
$$

The corresponding per-state Pythagorean identity is $W_{\Delta}^2=G_{\Delta}^2+\ell_R^2$. This ratio estimates the fraction of the observer's **computed change** entering from discarded coordinates. If $W_{\Delta}$ is near zero, it must be read alongside the absolute gain. The post-review computations report means of per-state ratios and gains, with random observers and two task-free local baselines.

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

# 4. Pre-optimization context: NRF-04–09

NRF-04 found lower held-out task error but higher dark-to-observed Jacobian leakage in its supervised rank-eight subspaces than in random controls. NRF-07 reproduced the earlier depth-dependent *joint-objective* reversal with new models, though equal 4,096 state visits meant 32 optimizer steps for depth 16 and 16 for depth 32. NRF-08X's frozen-midpoint suffix replay produced a directionally consistent mechanism diagnostic but **failed its strict checkpoint byte-identity gate**, so its outcome is exploratory [5]. NRF-09 then trained six new matched-seed model pairs for equal optimizer steps. At 32 steps, task-supervised observation beat the complete random-arm median in 6/6 depth-16 models and 1/6 depth-32 models. The observed margin contrast obeyed $0.395476=0.215683+0.179793$: the second term measures 45.46% of the equal-visit contrast along one depth-32 update path [9,10]. Post-review step-zero analysis shows large leakage before any model training. At 32 updates the **computed-change dark fraction** of unoptimized supervised observers was 0.9736 at depth 16 and 0.9785 at depth 32, and corresponding random controls were 0.9283 and 0.9126. Absolute observed change gain increased from 0.4278 to 0.8548 for the supervised readout. The main depth trend in this small cohort is **magnitude**, with its fractional composition already strongly represented at initialization; training changes absolute gain and the observed direction geometry.

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

**Table 1.** Frozen-weight NRF-10 readout results. Each cell aggregates six model seeds. The group mean of $\mathcal J$ is not obtained by squaring the group mean leakage [11].

The **equal-budget task-only arm is the principal comparator**. At depth 32, its task MSE of $0.1493$, leakage $0.5122$, and joint score $0.4117$ become MSE $0.2476$, leakage $0.3184$, and score $0.3526$ after leakage-aware optimization. The explicit penalty reduces leakage by **37.8% relative to task-only**, while task MSE increases by **65.8%**. The combined score improves by **14.4% at the previously chosen $\lambda=1$**. Define the mean-over-seeds objective $\overline{\mathcal J}_\lambda=\overline{E}+\lambda\overline{L^2}$, where the bar applies to complete *per-seed* scores. The chosen observer wins over task-only only when

$$
\lambda>\lambda^*_{\mathrm{NRF10}}=\frac{\overline{E}_{\mathrm{joint}}-\overline{E}_{\mathrm{task}}}{\overline{L_{\mathrm{task}}^2}-\overline{L_{\mathrm{joint}}^2}}=\boxed{0.6242}.
$$

This exact aggregation differs slightly from the approximately $0.61$ obtained by squaring the **group-mean** leakage. On NRF-11's reused model cohort with fresh input draws, the corresponding depth-32 break-even is 0.5667. The **depth-16 pairwise break-evens** are 0.6776 for NRF-10 and 0.6148 for NRF-11. All four values use group means of *per-seed squared leakage*, not squared group-mean leakage; these are comparisons against task-only and not the full candidate lower envelope. The combined-score advantage over task-only occurs in all six depth-32 NRF-10 seed-level comparisons and all six depth-16 comparisons at $\lambda=1$. These empirical thresholds depend on the unit convention of task MSE and leakage, and $\lambda$ was chosen after inspecting NRF-04.

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

**Table 2.** Fresh-fold NRF-11 scores, with no readout refit after the original NRF-10 selection. A dash indicates an omitted table statistic, not a zero measurement [12].

The depth-32 compound gate again passes 5/6, with seed 149 missing the task-error budget (ratio $1.1139$). The depth-16 cohort passes 6/6. For all twelve frozen observers, the joint score beats the original supervised readout, the equal-budget task-only control, and the median of eight random controls. Mean depth-32 joint $\mathcal J$ changes from $0.3526$ (NRF-10) to $0.3515$ (NRF-11), consistent with stable sampling from the same synthetic Gaussian distribution. The change is descriptive rather than evidence of generalization to another task family.

A repository-native replay bug discovered during publication review is also documented: NRF-10 initially imported the NRF-09 generator that intentionally rejected folds outside 1/7/8. The NRF-11 integration repaired the fold contract for 9–13 using the identical registered Gaussian stream and teacher, with parity tests and an independent saved-adapter replay. The fix changes admitted fold indices and leaves the generated data formula and selection settings intact [12].

# 7. Post-review exploratory controls: computed change, random observers, and the penalty frontier

These measurements were designed after inspecting NRF-10/11 outcomes. They reuse the **same six trained model seeds** and the already exposed NRF-11 fold-13 shadow inputs. A second audit recomputed the 128×128 Jacobians from the archived, SHA-verified NRF-09 checkpoints and checked the frozen NRF-11 observer-adapter hashes. Each dark-block leakage agrees with its saved receipt, and the equality $U^\top(T-I)Q=U^\top TQ$ holds within $1.2\times 10^{-16}$ in the reconstructed experiment. They are retrospective **mechanism diagnostics**.

## 7.1 Subtracting the identity skip path

Table 3 includes a random-observer reference, the step-zero initialization control, and the task-free local optimum. For a fixed recurrent depth of 32, the trained models are evaluated after 32 AdamW updates; each step-zero model has the same initialization seed but zero updates, with its supervised readout still fitted from labeled examples. All entries are six-seed mean values. The random reference averages eight independent rank-eight bases within each seed (48 arm measurements); those arms do not constitute 48 independent trained models.

| Depth-32 observer | Dark leakage $L$ | Full-tangent $\bar\rho$ | Change-only $\bar\rho_\Delta$ | Change write $\bar W_\Delta$ | Change within $\bar G_\Delta$ |
|:--|--:|--:|--:|--:|--:|
| Supervised at step zero | 1.2678 | 0.6322 | 0.8978 | 1.4128 | 0.6225 |
| Supervised after 32 updates | 0.8364 | 0.6383 | 0.9785 | 0.8548 | 0.1759 |
| Eight matched random controls, mean | 0.7178 | 0.6861 | 0.9126 | 0.7866 | 0.3211 |
| Task-only, 80 readout updates | 0.5128 | 0.7328 | 0.6665 | 0.7697 | 0.5737 |
| Leakage-aware, 80 readout updates | 0.3176 | 0.4390 | 0.6201 | 0.5250 | 0.4163 |
| Task-free leakage-only, supervised start | 0.1099 | 0.1119 | 0.6756 | 0.1635 | 0.1204 |
| Task-free leakage-only, random start | 0.1135 | 0.1278 | 0.4964 | 0.2322 | 0.2018 |

**Table 3.** Post-review means of per-state ratios and normalized Frobenius gains, reusing NRF-11 fold 13. The shadow-state identity $W_\Delta^2=G_\Delta^2+\ell^2$ holds *before* averaging. Absolute dark leakage remains unchanged after subtracting the identity; the reported $\rho$ and $\rho_\Delta$ are averages of per-state ratios, not ratios of column means.

The raw ratio moves only from 0.6322 at initialization to 0.6383 after short model training, even while absolute leakage falls from 1.2678 to 0.8364. On the computed-change scale the corresponding ratios are 0.8978 and 0.9785. Hence the **large initialized coupling remains** and the short training mostly reduces its absolute size for this protocol; training also changes its directional composition. The empirical depth comparison cannot be presented as a leakage pattern learned only during training.

Task-only observer optimization lowers absolute leakage and the change-only dark fraction relative to the unoptimized supervised observer. The leakage-aware arm reduces its change-only fraction further, 0.6665 to 0.6201, although the improvement is smaller than suggested by the full-tangent ratios, 0.7328 to 0.4390. The random-observer baseline of 0.9126 helps interpret the scale of these numbers. The task-free supervised-start observer has full-tangent within gain 0.9755 but **change-only within gain 0.1204**; its full-tangent dark ratio 0.1119 is therefore strongly affected by the identity skip path. Its change-only dark fraction is 0.6756, with low absolute change write gain 0.1635. Choosing the smallest full-tangent coupling can select a nearly inert observed subspace.

For the depth-16 control cohort, the corresponding change-only dark fractions are 0.9142 at step zero, 0.9736 for the supervised observer after training, 0.9283 for random observations, 0.7865 for task-only, and 0.7565 for leakage-aware. These secondary values were computed in the same retrospective audit.

## 7.2 Both directions of the computed-change channel

With $D=T-I$, write $B=PDQ$ for dark-to-observed influence, $C=QDP$ for observed-to-dark influence, and $A=PDP$ for within-observation change. The transpose-facing channel is measured by $\|QDU\|_F/\sqrt 8$. This is the *complementary Jacobian block*, not the transpose of $B$ in a generally nonnormal recurrence. Two exact Pythagorean identities hold per shadow state:

$$
\frac{\|U^\top D\|_F^2}{8}=\frac{\|U^\top DU\|_F^2+\|U^\top DQ\|_F^2}{8},\qquad
\frac{\|DU\|_F^2}{8}=\frac{\|U^\top DU\|_F^2+\|QDU\|_F^2}{8}.
$$

| Depth | Observer | Incoming $\|PDQ\|_F/\sqrt8$ | Outgoing $\|QDP\|_F/\sqrt8$ | Within $\|PDP\|_F/\sqrt8$ |
|:--|:--|--:|--:|--:|
| 16 | Eight random controls, mean | 0.4094 | 0.4073 | 0.1636 |
| 16 | Supervised | 0.4165 | 0.3570 | 0.0972 |
| 16 | Task-only | 0.3759 | 0.4456 | 0.2952 |
| 16 | Leakage-aware | 0.3154 | 0.4428 | 0.2726 |
| 32 | Eight random controls, mean | 0.7178 | 0.7157 | 0.3211 |
| 32 | Supervised | 0.8364 | 0.5964 | 0.1759 |
| 32 | Task-only | 0.5128 | 0.7762 | 0.5737 |
| 32 | Leakage-aware | 0.3176 | 0.7649 | 0.4163 |

**Table 3B.** Retrospective six-seed means, twelve frozen NRF-11 shadow states per seed, source checkpoints and adapters verified by SHA-256. The random reference averages eight rank-eight arms **within each seed** and then averages the six seed references; it is not a 48-model cohort. The full auditable dataset has **1,584 per-state arm rows**. Both computed-change Pythagorean identities passed per-state checks. Averages of norms do not themselves obey the squared-norm identities.

At depth 32, task-only to leakage-aware optimization reduces incoming coupling from 0.5128 to 0.3176, while outgoing coupling changes from 0.7762 to 0.7649 (a 1.5% decline). The **random outgoing reference is 0.7157**: task-only is 1.08 times random, and joint is 1.07 times random. Outgoing coupling exceeds incoming coupling in every seed for both optimized arms, but its absolute magnitude is approximately that of randomly chosen observation directions. The informative asymmetry is **incoming suppression below the random reference**, rather than exceptional outgoing excitation. Dynamic influence cannot be identified with functionally useful signal without trajectory interventions.

**Table 3C.** Ratios of six-seed means to the corresponding eight-random-arm mean (each arm and each seed has twelve shadow states). These are ratios of aggregated norm means, rather than means of per-state or per-seed ratios.

| Depth | Observer | Incoming/random | Outgoing/random | Within/random |
|:--|:--|--:|--:|--:|
| 16 | Supervised | 1.02 | 0.88 | 0.59 |
| 16 | Task-only | 0.92 | 1.09 | 1.80 |
| 16 | Leakage-aware | 0.77 | 1.09 | 1.67 |
| 32 | Supervised | **1.17** | **0.83** | **0.55** |
| 32 | Task-only | **0.71** | **1.08** | **1.79** |
| 32 | Leakage-aware | **0.44** | **1.07** | **1.30** |

At depth 32, the supervised readout has incoming above every one of its eight random controls and outgoing and within-observed change below all eight controls in **6/6 seeds**. The task-only optimized observer crosses to incoming below all eight and outgoing and within above all eight in **6/6 seeds**. The leakage-aware *selected* observer remains below all eight random incoming controls in 6/6, while its outgoing and within blocks exceed all eight in only **4/6**. In the other two seeds its within-observed change falls **below** all eight random arms. This suggests a shift from a comparatively receiving observed subspace to a more self-driven one under task-only refinement, followed by penalty-dependent suppression of computed change. The terms 'receiving' and 'self-driven' describe Jacobian blocks relative to these sampled random directions and are not causal descriptions of a biological or computational register.

The penalty's mean absolute leakage advantage arises primarily through lower observed change gain. Using **group means** from Table 3, the log ratio $\log(0.5250/0.7697)/\log(0.3176/0.5128)$ is approximately **0.80**; the analogous depth-16 ratio is **0.78**. These are descriptive ratios of aggregated means, because $\overline{\ell}=\overline{W_\Delta\rho_\Delta}$ and group averaging does not commute with products or logarithms. From supervised to the selected joint observer, task-only refinement explains approximately **87%** of the depth-32 reduction in mean $\rho_\Delta$ (86% at depth 16). The explicit leakage term contributes the remaining roughly 13% on that additive accounting path.

The selected NRF-11 joint observers use $\gamma=0.2$ in four depth-32 seeds and $\gamma=1$ in seeds 131 and 149. Four $\gamma=0.2$ observers have mean $\rho_\Delta=0.581$; the two $\gamma=1$ observers average 0.698. Seed 131 moves from $\rho_\Delta=0.680$ under task-only to 0.751 with its selected $\gamma=1$ joint observer, so the reduction in this fraction occurs in **5/6 models**, even though the absolute leakage decreases in 6/6.

**High-penalty selection failure mode.** Seed 131's within-observed computed change is **0.649 times its eight-random mean** and seed 149's is **0.886 times** random. Both fall below all eight random arms; the remaining four joint observers have above-random within change. The two high-penalty choices retain lower incoming magnitude (0.320 and 0.332 times random) while their task MSE rises to **1.851** and **1.791** times the equal-budget task-only MSE in the public NRF-11 risk file. Seed 131 is the fractional-partition exception; seed 149 also fails the separate **1.10× unoptimized-supervised-baseline** task gate. The penalty can therefore buy lower leakage by shrinking total observed computed-change gain, leaving proportionally more incoming dark influence in an individual selected readout.

## 7.3 Penalty frontier as an exchange rate

All $\gamma$ candidates below receive **80** QR-retracted Adam readout updates from a common supervised initialization on depth-32 weights. We calculate their score from NRF-11's already exposed task fold 12 and shadow fold 13, with no fresh model cohort. The penalty $\gamma$ controls the training objective, while $\lambda$ represents the *evaluation exchange rate* between task error and squared mean leakage. To compare arms, define

$$
\lambda^*(\gamma)=\frac{\overline E_\gamma-\overline E_{0}}{\overline{L_0^2}-\overline{L_\gamma^2}},\qquad
\overline{\mathcal J}_\lambda(\gamma)=\overline E_\gamma+\lambda\overline{L_\gamma^2}.
$$

The bar means six-model averaging. We report finite positive thresholds only when the candidate has larger task MSE and lower squared leakage than the task-only candidate. An evaluation weight above the threshold favors the candidate in this pairwise comparison, and weights below it favor task-only.

| Depth-32 observation | Task MSE | Leakage | Change-only $\bar\rho_\Delta$ | Mean $\mathcal J_{1}$ | Break-even $\lambda^*$ vs task-only |
|:--|--:|--:|--:|--:|--:|
| Task-only, $\gamma=0$ | 0.1571 | 0.5128 | 0.6665 | 0.4202 | reference |
| $\gamma=0.05$ | 0.1672 | 0.4348 | 0.6111 | 0.3564 | **0.136** |
| $\gamma=0.2$ | 0.2208 | 0.3577 | 0.5851 | **0.3488** | 0.471 |
| $\gamma=1$ | 0.3121 | 0.2334 | 0.6722 | 0.3666 | 0.743 |
| Task-free leakage-only, supervised start | 0.3711 | 0.1099 | 0.6756 | 0.3832 | 0.853 |
| Task-free leakage-only, random start | 0.3959 | 0.1135 | 0.4964 | 0.4088 | 0.954 |

**Table 4.** Post-hoc penalty sweep, six depth-32 models, independent archived input folds within the same task family. The task-free candidates are **locally optimized minima** from two starting points, not global solutions. Thresholds use averages of *per-seed leakage squares*, so numerical results need not match a calculation from the square of column-mean leakage.

The pairwise thresholds in Table 4 concern **only** a candidate versus $\gamma=0$, and several candidates lose to a different penalized arm. The empirical **lower envelope**, computed over all six measured candidates as $\min_\gamma[\overline{E}_\gamma+\lambda\overline{L^2}_\gamma]$, switches as follows:

| Evaluation $\lambda$ interval | Lowest pooled score among measured candidates |
|:--|:--|
| $0 \le \lambda < 0.1365$ | Task-only, $\gamma=0$ |
| $0.1365 < \lambda < 0.8758$ | $\gamma=0.05$ |
| $0.8758 < \lambda < 1.2427$ | $\gamma=0.2$ |
| $1.2427 < \lambda < 1.3917$ | $\gamma=1$ |
| $\lambda > 1.3917$ | Task-free, supervised-start local optimum |

**Table 4B.** Retrospective *global choice among the six measured candidate arms*; adjacent rows tie at each boundary. The task-free random-start arm is absent from the lower envelope. Pairwise break-even $0.471$ for $\gamma=0.2$ versus task-only does **not** imply that $\gamma=0.2$ is optimal at $\lambda=0.471$: $\gamma=0.05$ remains better until $0.8758$. The marginal threshold to move beyond $\gamma=0.05$ is about **6.4 times** the first threshold. The values are measurement-unit dependent and were calculated after all evaluation data were available.

At each of six seeds, $\rho_\Delta$ falls relative to task-only for fixed $\gamma=0.05$ and $0.2$, then rises when moving from $\gamma=0.2$ to $1$. Over that last step, mean $\rho_\Delta$ increases from 0.5851 to 0.6722 even as mean observed change gain falls from 0.6116 to 0.3487. This exposes the high-penalty scale-shrinkage regime. The selected NRF-10/11 observer uses a seed-dependent $\gamma$ and must be considered a distinct arm from each fixed-$\gamma$ row.

The least expensive point in task accuracy among these tested positive penalties is $\gamma=0.05$: compared with task-only it raises task MSE by about **6.4%** and lowers absolute leakage by **15.2%**, winning whenever the evaluation weight exceeds $0.136$. The selected $\gamma$-mixture from NRF-10 and NRF-11 has different task/leakage values from any fixed-$\gamma$ row and crosses task-only at **depth 32** $\lambda=0.6242$ on NRF-10 and $0.5667$ on NRF-11; the **depth-16** crossings are $0.6776$ and $0.6148$, respectively. All four are pairwise against task-only. For the fixed $\gamma=1$ arm, the raw dark fraction is 0.2660, but its computed-change fraction is 0.6722, slightly **above** the task-only 0.6665. This demonstrates the importance of subtracting the identity when interpreting a very low raw ratio.

An observable-fiber paper should report this frontier and its implied exchange rates. A future preregistration should bound task MSE relative to the fully optimized **task-only** readout and fix $\lambda$ from an independently justified scale or end-user utility. A new model family and a fresh task distribution are needed to test transfer of the measured tradeoff.

## 7.4 Mathematical and empirical scope of the controls

These diagnostics reuse the archived model weights and seed/task family, and the $\gamma$ frontier was reconstructed **after** inspecting NRF-11's evaluation folds. The skip-adjusted block identity is exact; the numerical ratios, initialization effects and break-even penalties are descriptive measurements at finite shadow states. The cross-study NRF-11 result remains a fresh-input stability check within an unchanged synthetic family. The original two OpenAI mathematics preprints are part of the research history rather than assumptions used in any learned-observer theorem.

# 8. Interpretation, related work, and limits

The experimental and mathematical results operate at different quantifiers and distinct computational depths. Proposition 1 asserts that every proper nonzero **global exact linear** quotient fails under the specified full-support hypotheses. NRF-10 and NRF-11 measure finite-sample, **distribution-conditioned local coupling** over $R/2$ recurrent visits after optimizing the readout itself. A one-step obstruction does not preclude an iterate-level quotient. A low average shadow-state leakage can coexist with a positive global floor. The former concerns a task-useful observer on sampled states; the latter concerns all real states and all proper linear projections.

The Jordan and suffix identities explain why finite recurrent depth can amplify or cancel dark-to-visible influence depending on the ordered tangent products and observation geometry. They motivate the penalty used in NRF-10. They do not prove that the learned decoder has recovered a stable semantic mechanism, nor that the same penalty will generalize across architectures. Training with task-only refinement already produces a strong improvement, making its equal-budget control essential when interpreting the additional value from leakage regularization.

Nonlinear observability via variational dynamics, Lyapunov exponents, and empirical Gramians [3] is a natural comparison for the present finite-sample Jacobian metric. Dynamics-aware oblique reduction [4] points to extensions beyond the orthogonal rank-eight subspaces considered here. The numerical-range and fixed-point papers that launched NRF [1,2] appear as historical motivation. Earlier scalar Crouzeix proofs [13,14], the looped-model readout blind spot [15], and classical lumpability [16,17] supply crucial related context. The later exact quotient theorem and numerical observer optimization have independent derivations.

The following limitations materially bound the claims:

- All measured models are 128-dimensional tied residual MLP loopers trained for only 16 or 32 optimizer steps on 128 or 256 stochastic input examples from one Gaussian signed-permutation family. They are not attention transformers or language models. There is no Lean proof-search or downstream reasoning evaluation here.
- The observation is low rank, and its decoding quality is task-specific. A reduction in local Jacobian leakage is **not evidence of improved model safety**, consciousness, or causal interpretability without additional interventions and checks.
- The original absolute leakage metric depends on observation rank and observed write gain; full-tangent ratios can be strongly affected by identity skip pathways. A smaller incoming channel may coincide with outgoing coupling near the random-observer level and a loss of task-relevant computation. The two selected high-penalty seeds sacrifice 85.1% and 79.1% more task error relative to the equal-budget task-only readout on NRF-11 fold 12. The chosen normalized dark fraction improves in only five of six depth-32 models relative to task-only. The change-only ratio, its write/within gain components, and random-observer baseline are retrospective controls. Two task-free local solutions are measured; a global projector minimum is not certified. The reported combined score depends on the chosen task label, shadow distribution, and $\lambda$. The shared $\lambda=1$ was chosen after earlier outcomes. Registration of later folds and seeds limits new opportunities for tuning, but does not restore a completely independent confirmatory design.
- The original comparison budget of 1.10 times the *unoptimized baseline* permits larger task regression than a task-only-normalized budget. Sample sizes of three or six independent model seeds per depth are small. Reused cohorts and multiple follow-up studies are correlated. We emphasize descriptive effects and gate counts rather than treating nominal binomial probabilities as confirmatory significance.
- NRF-08's original binary checkpoint identity gate failed. Its suffix experiment is **NRF-08X exploratory**, and must not be pooled into a strict preregistered success count.
- The exact global nonlinear quotient proof relies on invertibility, independent full-domain tanh gates, and full nonzero support of $W_1W_2$. Its finite-field certificates establish those hypotheses for twelve particular stored checkpoints. The theorem is written and tested with rational examples; only smaller algebraic pieces have Lean proofs.
- MathCan's Lean status is module-specific. Its NRF exact-arithmetic and fragment checks do not certify the entire real matrix analysis. Private LoopedTransformers GitHub Actions had repeated runner/log failures; locally validated receipts and independent exact arithmetic checks have separate evidential status.

The next experiment should register a distinct task family or architecture before any data are generated, and measure coupling relative to computed change $T-I$. A stronger task ceiling should be anchored to the fully optimized task-only observer, and the candidate set should include a task-free leakage local optimum, scale-normalized gain diagnostics, and a full penalty frontier. Compare orthogonal and oblique projections only after this measurement protocol is fixed. A meaningful capability-and-safety claim would require measurements on tasks and behavior well beyond this toy data distribution.

# 9. Conclusion

The exact one-step global quotient obstruction coexists with useful low-rank task decoding, as a task-conditioned observation need not represent a closed dynamical subsystem. In the six short-trained toy networks, the main depth-associated change in ordinary supervised observers is the **magnitude** of computed-change coupling: the incoming fraction remains near 0.974 at depth 16 and 0.978 at depth 32, while observed change gain approximately doubles. Strong coupling is already present at initialization. Equal-budget leakage-aware readout training lowers the reported incoming-channel norm and improves the chosen joint objective at a substantial cost in task MSE, mainly through reduced observed write gain. The additional directional separation beyond task-only refinement is modest, fails in one selected seed, and leaves reverse observed-to-hidden coupling close to the random rank-eight level, while retaining distinct and seed-dependent within-observed computed change. The task-accuracy/leakage exchange rate has a piecewise lower frontier whose first switch occurs at $\lambda=0.1365$ and whose later switches are increasingly expensive. Relative to random controls, task-only refinement changes a mostly receiving observed subspace into one with greater within-subspace computed change; aggressive leakage penalties sometimes reverse that gain. The same observer rankings persist across fresh samples from the unchanged synthetic family; cross-task, cross-architecture, and real-language-model validation remains open.

# Reproducibility appendix

Every empirical result is backed by merged experiment receipts and a separately identified source protocol. The mathematical statements and the experiment campaigns are linked in the numbered references. The source collection includes:

- **NRF-01–05:** finite-dimensional numerical-range certificates, exact observation closure, and finite-field full-support witnesses.
- **NRF-06–08X:** input and model-seed transfer receipts, plus the blocked original byte-identity gate for the exploratory suffix intervention.
- **NRF-09:** six paired seeds with matched optimizer-update budgets and complete random-control score comparisons.
- **NRF-10–11:** calibration choices, frozen observer parameters, twelve saved adapter hashes, and independent fresh-input measurements.
- **Post-review controls:** step-zero initialization, the full four-penalty and two task-free arms, random controls, both directed computed-change Jacobian channels, and explicit lower-envelope break-evens. Public MathCan draft paths include `papers/NRF_skip_adjusted_metrics_v03.csv`, `papers/NRF_skip_adjusted_frontier_v03.csv`, `papers/NRF_v04_bidirectional_per_state.csv`, `papers/NRF_v04_bidirectional_per_seed.csv`, `papers/NRF_v04_selected_observer_risk.csv`, the `papers/reproduction_v04/` source scripts, and the v0.5 summary files `papers/NRF_v05_random_relative_by_seed.csv` and `papers/NRF_v05_random_relative_summary.json`. These measurements are retrospective. The public per-state CSVs and standard-library arithmetic scripts support direct independent verification of block identities, random-reference ratios, all eight-arm min/max counts, and pairwise per-seed squared-leakage break-evens without checkpoint binaries. Full neural reruns require model/adapter bytes from the separately distributed reproduction archive, or regeneration and SHA-256 parity.

The applied receipts are available in the [LoopedTransformers experiment collection](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/numerical_range_fixed_point_v1). Written proofs and exact-rational oracles are available in [MathCan](https://github.com/patrickdugan/MathCan/tree/main/research/compactification). Source campaign PRs are [LoopedTransformers #56](https://github.com/MoralityLabAI/LoopedTransformers/pull/56), [#88](https://github.com/MoralityLabAI/LoopedTransformers/pull/88), [#95](https://github.com/MoralityLabAI/LoopedTransformers/pull/95), [#98](https://github.com/MoralityLabAI/LoopedTransformers/pull/98) and [MathCan #46](https://github.com/patrickdugan/MathCan/pull/46), [#75](https://github.com/patrickdugan/MathCan/pull/75), [#81](https://github.com/patrickdugan/MathCan/pull/81). Experimental checkpoint binaries and full eleven-arm receipts for certain campaigns were distributed as conversation reproduction archives, rather than committed binary assets; the public receipts alone are not a full model-weight archive.

# References

[1] OpenAI (2026). *A direct proof of the complete Crouzeix inequality*. OpenAI Math collection entry 325, 26 September 2026. [Preprint](https://github.com/openai/math/tree/main/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026).

[2] OpenAI (2026). *Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces*. OpenAI Math collection entry 328, 24 September 2026. [Preprint](https://github.com/openai/math/tree/main/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026).

[3] Kazma, M. H., and Taha, A. F. (2024, revised 2026). *Observability for Nonlinear Systems: Connecting Variational Dynamics, Lyapunov Exponents, and Empirical Gramians*. First submitted 22 February 2024, [arXiv:2402.14711](https://arxiv.org/abs/2402.14711); published online 11 August 2026 in IEEE Transactions on Control of Network Systems (early access), [doi:10.1109/TCNS.2026.3721959](https://doi.org/10.1109/TCNS.2026.3721959).

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

[16] Horstmeyer, L., and Atay, F. M. (2016). *Characterization of exact lumpability for vector fields on smooth manifolds*. Differential Geometry and its Applications 48, 46–60. [doi:10.1016/j.difgeo.2016.06.001](https://doi.org/10.1016/j.difgeo.2016.06.001); [arXiv:1607.01237](https://arxiv.org/abs/1607.01237).

[17] Atay, F. M., and Roncoroni, L. (2017). *Lumpability of linear evolution equations in Banach spaces*. Evolution Equations and Control Theory 6(1), 15–34. [doi:10.3934/eect.2017002](https://www.aimsciences.org/article/doi/10.3934/eect.2017002).
