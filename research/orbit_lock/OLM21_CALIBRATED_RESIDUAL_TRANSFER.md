# OLM-21: Calibration-only SAE erasure residual transfer and a sharp risk-shift obstruction

November 16, 2026. Written finite-dimensional mathematics for the [prospectively frozen SMC-21 calibration experiment](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc21-calibrated-residual-20261116/research/real_recurrence_sae_v1/SMC21_PROTOCOL.md). Extends OLM-20F's exact finite-residual identity. The classical regression, absolute-risk and linear-algebra arguments below are given with original explicit rational witnesses. These are written proofs and Fraction tests, **not Lean kernel declarations or priority claims**.

## Setup

At one frozen recurrent Sudoku goal state \(h\), for a physical decoder erasure edit \(v\) and the answer-conditioned correct-digit task margin \(m\), define its finite erasure \(E(v)=m(h)-m(h-v)\), clean physical task gradient \(g=\nabla m(h)\), and exact finite residual \(R(v)=E(v)-g^\top v\). The direct clean-gradient prediction of a new SAE refit's target erasure \(E(b)\) is \(g^\top b\), with target residual \(y=R(b)\).

The original/source SAE feature gives a residual covariate \(x=R(a)\), while a different naturally active target SAE decoder direction yields a matched-budget control \(z=R(o)\). Both are computed from the **same teacher**, and in the SMC-21 calibration stage the old 64-puzzle calibration targets \(y\) are available. The new heldout target \(E(b)\) is unavailable when the two one-parameter coefficients are frozen.

SMC-21 fits a fixed-shrinkage, no-intercept, bounded scalar
\[
\boxed{\widehat\beta(x,y)=\mathrm{clip}_{[-2,2]}
 \frac{\sum_i x_i y_i}{(21/20)\sum_i x_i^2}}
\tag{1}
\]
on an independent calibration collection. A degenerate \(x\) with squared norm below a predeclared threshold gets coefficient zero and an explicit abstention. There is an analogous \(\widehat\gamma(z,y)\) for the other-active control, with exactly equal calibration target exposure and model dimension.

The predictions on new heldout states are \(g^\top b+\widehat\beta R(a)\) and \(g^\top b+\widehat\gamma R(o)\), compared on identical target-erasure labels against the strong direct predictor \(g^\top b\). No new SAE fitting is performed.

## OLM-21A: Frozen finite-residual transfer has exact error decomposition

**Proposition.** For every state and frozen \(\beta\),
\[
\boxed{E(b)-[g^\top b+\beta R(a)]=R(b)-\beta R(a).}\tag{2}
\]

The anchored error relative to the direct-gradient error is
\[
\ell_\beta-\ell_0=|R(b)-\beta R(a)|-|R(b)|.
\]
This is a pointwise identity requiring only differentiability of \(m\) at the clean state. Its implication for average absolute error depends on the **joint** distribution of source and target residuals, not solely on the calibration coefficient's nonzero value.

**Proof.** Substitute \(E(b)=g^\top b+R(b)\) into the definition and subtract. QED.

## OLM-21B: Fixed 5% ridge is a shrunk least-squares slope when the clip is inactive

Let \(X=\sum_i x_i^2>0\), \(C=\sum_i x_i y_i\). Consider the strictly convex calibration objective
\[
F(\beta)=\sum_i (y_i-\beta x_i)^2+\frac{X}{20}\beta^2.
\]
**Theorem.** Its unique unconstrained optimizer is
\[
\boxed{\beta_*=C/((21/20)X).}\tag{3}
\]
Imposing \(\beta\in[-2,2]\) gives the exact optimizer by clipping to the interval; any solution on its boundary is a genuine constrained squared-risk minimizer.

**Proof.** Differentiate the quadratic:
\(F'(\beta)=-2C+2(21/20)X\beta\),
\(F''(\beta)=(21/10)X>0\).
Its unique stationary point is the unconstrained global minimum; strict convexity yields the clipped constrained optimum. QED.

This fit **minimizes a calibration squared-error target with regularization**. It is not an optimizer of the primary heldout *absolute-error* score, even when the calibration and test joint residual distributions coincide.

## OLM-21C: A sharp quadratic-risk shift identity and conditional certificate

For an empirical (or population) joint residual law \(\mu\), let \(\mathbb E_\mu\) denote average and
\[
Q_\mu(\beta)=\mathbb E_\mu[(y-\beta x)^2].
\]
Write \(A_\mu=\mathbb E_\mu[y^2]\), \(C_\mu=\mathbb E_\mu[xy]\), \(B_\mu=\mathbb E_\mu[x^2]\).

For any fixed frozen \(\beta\) and two calibration/heldout laws \(\mu,\nu\),
\[
\boxed{
Q_\nu(\beta)-Q_\mu(\beta)
=(A_\nu-A_\mu)-2\beta(C_\nu-C_\mu)
+\beta^2(B_\nu-B_\mu).
}\tag{4}
\]
Hence
\[
\boxed{|Q_\nu(\beta)-Q_\mu(\beta)|
\le |A_\nu-A_\mu|
+2|\beta||C_\nu-C_\mu|
+\beta^2|B_\nu-B_\mu|.}\tag{5}
\]

**Proof.** Expand the quadratic within each expectation, subtract, then apply the triangle inequality. The coefficientwise bound is sharp whenever the signed moment differences align with the three terms, including one-term differences. QED.

**Conditional transfer certificate.** If, for frozen \(\beta\), the calibration square-risk advantage \(Q_\mu(0)-Q_\mu(\beta)\) exceeds the sum of the shifts from (5) for both \(\beta\) and zero, then \(Q_\nu(\beta)<Q_\nu(0)\). This bound is a sufficient condition in **squared risk**, and requires independently established moment-shift limits before observing target labels. It does not yield a direct guarantee for SMC-21's mean absolute error without additional assumptions.

## OLM-21D: Equal calibration/test distributions can make ridge correction strictly worsen MAE

Let \(x_i=1\) for all ten calibration observations, with target residuals \(y_1=\ldots=y_9=0\), \(y_{10}=10\). Let the heldout empirical joint residual law be **identical** (a new independent copy with the same ten empirical pairs). Then
\[
X=10,\quad C=10,\quad \widehat\beta=\frac{20}{21}.
\]
The **direct clean-gradient residual** predicts zero and has mean absolute error
\[
\frac{9|0|+|10|}{10}=1.
\]
The one-parameter calibration ridge predictor has mean absolute error
\[
\frac{9(20/21)+|10-20/21|}{10}
=\boxed{\frac{37}{21}>1}.
\]

**Theorem.** Even a positive, uniquely calibration-optimal squared-risk slope, equal calibration and heldout residual distributions, and any number of fresh copies do not guarantee a lower **heldout MAE** than the strong direct-gradient baseline. QED by the above exact rational construction. The source residual feature may be measured accurately, yet the choice of a square-loss calibration criterion can be ill-suited to a heavy-tailed absolute-loss target.

## OLM-21E: Stable source marginals do not identify target-residual transfer

Consider two equally sized calibration and fresh datasets with source residual \(x\in\{-1,+1\}\), each sign occurring equally often. In calibration, target residual \(y=x\), and thus (1) gives \(\widehat\beta=20/21\). In the fresh cohort, keep the **identical source residual multiset** but set \(y=-x\). Then
\[
\boxed{\ell_{\rm direct}=|y|=1,\quad
\ell_{\rm frozen}=\left|y-\frac{20}{21}x\right|=\frac{41}{21}>1.}
\]
Calibration squared risk and MAE both favored the fitted correction; heldout both favor the direct gradient. The joint covariate/target cross moment changes sign while the source covariate marginal and its second moment remain identical.

This construction proves that a successful SMC-19 feature-activation match, constant source residual magnitude distribution, and source-only calibration fit cannot identify stability of target erasure residuals on a new family. An independent cohort and the **same-goal paired residual error** are necessary.

## OLM-21F: Exact orthogonal hidden-state gauge covariance

Under a joint orthogonal change of physical hidden coordinates \(Q\) transporting the recurrent teacher and all SAE native physical edits, OLM-19A and OLM-20E show \(E(v)\) and \(g^\top v\) are separately invariant. Therefore each \(R(v)\), its source/target/other calibration moments, \(\widehat\beta\), the SMC-21 per-goal predictions and every registered paired bootstrap statistic are invariant **in exact arithmetic**, provided calibration goals, frozen feature assignments and other-active selection are transported together.

Independent stochastic SAE retraining is outside this invariance premise, just as it was in SMC-19. A numerical orthogonal-gauge sanity check is evidence of correct implementation rather than representation-stable native SAE semantics.

## Experimental interpretation

SMC-21's applied null is **direct true-digit task-gradient prediction**, the stronger SMC-20 descriptive baseline. It asks whether a fixed univariate residual correction inferred **only from the original source calibration** improves fresh-cohort native refit target MAE, and whether it beats an equally parameterized, equally intervention-expensive correction from a different naturally active target SAE decoder. Positive outcomes measure conditional residual transfer in a fixed teacher, while negative outcomes may be caused by target/source joint-distribution shift, choice of squared vs absolute loss, or physical decoder nonlinearity. Neither outcome is equivalent to learning a better Sudoku reasoner or identifying an intrinsic semantic neuron.

No original SMC-19/20 protocol or source weights are modified. Lean kernel formalization would be a separate explicitly scoped task.
