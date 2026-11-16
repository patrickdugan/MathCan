# OLM-22: Weighted-median absolute-error SAE residual calibration and conditional transfer

**November 16, 2026.** Written exact finite-dimensional mathematics for the preregistered [SMC-22 absolute-error-calibrated SAE residual experiment](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc22-lad-residual-transfer-20261116/research/real_recurrence_sae_v1/SMC22_PROTOCOL.md). The algebra and weighted median are classical. The concrete rational counterexamples and coupling bounds below are included as source-reviewed exact Fraction regression tests. No Lean kernel formalization or historical novelty claim.

## Setup

Let a frozen recurrent teacher have a fixed hidden-state task margin \(m(h)\) and clean gradient \(g=\nabla m(h)\), where m uses the known Sudoku answer and the strongest clean non-answer rival. For any SAE-native physical decoder contribution \(v\), the finite-erasure residual is \(R(v)=m(h)-m(h-v)-g^\top v\). For the reference SAE erasure \(a\), refitted target erasure \(b\), and another naturally active target SAE control \(o\), set \(x=R(a)\), \(z=R(o)\), \(y=R(b)\).

All three residuals are observed **only on the original source calibration**. The SMC-22 heldout predictions retain the direct clean gradient \(g^\top b\), plus a frozen scalar residual correction with either x or z. They are compared against the original calibration-only ridge scalar fitted before the SMC-21 test and against the new equally parameterized other-active LAD control.

## OLM-22A: Exact deterministic weighted median minimizes no-intercept empirical MAE

Let \(C=\{(x_i,y_i)\}_{i=1}^n\) be finite paired residuals, with at least one \(x_i\ne0\). Define the no-intercept mean absolute calibration error
\[
L_C(\beta)=\frac1n\sum_{i=1}^n |y_i-\beta x_i|,\qquad \beta\in[-2,2].
\]
For each \(x_i\ne0\) define \(r_i=y_i/x_i\) and \(w_i=|x_i|\). Let the ratios be sorted nondecreasingly, ties broken by original puzzle/goal index, and let \(r_*\) be the **first** sorted ratio for which the cumulative weight is at least \(W/2\), \(W=\sum w_i\).

**Theorem.** The deterministic coefficient
\[
\boxed{\beta_{\rm LAD}=\operatorname{clip}_{[-2,2]}(r_*)}
\]
minimizes \(L_C\) over the registered interval. It uses exactly one scalar and remains a valid minimizer in weighted-median intervals of nonuniqueness. Observations with \(x_i=0\) contribute a constant \(|y_i|\) and do not affect the minimizer.

**Proof.** For nonzero x, \(|y_i-\beta x_i|=w_i|r_i-\beta|\). The objective is a weighted sum of absolute deviations plus constants. Its subgradient at any β has nonnegative/negative contributions determined by weights on either side and permits zero precisely when each side carries at most half the total weight. The first cumulative-half ratio \(r_*\) is a lower weighted median satisfying this criterion. Restricting a convex function whose unconstrained minimizer set is an interval to \([-2,2]\) yields a constrained minimizer by projecting any unconstrained minimizer onto that interval. QED.

The no-intercept **ridge** correction from SMC-21 is \( \beta_{\rm ridge}=\operatorname{clip}_{[-2,2]}[\sum x_i y_i/(1.05\sum x_i^2)]\), which minimizes a different, regularized square-loss objective. SMC-22 holds all its original source calibration receipts fixed.

## OLM-22B: Calibration LAD superiority does not imply heldout LAD superiority

**Exact rational witness.** Let all ten calibration source residual covariates be \(x=1\). On seven of ten examples set \(y=0\); on three set \(y=2\). The weighted-median coefficient is \(\beta_{\rm LAD}=0\), while the original 5%-ridge coefficient is
\[
\beta_{\rm ridge}=\frac{3\cdot 2}{1.05\cdot10}=\frac47.
\]
Their calibration absolute errors are
\[
L_C(0)=\frac35,\qquad L_C(4/7)=\frac{29}{35}.
\]
Hence LAD beats ridge strictly in calibration. Now form an independent heldout cohort with the **identical source residual** \(x=1\) on every goal but with \(y=2\) for every new target:
\[
L_{\rm test}(\beta_{\rm LAD})=2,\qquad
L_{\rm test}(\beta_{\rm ridge})=\frac{10}{7}<2.
\]
The new target distribution changed while the source residual covariate distribution remained constant; both fitted parameters were frozen before the heldout cohort.

**Theorem.** Even strict calibration MAE optimality and unchanged source residual marginals cannot establish superiority over the previously calibrated ridge method on new test targets. QED by this exact construction.

## OLM-22C: A coupling-based absolute-risk transfer bound

Let \(\mu,\nu\) be two empirical/population joint residual laws on \((x,y)\), coupled by \(\pi\) with marginals \(\mu,\nu\). For any **frozen** scalar \(|\beta|\le 2\), define \(L_\rho(\beta)=\mathbb E_\rho|y-\beta x|\).

**Theorem.**
\[
\boxed{\left|L_\nu(\beta)-L_\mu(\beta)\right|
 \le \mathbb E_\pi\left[|y'-y|+2|x'-x|\right]}\tag{1}
\]
for every valid coupling; taking the infimum gives a weighted \(W_1\) bound. In the absence of a coupling identified before heldout labels, this is a **conditional** mathematical theorem.

**Proof.** The reverse triangle inequality gives
\[
\big||y'-\beta x'|-|y-\beta x|\big|
 \le |(y'-y)-\beta(x'-x)|
 \le |y'-y|+|\beta|\,|x'-x|.
\]
Take expectations under π and apply \(|\beta|\le2\). QED. The coefficient 2 is sharp when y remains fixed, x changes and β has magnitude 2 with aligned signed loss differences.

**Transfer corollary.** If the original calibration LAD-vs-ridge absolute-risk advantage
\(\Delta_C=L_C(\beta_{\rm ridge})-L_C(\beta_{\rm LAD})>0\), and independently established coupling bounds \(d_{\rm LAD},d_{\rm ridge}\) satisfy \( \Delta_C>d_{\rm LAD}+d_{\rm ridge}\), then the *heldout absolute risk* satisfies \(L_{\rm test}(\beta_{\rm LAD})<L_{\rm test}(\beta_{\rm ridge})\).

**Proof.** Bound each heldout risk by its calibration value plus its own corresponding absolute transfer discrepancy and subtract. A strict gap greater than the combined error forces the sign. QED.

The empirical SMC-22 program does not assume numerical bounds on the old/new joint residual coupling. It measures the actual fresh 64-puzzle cluster paired errors instead.

## OLM-22D: Equal-budget other-active fits and task semantics

For source covariate x and other-active native target SAE covariate z, the weighted-median rule fits one scalar each against the **same calibration target y and same mask**. Both use the original clean task gradient and one additional native erasure observation per heldout goal. Differences in heldout absolute error between those predictors can therefore be attributed operationally to their different residual covariates and calibration fits under the frozen source. Neither one-parameter numerical result identifies intrinsic SAE feature semantics. The decoder gauge ambiguity and exactly reconstructing opposite-erasure aliases from OLM-18/19 remain mathematical obstructions.

## OLM-22E: Gauge invariance and finite sample scope

Under a single jointly transported orthogonal hidden-coordinate basis Q, the task-margin drops \(E(v)\), clean dot products \(g^\top v\), and hence \(x,y,z\) remain unchanged. The weighted-median ratios, deterministic source-index tie breaks, frozen coefficients and every paired test/bootstrap error are then **identical in exact arithmetic**. Independent random SAE refits are not such transported bases.

The SMC-22 goal is to test a prospective *operational prediction* on two new exact-unique Sudoku families, not to claim a deployable answer-free Sudoku reasoner. Its gradient requires the true heldout digit, and four comparisons reuse the same two frozen teacher weights. Even a positive result is only conditional predictive residual transfer.
