# OLM-10: Robust finite causal ordering on uncertain recurrent-state neighborhoods

**Date:** November 15, 2026. Continues merged OLM-09 exact endpoint ordering, and the source-locked SMC-07 through SMC-09 recurrent SAE experiments. The new application is SMC-10 in Compactification-Theory. The results below use elementary interval inclusion, triangle inequalities and finite-set optimization. Their synthesis for the active SAE intervention is new to this campaign; independent mathematical priority is not established. No new Lean kernel formalization is claimed.

## 1. A precise uncertain-intervention contract

Fix a frozen full recurrent state \(H\in\mathbb R^{T\times d}\) and a selected goal token \(g\), with \(d=48\) for the pinned Sudoku teacher. Let \(h=H_g\in\mathbb R^d\). The other \(T-1\) token states remain **fixed**. Define the exact-real output map
\[
F(x)=\operatorname{head}\big(R^3(H\text{ with token }g\leftarrow x)\big)_g\in\mathbb R^{10}.
\]

Let the nominal selected directions \(u,v\in\mathbb R^d\) be exact-real unit vectors and let the intervention radius \(r>0\) be an exact rational. The admissible uncertainty class consists of a **common anchor** \(h'\) and alternative unit directions \(u',v'\) satisfying
\[
\|h'-h\|_2\le\delta_h,\quad\|u'-u\|_2\le\delta_u,\quad\|v'-v\|_2\le\delta_v.
\]
The clean and perturbed states for *each* comparison use the same admissible \(h'\), and the two perturbed states use the same exact radius \(r\). The uncertainty budgets are chosen before examining the model's test outputs.

We seek a certificate for the **uniform finite-endpoint relation**
\[
\boxed{\|F(h'+ru')-F(h')\|_2>\|F(h'+rv')-F(h')\|_2}
\tag{1}
\]
for every admissible triple. This is strictly stronger than OLM-09's pointwise ordering at \((h,u,v)\), and much weaker than dominance over arbitrary recurrent states or intervening radii.

## 2. A sound, finite-dimensional outer box

For a vector \(x\) and \(t\ge0\), write \([x\pm t]_\infty\) for the Cartesian product of coordinate intervals \([x_j-t,x_j+t]\).

**Theorem OLM-10A (robust endpoint inclusion).** Every admissible clean and perturbed input belongs respectively to the following boxes:
\[
\begin{aligned}
B_0&=[h\pm\delta_h]_\infty,\\
B_u&=[h+ru\pm(\delta_h+r\delta_u)]_\infty,\\
B_v&=[h+rv\pm(\delta_h+r\delta_v)]_\infty.
\end{aligned}
\tag{2}
\]
Suppose a validated interval forward evaluator \(\mathcal I_F\) returns componentwise enclosing ten-logit intervals for all inputs in each box. Define
\[
I_u=\sum_{j=1}^{10}\operatorname{sq}\big(\mathcal I_F(B_u)_j-\mathcal I_F(B_0)_j\big),\qquad
I_v=\sum_{j=1}^{10}\operatorname{sq}\big(\mathcal I_F(B_v)_j-\mathcal I_F(B_0)_j\big),
\tag{3}
\]
where \(\operatorname{sq}\) is a validated interval square. Then
\[
\boxed{\inf I_u>\sup I_v\Longrightarrow\text{(1) for every admissible }(h',u',v').}
\tag{4}
\]
The opposite strict inequality certifies the reverse ordering, and overlapping interval enclosures require abstention.

**Proof.** A Euclidean ball of radius \(t\) lies in the corresponding coordinatewise \(\ell_\infty\) box of radius \(t\). For each coordinate,
\(\left|(h'_j+ru'_j)-(h_j+ru_j)\right|\le|h'_j-h_j|+r|u'_j-u_j|\le\delta_h+r\delta_u\).
The other boxes follow the same way. Inclusion-valid interval arithmetic gives enclosures of the clean and the two endpoint outputs. Subtraction and interval squaring enclose every output displacement and its squared L2 norm; positivity of a strict interval gap proves (4). QED.

The independent box evaluations lose the correlation of the shared anchor. That makes the result conservative and protects soundness: a nonzero certified radius establishes an **entire input neighborhood**, while a failure only means the current interval extension is inconclusive. No uniform Hessian estimate is required.

## 3. The radius that is actually certified

The boxes in (2) are nested as any uncertainty budget increases. Consequently, a certificate for \((\delta_h,\delta_u,\delta_v)\) also logically certifies every smaller nonnegative budget triple. The underlying set of triples on which the strict ordering is true is likewise downward closed. A finite grid of successful interval evaluations supplies a rigorously justified **lower robustness frontier**; it does not locate the exact boundary at which the network truly changes ordering. A bisection using certified inclusion must preserve its previous successful witness and must not treat numerical noncertification as a counterexample.

For a common budget \(\eta\) across anchor and both directions, the perturbed boxes have half-width \((1+r)\eta\) and the clean box half-width \(\eta\). The resulting \(\ell_\infty\) hull encloses the stipulated \(\ell_2\) ball, and this concrete factor \(1+r\) should accompany every reported \(\eta\) to make the robustness claim auditable.

## 4. Normalized decoder-atom uncertainty

SAE weights themselves may be uncertain. Let \(w\ne0\) be a frozen decoder atom and \(w'=w+e\), with \(\|e\|_2\le\rho\|w\|_2\), \(0\le\rho<1\). Put \(u=w/\|w\|_2\) and \(u'=w'/\|w'\|_2\).

**Lemma OLM-10B (raw-weight to physical-direction budget).**
\[
\boxed{\|u'-u\|_2\le\frac{2\rho}{1-\rho}.}
\tag{5}
\]
**Proof.** Using \(\|w'\|\ge\|w\|-\|e\|\) and the reverse triangle inequality,
\[
\left\|\frac{w'}{\|w'\|}-\frac{w}{\|w\|}\right\|
\le \frac{\|e\|}{\|w'\|}+\frac{|\|w\|-\|w'\||}{\|w'\|}
\le \frac{2\|e\|}{\|w\|-\|e\|}\le \frac{2\rho}{1-\rho}.
\]
QED.

This gives a sound way to translate an independent bound on decoder-weight changes into the \(\delta_u\) budget of (2). The numerical feature *selection* and its top-k support must also be fixed; (5) does not certify that the same learned atom would be selected after retraining.

## 5. Counterexample to overclaiming from a fixed endpoint

Take \(F:\mathbb R^2\to\mathbb R^2\), \(F(x,y)=(2x,y)\), with nominal \(h=(0,0)\), \(u=e_1\), \(v=e_2\), and \(r=1\). At the nominal endpoints the active effect is 2 and the control effect is 1. The fixed-endpoint certificate is strict. For admissible uncertainty \(\delta_u=2\), the alternative unit vector \(u'=e_2\) lies within the direction ball because \(\|e_1-e_2\|=\sqrt2<2\), so strict dominance can fail. A pointwise interval certificate at \(\eta=0\) therefore never implies arbitrary neighborhood robustness.

Conversely, sufficiently small rectangular uncertainty boxes around these endpoints preserve strict interval separation under exact rational arithmetic, as the [OLM-10 oracle](robust_endpoint.py) verifies. An unchanged ranking at one selected radius does not imply its validity at adjacent radii.

## 6. Applied numerical contract

The [SMC-10 exact-real Arb endpoint evaluator](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc10-robust-endpoint-neighborhoods-20261115/research/real_recurrence_sae_v1) reuses the source-hashed frozen 44K TRM-inspired Sudoku teacher, fixed 64-puzzle roster and SMC-09 SAE directions. At a **predeclared finite uncertainty grid**, it feeds the outer boxes (2) through the existing outward-rounded Arb erf-GELU and population LayerNorm recurrence, with all non-goal tokens fixed. It reports the number of strict certified active-vs-isotropic and active-vs-inactive comparisons, each uncertainty budget and any abstentions. An optional calibrated pure fixed-endpoint regression must agree with SMC-09 at \(\eta=0\).

The certificate concerns the exact-real function on the selected input box. It excludes FP64 kernel rounding and model-weight perturbations unless independently supplied budget bounds are mapped to the input/direction balls. These are repeat analyses on the same previously examined 16 puzzle IDs, and are not an independent model-generalization claim.

[Exact rational finite verification](robust_endpoint.py) and [five local tests](../../tests/test_robust_endpoint.py) establish the inclusion and strict-order contracts without relying on a neural checkpoint, Arb library or GPU. The scientific question is how much of the SMC-09 ordering survives bounded perturbations of the hidden patch and selected feature directions.