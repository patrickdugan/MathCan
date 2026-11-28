# OLM-12: Exact angular cones of self-reinforcing SAE features

November 15, 2026. Continues the [OLM-11 / 11D](OLM11_SELECTION_CELL_THEOREM.md) results on sharp affine feature-selection cells and finite forward decoder-ray crossings. Applied companion: [SMC-12](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc12-conic-self-selection-20261115/research/real_recurrence_sae_v1). The cone and angular-distance facts come from classical convex geometry; this campaign contributes an exact checkpoint-auditable formulation, not a claim of priority in pure mathematics.

## 1. The positive self-selection cone

Let an SAE encoder have affine, **pre-ReLU** scores \(a_i(h)=v_i\cdot h+c_i\), where the physical row vectors \(v_i\) account for the frozen training-only scaling. At a source hidden state h, assume the neuron t has a strictly positive score and is strictly above every competitor. Re-evaluate the **same frozen SAE** after moving the hidden state along a physical direction d:

\[
h(r)=h+r\frac{d}{\|d\|_2},\qquad r\ge0,\quad d\ne0.
\]

Define a finite family of score-margin normals

\[
\mathcal N_t=\{v_t\}\cup\{v_t-v_j:j\ne t\}.
\]

The first normal encodes positivity of the selected neuron; the remaining normals encode its superiority over every competing neuron.

**OLM-12A (exact all-radius self-selection cone).** The selected highest-positive neuron remains t for **every** finite positive ray amplitude r if and only if

\[
\boxed{d\in C_t:=\{d\in\mathbb R^d:n\cdot d\ge0\ \text{for all }n\in\mathcal N_t\}.}
\tag{1}
\]

The cone is a closed convex polyhedral cone. Its interior relative to the ambient direction space consists of vectors with strict positive slopes for every **nonzero** constraint normal (apart from wholly unconstrained cases).

**Proof.** For every \(n\in\mathcal N_t\), the corresponding affine score margin along the ray equals its strictly positive starting value plus \(r(n\cdot d)/\|d\|\). If every slope is nonnegative, each margin remains strictly positive for every r≥0. If some slope is negative, the corresponding margin reaches zero at a finite positive r and becomes negative beyond it. QED.

A score-normal n=0 adds an always-constant positive inequality and can be discarded. A slope exactly zero permits indefinite identity stability along the selected ray but places the ray on the cone boundary, with zero robust angular margin.

## 2. The sharp angular margin

Fix an **interior** ray d and its exact unit direction \(u=d/\|d\|_2\). For each nonzero normal n define the normalized slope

\[
q_n=\frac{n\cdot d}{\|n\|_2\|d\|_2}\in(0,1].
\]

Its squared value \(q_n^2\) is rational whenever the input normal and direction components are rational. Put

\[
\boxed{q_*^2=\min_{n\in\mathcal N_t,\ n\ne0}
       \frac{(n\cdot d)^2}{\|n\|_2^2\|d\|_2^2}.}
\tag{2}
\]

All input quantities are exact rationals in the source-locked PyTorch SAE case because stored FP32/FP64 binary numbers are dyadic rationals and the scale vector is positive. The exact **squared normalized slope** is the primary proof receipt.

**OLM-12B (sharp spherical cap / unit-direction chord).** The greatest angular radius centered at u that is contained in the cone is

\[
\boxed{\theta_*=\arcsin\!\sqrt{q_*^2}}
\quad\text{with}\quad
\boxed{\delta_*^2=2-2\sqrt{1-q_*^2},}
\tag{3}
\]

where \(\delta_*\) is the corresponding Euclidean chord radius between unit vectors. For every unit u' with \(\angle(u,u')<\theta_*\), all score slopes stay strictly positive and t remains highest after **any nonnegative intervention amplitude**. For every angular radius strictly larger than θ*, some unit direction within that radius violates a selected score inequality and eventually changes the selected neuron at a sufficiently large intervention amplitude.

**Proof.** The great-sphere distance from a unit u with n·u>0 to the equatorial hyperplane n·u'=0 is \(\arcsin(n\cdot u/\|n\|)\). The closest equator point is the normalized orthogonal projection of u onto n⊥ when \(q_n<1\); when q_n=1 any orthogonal great-circle path reaches the equator after π/2. The sphere's intersection with all nonnegative hemispheres has its nearest complement boundary at the minimum such distance. The Euclidean chord subtending an angle θ has squared length \(2-2\cos\theta\), giving (3). Strict angular perturbations below θ* remain inside every hemisphere, and any slightly larger cap meets the opposite halfspace of a limiting constraint. QED.

### Fully rational angular guard

For any nonnegative proposed unit-vector chord tolerance δ satisfying \(0<\delta^2<2\), the strict sufficient-and-sharp test is the **rational inequality**

\[
\boxed{
q_*^2>\delta^2-\frac{\delta^4}{4}.
}
\tag{4}
\]

Indeed, δ² < 2−2√(1−q²) is equivalent, after squaring two nonnegative sides, to q² > δ²−δ⁴/4. The zero-radius case is valid for a ray lying on the cone boundary. A fully unconstrained cone admits every unit direction. The [exact-rational oracle](conic_self_selection.py) evaluates this guard without transcendental approximations.

## 3. Sharp relative perturbation of a raw decoder vector

The chosen physical decoder atom before mathematical normalization is a nonzero raw vector d. Let its actual physical decoder components change to d+e, with \(\|e\|_2\le\rho\|d\|_2\). Positive scaling during normalization cannot change the signs of the margin slopes.

**OLM-12C (exact raw decoder robustness).** For a strictly interior ray, the largest open relative Euclidean ball of decoder vectors centered at d that remains inside the self-selection cone has sharp radius

\[
\boxed{\rho_*=\sqrt{q_*^2}.}
\tag{5}
\]

Thus **every** perturbation with \(\rho<\rho_*\) still yields a decoder direction whose positive ray preserves the same SAE top neuron for all amplitudes r≥0. The exact guard is simply \(\rho^2<q_*^2\).

**Proof and sharp witness.** For a constraint with normal n and positive n·d, the Euclidean distance from d to its hyperplane n·x=0 is \((n\cdot d)/\|n\|_2\). Dividing by \(\|d\|\) and minimizing across constraints gives (5). For a minimizing n the exact displacement

\[
\boxed{e_*=-\frac{n\cdot d}{\|n\|_2^2}n}
\tag{6}
\]

reaches the boundary and has \(\|e_*\|^2/\|d\|^2=q_*^2\). Every slightly larger displacement \((1+\varepsilon)e_*\) makes that score-gap slope strictly negative, proving sharpness. QED.

This is tighter than transporting an arbitrary normalized direction-error bound such as \(2\rho/(1-\rho)\), since it reasons directly about the cone of *unnormalized* physical decoder vectors.

### Encoder-normal perturbations

If in addition each original nonzero score constraint normal n changes to n+f with \(\|f\|\le\eta\|n\|\), the lower bound

\[
(n+f)\cdot(d+e)
\ge\|n\|\|d\|\,[q_n-\rho-\eta(1+\rho)]
\]

gives the **OLM-12D joint sufficient condition**

\[
\boxed{q_*^2>[\rho+\eta(1+\rho)]^2.}
\tag{7}
\]

This is conditional on the selected feature **still having strictly positive score margins at the starting anchor under the modified encoder**. A changed encoder bias, training mean/scale, or normalization requires a separate starting-selection guard. Equation (7) establishes angular cone membership after allowed constraint-normal changes, rather than unconditional stability of an independently retrained SAE.

## 4. Composition with previous robust causal statements

Let the initial physical h lie in the strict top-one cell t, whose exact ball radius \(\rho_1(h)\) was certified by OLM-11. Let the decoder d lie in the interior of C_t with cone margin q*. If an alternative initial hidden state h' satisfies \(\|h'-h\|<\rho_1(h)\), and a modified physical raw decoder d' satisfies \(\|d'-d\|<\rho_*\|d\|\), then **for every r≥0** the exact-real SAE's highest-positive neuron at

\[
h'+r\frac{d'}{\|d'\|}
\]

is t. This follows by applying the starting feature-cell theorem at h' and the conic all-radius theorem to d'.

**Scope of this composite result:** it certifies the **discrete SAE top-feature identity** at arbitrary positive intervention amplitudes under bounded anchor and raw decoder uncertainty. It does **not** certify the frozen recurrent teacher's downstream logit magnitude ordering for arbitrary r. SMC-10's separate source-locked Arb causal bounds control the downstream ranking only at their declared radii and much smaller uncertainty budgets. To combine both guarantees, one must satisfy both sets of premises and use the *same frozen SAE/teacher snapshots*.

## 5. Frozen-weights application and proof-carrying reproducibility

[SMC-12](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc12-conic-self-selection-20261115/research/real_recurrence_sae_v1) loads the fully audited SMC-11C artifact, checks its exact JSON and all three SAE weight file SHA-256 values, and recomputes every cone normal \(v_t\) and \(v_t-v_j\) using the frozen physical SAE encoder and the same post-FP64-normalization dyadic decoder direction used by SMC-09–11.

Its initial exact-rational audit over all 48 frozen goal-token/SAE cases finds:

- Every positive decoder ray is an **interior** cone ray. All 96 nontrivial positivity/competitor slopes are strictly positive per case.
- Minimum \(q_*^2\) is approximately 0.0469986747628, giving sharp raw relative decoder margin **0.2167917774**, angular margin **0.2185268848 radians = 12.52°**, and unit-chord margin **0.2180923304**.
- Consequently a **relative physical decoder-vector perturbation of 20%** remains inside the positive self-selection cone on all 48 cases, as does a unit-direction chord perturbation of 0.2.
- A joint relative perturbation budget of 10% in each constraint normal and 10% in the raw physical decoder direction also passes the sufficient cone-slope condition in all 48 cases, **conditional** on independently confirming strict source feature selection under the modified encoder.
- The exact boundary witness in (6), and a slightly overshot rational witness, are checked for every limiting score constraint. These establish sharpness of each reported raw margin.

These are exact-real feature-ID geometry results on the previously inspected Sudoku fixture set. No new pretrained teacher checkpoint, broader puzzle-family holdout, or semantic SAE interpretability claim is asserted. The [OLM-12 standalone Fraction tests](../../tests/test_conic_self_selection.py) check the mathematical identities without importing any pretrained model. The corresponding source-pinned experimental replay is independently recorded in Compactification-Theory.

## 6. OLM-12E: Self-reinforcing atoms are columns of an internal encoder-decoder Gram

A useful structural simplification follows by writing the *exact-real* unnormalized physical decoder atom as \(d_t=\sigma\odot D_{\cdot t}\) while the physical preactivation normal is \(v_i=W_{i\cdot}/\sigma\), with each scale \(\sigma_\ell>0\).

Then the slope of the ith encoder score along the tth decoder ray is

\[
\langle v_i,d_t\rangle
=\sum_{\ell}(W_{i\ell}/\sigma_\ell)(\sigma_\ell D_{\ell t})
=\boxed{(WD)_{it}.}
\]

Call \(K=WD\in\mathbb R^{m\times m}\) the encoder-decoder **cross-talk matrix**, which is generally nonsymmetric and must not be confused with the downstream causal Gram operator of OLM-07.

**Theorem OLM-12E (exact column-dominance characterization).** For the ideal exact-real raw decoder product \(d_t=\sigma\odot D_{\cdot t}\), the tth neuron has an all-radius self-reinforcing positive ray at every hidden state where t starts highest and positive if and only if

\[
\boxed{K_{tt}\ge0,\qquad K_{tt}\ge K_{jt}\quad(\forall j\ne t).}
\tag{8}
\]

Strict positive inequalities make the selected raw decoder an angular **interior** ray. The property is independent of the frozen *positive* standardization scale \(\sigma\): it is determined by the W,D weights alone.

**Proof.** Substitute the scale cancellation above into the positivity and competitor score-slope conditions (1). Those conditions become precisely (8). QED.

The exact matrix \(K=WD\) is easily audited without test inputs. It characterizes the *possibility* of self-reinforcing ray selection conditional on t being a strictly highest positive neuron at the anchor. It does not guarantee the tth neuron is ever activated on the source data.

The applied SMC-12B control measures (8) across **all 96 decoder atoms** in each of three source-frozen SAEs and their original random initializations, preserving the exact initial decoder SHA-256 from SMC-07. The actual causal direction in SMC-09 is computed by FP32 elementwise decoder×scale multiplication followed by FP64 normalization, so its stored binary components are not necessarily an exact scalar multiple of the *ideal* raw dyadic decoder product. The experiment checks both the ideal matrix condition and the actual frozen-dyadic cone condition independently and reports any discrepancy. No algebraic cancellation across individually rounded machine operations is assumed.

This internal cross-talk result also clarifies the scientific boundary: diagonal dominance of WD can be favored by reconstruction training, while **downstream task sensitivity** is governed by the teacher Jacobian and its separate Gram \(D^\top H D\). Self-reinforcement of an SAE atom and semantic causal interpretability are different properties.
