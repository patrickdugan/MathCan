# OLM-11: Exact polyhedral selection cells for sparse recurrent encoders

November 15, 2026. Mathematical companion to [SMC-11](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc11-sae-selection-20261115/research/real_recurrence_sae_v1). This follows the exact-real causal endpoint ordering in OLM-09 and the uniform state/direction robustness theorem in OLM-10. The results are classical geometry of affine classifiers, made into an exact checkpoint-dependent guard for a specific SAE. No priority claim or Lean-kernel proof is made.

## 1. Physical metric and the affine encoder

Fix training normalization mean \(\mu\in\mathbb R^d\), coordinatewise positive scale \(\sigma_j>0\), an encoder \(W\in\mathbb R^{m\times d}\), and bias \(b\in\mathbb R^m\). Its *pre-ReLU* neuron score on a physical recurrent state \(h\in\mathbb R^d\) is

\[
a_i(h)= b_i+\sum_{\ell=1}^d W_{i\ell}\frac{h_\ell-\mu_\ell}{\sigma_\ell}
=\langle v_i,h\rangle+c_i,\quad
v_{i\ell}=\frac{W_{i\ell}}{\sigma_\ell},\quad
c_i=b_i-\langle v_i,\mu\rangle.
\tag{1}
\]

A top-k ReLU SAE retains the k largest positive rectified activations. Require **strictly positive kth score and strictly positive kth–(k+1)th gap**. Exact ties and inactive positions accidentally returned as top-k receive abstention. Norms and perturbations refer to *unstandardized physical* hidden-state coordinates, as in SMC-10.

Write S for the set of k selected positive neurons at a strict point h and t for the unique top-scoring neuron.

## 2. Sharp support and active-atom identity radii

For every active i in S define its positivity-boundary distance

\[
d_i^+=\begin{cases}
a_i(h)/\|v_i\|_2,&\|v_i\|_2>0,\\
+\infty,&\|v_i\|_2=0,
\end{cases}
\]

and for every i in S, j outside S, its crossing-hyperplane distance

\[
d_{ij}=\begin{cases}
(a_i(h)-a_j(h))/\|v_i-v_j\|_2,&\|v_i-v_j\|_2>0,\\
+\infty,&\|v_i-v_j\|_2=0.
\end{cases}
\]

**Theorem OLM-11A (exact strict top-k cell radius).** The maximal open Euclidean ball centered at h and contained in the strict positive top-k selection region has radius

\[
\boxed{\rho_k(h)=\min\Big\{\min_{i\in S}d_i^+,
\min_{\substack{i\in S\\j\notin S}}d_{ij}\Big\}.}
\tag{2}
\]

Every h' with \(\|h'-h\|_2<\rho_k(h)\) keeps the same strictly positive k neuron identities. When \(\rho_k\) is finite, a selected-positivity or selected/unselected equality hyperplane is reached at exactly that distance, showing sharpness.

**Proof.** The strict selection region is the intersection of all open half-spaces \(a_i(h')>0\) for selected i and \(a_i(h')>a_j(h')\) for every selected i and unselected j. The Euclidean distance to each boundary hyperplane equals its positive margin divided by its normal's Euclidean norm, or infinity for a constant positive inequality. An open ball stays in the intersection precisely when it stays in each constituent half-space. The distance from h to the complement of their intersection is the minimum of those hyperplane distances. QED.

The SAE intervention policy in SMC-07–10 uses the unique *highest positive* neuron, t. Its exact active-atom identity radius is

\[
\boxed{\rho_1(h)=\min\Big\{
\frac{a_t(h)}{\|v_t\|_2},
\min_{j\ne t}\frac{a_t(h)-a_j(h)}{\|v_t-v_j\|_2}
\Big\},}
\tag{3}
\]

with the same constant-normal convention. Both radii matter: a top-k support may change while its top neuron remains fixed, while the top neuron can change between existing active members with unchanged top-k support.

**Corollary OLM-11B (fixed decoder direction).** Fix the physical decoder D and scale sigma. If \(\|h'-h\|_2<\rho_1(h)\), the reselected exact SAE active neuron t(h') is t(h). If the selected physical decoder atom has nonzero length, its unit intervention direction

\[
u(h')=\frac{\sigma\odot D_{\cdot,t(h')}}{\|\sigma\odot D_{\cdot,t(h')}\|_2}
\]

equals u(h) exactly. Under \(\|h'-h\|_2<\rho_k(h)\), the positive top-k support also remains unchanged, so a deterministically seeded inactive-feature sampler sees the same inactive-index complement.

## 3. A certificate using exact rational arithmetic

The fitted PyTorch FP32 weights, means, scales, source state and biases are all dyadic rationals when treated as exact real numbers. Hence every score and squared boundary distance is rational. For strict positive margin s and nonzero rational normal w, the guard for a claimed Euclidean radius r is the fully rational inequality

\[
\boxed{r^2\,\|w\|_2^2<s^2.}
\tag{4}
\]

The [OLM-11 exact oracle](selection_cells.py) enumerates every selected/competing hyperplane, computes the **minimum squared boundary radius** as a Fraction, and derives an integer-proved dyadic lower square-root bound. The operational guard compares r squared with the exact squared threshold, avoiding floating-point rounding. A perturbation along the minimizing constraint normal reaches a boundary witness, proving exactness of the squared-radius calculation.

## 4. Composition with OLM-10 robust causal ordering

Let F be the frozen exact-real recurrent continuation and R a fixed intervention amplitude. OLM-10 provides a certificate comparing the finite output effects of nominal active direction u and control v **uniformly** over shared anchor perturbations of size at most eta and selected direction perturbations of size at most eta (or other declared bounds).

**Theorem OLM-11C (selection-stable causal certificate).** If

\[
\boxed{0\le\eta<\rho_1(h),}
\tag{5}
\]

then for *every* admissible \(h'\) in that closed eta-ball, the exact fitted SAE reselects precisely its original highest positive atom and hence the **same physical decoder direction** u. A previously proven OLM-10 active-versus-*fixed-control* causal ordering at anchor budget eta therefore also applies to the **dynamically reselected** active SAE policy at every h' in the ball.

For a deterministic sampled-inactive control, additionally require eta less than \(\rho_k(h)\) so its inactive complement and corresponding sampled index remain unchanged. For a numerically Jacobian-optimal control, the result concerns the **frozen original numerical direction** and never assumes a recomputed singular vector has the same identity.

**Proof.** The strict top-1 cell gives t(h')=t(h). Since the decoder/scale are fixed, the intervention unit vector is constant throughout the ball, so its direction error relative to nominal is zero. OLM-10 certifies the output ordering on a superset that admits anchor error eta and direction error at least zero. The deterministic inactive control has a constant available index list when the top-k support is fixed, giving the additional statement. QED.

The combination is stronger than either ingredient: OLM-10 proves a finite causal effect uniformly over the uncertainty neighborhood, while OLM-11 proves the *actual feature-selection policy* stays fixed there.

## 5. Scientific and implementation limits

Selection support stability does not imply that nonzero SAE activation **magnitudes** or reconstructed hidden states remain constant inside the cell. The intervention concerns a particular decoder direction. Its causal ranking has no automatic semantic interpretation.

The source-pinned Sudoku 16-puzzle cohort has already been inspected in SMC-07–10. The continuation is an exact mathematical audit of known states and requires unseen puzzle families for confirmatory generalization. Changing trained normalization, encoder/decoder weights, top-k, or their stochastic training protocol changes the selection cells and requires new certificates.

The exact-real binary-weight affine scoring model differs from rounded FP32 execution. The experiment cross-checks the nominal identity against Torch but makes no claim about every machine-rounded inference path. Verified pointwise or neighborhood downstream recurrent effects retain their own exact-real evaluation scope.
