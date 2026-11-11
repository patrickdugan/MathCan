# TOE-07: tensor-cone compensation and the limit of FLRW covariant reconstruction

**Status (2026-11-11):** exact algebraic theorems, 17 source-isolated Python test methods, an optional independent SymPy covariant-derivative derivation, and Lean structural lemmas awaiting repository CI. The two-multiplet response is an algebraic ansatz without a derived matter action. The complete Bianconi dressed tensors have not been calculated from the four-dimensional theory. No observational claim or physical stability claim is made.

## 1. Provenance and scope

The physical motivation is Ginestra Bianconi, [*Λ-Gravity from Entropy*](https://arxiv.org/abs/2610.34496), especially the induced metric and dressed-field equations, and David S. Pereira, [*Gravitational Waves and Matter Constraints in Gravity from Entropy*](https://arxiv.org/abs/2609.03082), its strict-principal tensor symbol and matter-sector rank obstruction. Mathematical comparisons begin at [TOE-04](BIANCONI_FLRW_GFIELD_DYNAMICS.md), [TOE-05](BIANCONI_DRESSED_SCALAR_FLRW.md) and [TOE-06](TOE06_COVARIANT_AUDIT.md). The *Theory of Everything with Curt Jaimungal* episode registry is [EPISODE_INDEX.json](EPISODE_INDEX.json); later papers are not attributed to earlier interviews.

The primary-source field-equation definitions of the full `D_(mu nu)` and dressed `T_(mu nu)` are required to complete the intended covariant audit. The derivation below introduces a **particular Ricci-response completion** and explicitly isolates its assumptions. Bianconi's actual 0-, 1-, and 2-form curvature operators include Riemann response information, so equality with her full tensors has not been established.

## 2. Strict-principal two-multiplet response condition

In spatially flat FLRW let `A = Hdot + H²`, `B = H²`. With curvature `K/a²`, replace `B` by `H²+K/a²` and let `delta = A-B = Hdot-K/a²`. Pereira's strict-principal transverse-traceless polynomial in the single-multiplet response sectors is

\[
q_4(\omega,p)={W_s^2\over2}(\omega^2-p^2)^2
 +2(W_E\omega^2-W_Bp^2)^2.
\]

For `W_s,W_E,W_B > 0` and `p != 0`, a real characteristic requires `omega² = p²` and `W_E = W_B`. For the variable `x=omega²/p²`, its quadratic discriminant is exactly

\[
\Delta_x=-4W_s^2(W_E-W_B)^2.
\]

Consider a *declared isotropic effective* 2-form response added to the induced eigenvalues,

\[
\theta_E=1+\alpha m_E-2\beta A,\qquad
\theta_B=1+\alpha m_B-2\beta B,\qquad
W_{E,B}=\theta_{E,B}^{-1}.
\]

**T1 (algebraic matching).** If `alpha,beta > 0` and `theta_E, theta_B > 0`, this symbol has a nonzero real characteristic exactly when

\[
\boxed{\alpha(m_E-m_B)=2\beta\delta.}\tag{1}
\]

Indeed, `theta_E-theta_B = alpha(m_E-m_B)-2 beta delta`. Substituting the inverse responses gives the exact off-matching discriminant

\[
\boxed{\Delta_x=-{4W_s^2[\alpha(m_E-m_B)-2\beta\delta]^2
\over\theta_E^2\theta_B^2}.}\tag{2}
\]

For each desired signed difference `d=2 beta delta/alpha`, the choice
`m_E=max(d,0)+b`, `m_B=max(-d,0)+b`, `b>=0`, is nonnegative and has difference `d`. It gives an admissible *algebraic* construction whenever the resulting tensor eigenvalues remain positive. This shows pointwise response feasibility. It does not provide a multiplet action, a dynamical continuation equation for the responses, or a proof that the metric–matter *coupled* principal system is hyperbolic. The double root at `omega²=p²` also requires a well-posedness analysis beyond root reality.

**TOE-05 reference curve (synthetic, dimensionless).** With `beta=0.01`, `alpha=0.06`, `K=0`, take `m_E=0` and `m_B=-Hdot/3` for the sampled negative Hdot values. The positive induced tensor eigenvalues and exact zero discriminants are calculated from the existing TOE-05 trajectory:

| z | Hdot | required m_B | theta_E = theta_B |
|---:|---:|---:|---:|
| 0.0 | -0.010000000 | 0.003333333 | 0.980200000 |
| 0.1 | -0.016331613 | 0.005443871 | 0.980277284 |
| 0.2 | -0.025184276 | 0.008394759 | 0.980383198 |
| 0.3 | -0.037799867 | 0.012599956 | 0.980536160 |
| 0.4 | -0.055884056 | 0.018628019 | 0.980760914 |
| 0.5 | -0.081556548 | 0.027185516 | 0.981087139 |

The corresponding response trajectory is an algebraic diagnostic, not a field solution. A self-consistent construction must re-solve the background with the new 2-form source, verify positive G-field eigenvalues in **all sectors**, satisfy matter equations, and check the full coupled perturbation symbol and symmetrizer.

### A stronger restricted rank obstruction

**T2 (homogeneous scalar wedge vanishing).** The gradient of any homogeneous scalar is proportional to `dt`, so for any two scalar species `d phi_a ∧ d phi_b = 0`. Thus any source whose 2-form sector is generated solely by these antisymmetric wedges has zero E/B correction regardless of the number of homogeneous scalars. This is verified as an exact four-index antisymmetric identity and formalized in Lean for integer-valued components.

**T3 (two single-bivector rank obstruction).** Consider a narrower microscopic trial model in which each independent 2-form contributes one spatial electric vector `e_i`, and its isotropic electric response would be `M_E = Σ e_i e_i^T` (similarly for magnetic vectors). With only two such fields, `rank(M_E) ≤ 2`. Hence the equality `M_E=c I_3` implies `c=0`; a nonzero strictly isotropic scalar response requires at least three independent E-vector orientations in this trial model. The code checks every pair of 3-vectors with entries in `{-1,0,1}`, giving 729 zero-determinant cases, and exhibits the three-basis-vector identity. This **restricted toy model** has fewer internal components than a general Dirac–Kähler multiplet and therefore does not contradict Pereira's statement that two richer multiplets are the first candidate not excluded by his rank theorem.

## 3. A general Ricci-derivative formula and its limitation

For an arbitrary Ricci-dependent metric action `∫ √(-g) f(g,R_(mu nu),matter)`, let

\[
P^{\mu\nu}=\frac{\partial f}{\partial R_{\mu\nu}}
\]

with other independent variables held fixed. Its connection-variation contribution, using the `(-,+,+,+)` metric, is

\[
D^{(P)}_{\mu\nu}={1\over2}\left(
\Box P_{\mu\nu}+g_{\mu\nu}\nabla_\alpha\nabla_\beta P^{\alpha\beta}
-2\nabla_\alpha\nabla_{(\mu}P_{\nu)}{}^\alpha\right).\tag{3}
\]

This formula is the covariant integration-by-parts variation of the Ricci tensor, with the **displayed derivative ordering**. It is applicable to a Ricci-response theory under its own assumptions. It is not asserted to equal the full Riemann/bivector derivative tensor of ΛGfE.

On flat FLRW with `N=1`, set `P^{00}=-U(t)` and `P^{ij}=V(t)δ^{ij}/a²`. Direct evaluation of the FLRW Christoffels gives

\[
\begin{split}
D^{(P)}_{00}&={3\over2}\left[(U-V)(\dot H+3H^2)+H(\dot U+\dot V)\right],\\
{D^{(P)}_{ii}\over a^2}&=-{1\over2}(U-V)(\dot H+3H^2)
-{\ddot U+\ddot V\over2}-2H\dot U.\tag{4}
\end{split}
\]

**T4 (exact covariant contraction).** The independent `double-divergence`, `rough-Laplacian` and `mixed-divergence` contractions recombine to Eq.(4). The standard-library `Fraction` oracle tests 700 randomly seeded rational states, and an optional `sympy` script rebuilds the expressions from the full four-dimensional Christoffels.

For the metric-proportional response `U=V=f_R`, Eq.(4) reduces to the standard f(R) derivative tensor:

\[
D^{(P)}_{00}=3H\dot f_R,\qquad
D^{(P)}_{ii}/a^2=-\ddot f_R-2H\dot f_R.\tag{5}
\]

Thus a constant `f_R` gives zero derivative tensor, recovering the Einstein–Hilbert limit.

A possible *isotropic Ricci lift* of the reduced logarithmic function `f(A,B,phi,pi)` is

\[
U={2f_A-f_B\over6},\qquad V={f_B\over6}.\tag{6}
\]

To derive Eq.(6), vary `A=-R_00/3` and `B=(R_s-A)/2` inside the isotropic family. The construction matches the background `δA,δB` variations, and in the weak-curvature limit `f_A=f_B=18β` it gives `U=V=3β`. The higher-dimensional off-FLRW tensor response is not uniquely fixed by those two background derivatives, so Eq.(6) is a **particular completion**. A genuine Bianconi tensor check still needs the 0-, 1- and 2-form indexed curvature operator, its metric variation, the corresponding G-field derivatives, and the dressed matter metric variation.

**T5 (why the background does not determine the tensor theory).** FLRW metrics are conformally flat, so the Weyl tensor `C_abcd` vanishes there. An additional action term `λ ∫ √(-g) C_abcd C^abcd` vanishes on the entire homogeneous background and contributes no first-order background field equation, but generally changes the quadratic tensor-perturbation action through `λ ∫ √(-g) (δC)^2`. Hence agreement of an FLRW action and all its homogeneous solutions is insufficient to identify the full TT principal symbol. This is a standard higher-curvature identifiability obstruction, used here as a warning about applying a symmetry-reduced GfE solver to full perturbations.

## 4. Independent verification and unresolved physics

The Python tests cover exact rational arithmetic for the TT symbol and its discriminant, response positivity, the algebraic compensation along TOE-05, scalar wedge vanishing, the restricted 2-vector rank obstruction, and covariant Ricci derivative contractions. They do not certify the missing microscopic matter coupling. The Lean module `MathCan/TOETensorCompletion.lean` proves discrete response-budget and homogeneous wedge identities and simple derivative limit equations after CI.

Next source-dependent tasks: independently obtain and reduce Bianconi's full indexed definitions of `R^G_(mu nu)`, `D_(mu nu)` and dressed `T_(mu nu)`; derive the candidate source multiplets' matter 2-form tensors; solve the coupled background while preserving the algebraic constraint and joint Noether identity; compute the full metric–matter characteristic matrix rather than only the isolated TT polynomial; check hyperbolicity and positive-energy mode content over the physical EFT window.

### Reproduce

```sh
python -m unittest tests.test_toe07_tensor_completion -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOETensorCompletion.lean
# Optional independent symbolic derivation (requires SymPy):
python research/toe/derive_ricci_flrw_sympy.py
```
