# TOE-12: Jordan chains, six-mode tensor mixing, and the auxiliary G-field gate

**2026-11-11. Verification scope:** Exact algebra on the explicitly declared TOE-10/11 non-Abelian logarithmic two-form model. A first-order companion of the TOE-11 single-TT/single-gauge polarization has a nonzero square-zero polynomial in it. Including both metric TT polarizations and two tensor polarizations from each of the two SU(2) gauge triplets leaves a double characteristic **per helicity**. A separate exact linearization eliminates the *algebraic 2-form* G-field. The bare Yang–Mills principal gauge nulls and Gauss quotient are calculated. **This is not a complete gauge-fixed characteristic polynomial of ΛGfE**, and it does not prove its coupled Cauchy problem is weakly or strongly hyperbolic.

## Sources, hypotheses, and reproducibility

- [Bianconi, *Gravity from Entropy*, Phys. Rev. D 111, 066001 (2025)](https://doi.org/10.1103/PhysRevD.111.066001), [arXiv:2408.14391](https://arxiv.org/abs/2408.14391): 0/1/2-form operator, Abelian gauge-field 2-form term, Lorentzian bivector metric and auxiliary G-field.
- [Bianconi, *Λ-Gravity from Entropy* (2026)](https://arxiv.org/abs/2610.34496): independent constrained volume multiplier and full dressed metric equations.
- [Pereira, *Gravitational Waves and Matter Constraints in Gravity from Entropy* (2026)](https://arxiv.org/abs/2609.03082): high-frequency TT obstruction in specified matter sectors, motivation for a multiplet extension.
- [TOE-10](TOE10_NONABELIAN_KREIN_DYNAMICS.md): **proposed** Killing-form-contracted SU(2)² two-form tensor and `−σ log det Θ₂` gauge-medium action. A non-Abelian Dirac–Kähler extension and complete ΛGfE action have yet to be identified with this trial model.
- [TOE-11](TOE11_COUPLED_PRINCIPAL_SCHUR.md): six-dimensional 2-form susceptibility and a first TT/gauge tensor projection, with the `i`-phase and physical gauge constraints explicitly left open.

All executable quantities are exact `fractions.Fraction`, using deterministic background inputs. The positive-real spectrum gate for the background 2-form operator and hyperbolicity of its fluctuation PDE are **independent tests**. Numerical experiments here are neither cosmological data nor predictions about gravitational waves.

## T1. An exact Jordan obstruction in the original one-polarization restriction

Write `x = ω²` at unit spatial momentum. The TOE-11 polarization's source-derived 2×2 *formal* polynomial is

\[
P(\omega)=\begin{pmatrix}
 a(\omega^2-r)^2&b\omega(\omega^2-r)\\
 b\omega(\omega^2-r)&c\omega^2+d
\end{pmatrix},\qquad a>0,\quad c\ne0,\quad ac-b^2\ne0. \tag{1}
\]

The reference exact coefficients are obtained by `research/toe/wave_principal.py`, with

\[
\boxed{r=\frac{480993997}{493000000},\quad
s=\frac{2812732928347778628181199}{2812735172899996567572050}.}\tag{2}
\]

In particular `c*r + d` is nonzero. Factoring gives

\[
\det P(\omega)=(ac-b^2)(\omega^2-r)^2(\omega^2-s). \tag{3}
\]

The formal differential system associated with Eq. (1), retaining the displayed polynomial signs, has two equations of orders four and two. Differentiating the second equation once and eliminating its third gauge derivative gives a **regular** six-state first-order companion on `(h,h',h'',h''',g,g')`. Its full characteristic polynomial is `χ(λ)=(λ²−r)²(λ²−s)`, independently reconstructed by Faddeev–LeVerrier and the original 2×2 determinant.

Put

\[
N=(C^2-rI)(C^2-sI).
\]

**T1 (exact nonsemisimplicity).** Fraction arithmetic proves

\[
\boxed{N\ne0,\quad N^2=0,\quad \mathrm{rank}\,N=2.}\tag{4}
\]

At each of `λ=±√r`, the 2×2 source polynomial has rank one because its metric row vanishes and `c*r+d ≠0`; the determinant has root order two. Consequently each root carries a length-two Jordan chain. A nonzero square-zero polynomial in a matrix obstructs a positive-definite symmetrizer making that matrix self-adjoint: if `SC=CᵀS`, its polynomial `N` is also S-self-adjoint, so `⟨Nx,Nx⟩_S = ⟨x,N²x⟩_S=0` for every x, forcing `N=0`. Contradiction.

This is a **linear-algebra certificate for the formal restricted companion**. Transport to the physical Cauchy problem requires coherent Fourier phases, gauge-fixing and a regular PDE reduction. In particular an arbitrary projected subblock need not define an invariant subsystem of the full tensor evolution.

## T2. Both TT polarizations and both SU(2) tensor flavors

The six amplitudes in the extended projection are

\[
(h_+,h_\times,a_{1+},a_{1\times},a_{2+},a_{2\times}).
\]

The two metric modes are `h₁₁=-h₂₂` and `h₁₂=h₂₁`; each flavor has two color/spatial symmetric trace-free gauge amplitudes. The wave covector is `ξ=(ω,0,0,1)` in the local orthonormal frame. For each amplitude, `δR` is calculated using the linearized Riemann curvature and `δF=ξ∧a`. The exact 6×6 quadratic form uses the **noncommuting** 2-form second variation from TOE-11, independently cross-checked against the polarization identity `(Q(u+v)-Q(u)-Q(v))/2`.

### Parity-sensitive couplings are present

The original TOE-11 same-polarization matrix misses a coupling between opposite helicity labels. At `ω=0`,

\[
P_{h_+,a_{1\times}}(0)=
\frac{711381459342108027}{281238653882043069757205},\qquad
P_{h_\times,a_{1+}}(0)=
-\frac{711381459342108027}{281238653882043069757205}.\tag{5}
\]

This is the mixed electric–magnetic background at work. The **whole** six-mode bilinear matrix is symmetric even though these cross-helicity entries have opposite signs when helicity labels are exchanged. Its 21 independent entries are interpolated as polynomials of degree ≤4 and independently checked at four extra frequencies, including rational noninteger frequencies.

### Exact multiplicity-four factorization

Let `δ=ω²−r`. Every metric-metric entry is divisible by `δ²`. Every metric-gauge entry, including the parity-sensitive terms, is divisible by `δ`. Therefore the entire six-mode symbol has the form

\[
\boxed{
P_6(\omega)=\begin{pmatrix}
\delta^2 A&\delta B(\omega)\\
\delta B(\omega)^\top&G(\omega)
\end{pmatrix},}\tag{6}
\]

with `A` 2×2, `B` 2×4, and `G` 4×4. Row and column factorization yields

\[
\det P_6(\omega)=\delta^4
\det\begin{pmatrix}A&B(\omega)\\B(\omega)^\top&G(\omega)\end{pmatrix}.\tag{7}
\]

The second determinant is evaluated exactly at `ω=√r` in the quadratic extension `Q(√r)`. It is nonzero, as is `det G(√r)`, and the weighted six-by-six highest-derivative matrix is invertible. Thus the factor `(ω²−r)^4` is **exactly of multiplicity four** at this test background. The original six-mode polynomial at each root has rank four and nullity two. Analytic Schur reduction gives the local Smith normal form with two `(ω−√r)^2` factors. The same holds at the negative root, giving **two length-two Jordan chains** in a regular 16-state polynomial linearization of this restricted tensor subspace.

These conclusions survive replacing the second electric field by `999/1000`, `1`, or `1001/1000`. Exact rational determinants and nullity witnesses are in the fixture. The gauge tensor modes are *transverse at principal level*. They do not supply the omitted gravitational one-form/scalar response, unconstrained spatial metric fields, or all auxiliary G fluctuations. Hence Eq. (7) is a property of a **selected six-mode trial tensor block**, not the complete ΛGfE tensor determinant.

## T3. What can be eliminated from the G-field constraint

Within the declared invertible 2-form operator `Θ₂`, the algebraic G-field is `G₂=Θ₂⁻¹`. Its full noncommuting linearization is exactly

\[
\boxed{\delta G_2=-G_2(\delta\Theta_2)G_2}.\tag{8}
\]

For a finite rational perturbation ε and `G_ε=(Θ₂+ε δΘ₂)⁻¹`, the exact resolvent identity yields

\[
G_\varepsilon-G_2+\varepsilon G_2\delta\Theta_2 G_2
=\varepsilon^2 G_2\delta\Theta_2 G_2\delta\Theta_2G_\varepsilon.\tag{9}
\]

The separate 6×6 oracle checks Eq. (8) on both sides of the inverse constraint and Eq. (9) as an exact matrix identity, including noncommuting rational perturbations. This **algebraically** removes the 2-form G-field variation of the assumed logarithmic action. The 0- and 1-form channels, the covariant metric equations and the actual non-Abelian GfE operator remain separate source-dependent work.

## T4. Bare Yang–Mills principal gauge quotient

For any nonzero covector `ξ`, the six-by-four linear map `a↦ξ∧a` has rank three and kernel `span(ξ)`. Choose any pivot `ξ_p≠0`; the unique gauge representative satisfying `a_p=0` is

\[
a'=a-\frac{a_p}{\xi_p}\xi,\qquad \xi\wedge a'=\xi\wedge a.\tag{10}
\]

The **bare** Yang–Mills principal equation has symbol

\[
L_\nu(\xi,a)=\xi^2a_\nu-\xi_\nu(\xi\cdot a).\tag{11}
\]

On a null covector `ξ=(1,0,0,1)`, the gauge slice `a_0=0` and the Gauss constraint impose `a_3=0`; the physical transverse amplitudes `a_1,a_2` remain. For six adjoint colors in two SU(2) factors, that counts 12 bare transverse modes. The calculation covers the **minimal YM principal part**. Nonminimal logarithmic coupling alters the gauge constitutive symbol and demands its own Gauss equation and reduced symmetrizer. There is no claim of a complete gauge reduction of the non-Abelian GfE action.

## T5. A missing-sector correction can remove the projected defect

As a mathematical non-uniqueness check, introduce a **hypothetical** correction to the metric entry,

\[
P_{hh}\longrightarrow P_{hh}+\varepsilon(\omega^2-r),
\qquad \varepsilon=a/10000.\tag{12}
\]

Its determinant has a single factor `(x−r)` times an explicit quadratic `Q(x)`. Exact rational sign checks show `Q(r−1/1000)>0`, `Q(r)<0`, and `Q(s)>0`. Therefore the three squared-frequency roots are all positive and **distinct**. The regular six-state companion in this mathematical completion is diagonalizable over the reals. The correction is an *illustrative freedom*, not a term found in Bianconi's 0/1-form action. It establishes why obtaining those omitted terms from the primary source is mandatory before making a physical hyperbolicity verdict.

## Verification and next gates

Run from repository root:

```sh
python -m unittest tests.test_toe12_jordan tests.test_toe12_tensor_subspace tests.test_toe12_gfield_inverse -v
python -m research.toe.jordan_principal
python -m research.toe.tensor_subspace
python -m research.toe.gfield_linearization
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOEJordan.lean
```

The 45 new test methods include exact 6×6 characteristic polynomials, rank-two nilpotents, a polynomial completion counterexample, 21-component six-mode tensor interpolation, quadratic-field determinants, generic rational gauge quotients and noncommuting auxiliary G-field resolvents. Lean proves **14 conditional algebraic identities**, including a no-positive-symmetrizer lemma for the Jordan normal form, gauge wedge relations and a scalar inverse constraint. The exact rational **specific six-by-six and sixteen-state** computations remain executable proofs, with full Lean matrix formalization open.

**Next physical tasks:** reconstruct source-defined 0/1/2-form variations of the complete ΛGfE action, gauge-fix and eliminate *all* metric/G/gauge constraints, account for background equations, and compute the real Fourier principal matrix and a frequency-uniform symmetrizer over all directions. Test both the strict low-energy effective-theory cutoff and the known extra gravitational modes. The six-mode counterexample and hypothetical completion identify the algebra that these calculations must resolve.
