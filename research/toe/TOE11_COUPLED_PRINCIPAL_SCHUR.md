# TOE-11: Curvature–gauge mixed principal blocks, rank-one Schur cancellation, and restricted wave cones

**11 November 2026.** Exact algebra for a specified logarithmically coupled SU(2)² gauge/2-form action, independently checked with pure-Python rational arithmetic, six-dimensional bivector-operator variations, and optional SymPy differentiation. The mixed curvature–gauge block is **nonzero**. The homogeneous highest-derivative kinetic Hessian has a rank-one cancellation and admits a positive-definite sum-of-squares certificate on a specified domain. A fixed, single-TT-plus-gauge-tensor wave projection has a **doubled real characteristic** and a second real characteristic in the reference sample. **These are partial symbols of an explicitly proposed action, not the full gauge-fixed ΛGfE gravity–matter characteristic matrix.** Neither spectral reality nor positive homogeneous jet energy establishes strong hyperbolicity, Ostrogradsky freedom, or physical viability.

## Sources, scope and conventions

- [Bianconi, *Gravity from entropy*, arXiv:2408.14391](https://arxiv.org/abs/2408.14391), Appendix A's Abelian gauge-field outer product in the 2-form matter sector and Appendix B's Lorentzian 2-form metric. A multi-SU(2) Killing-form extension remains a hypothesis.
- [Bianconi, *Λ-Gravity from Entropy*, arXiv:2610.34496](https://arxiv.org/abs/2610.34496) supplies the full G-field and volume-constrained gravitational system. Its additional 0/1-form and auxiliary field/constraint equations are **not** included in TOE-11's trial action.
- [Pereira, *Gravitational Waves and Matter Constraints in Gravity from Entropy*, arXiv:2609.03082](https://arxiv.org/abs/2609.03082) derives the strict-principal TT cone obstruction for its stated vacuum/single-multiplet/perfect-fluid domains. TOE-11's multi-gauge projection cannot be identified with that complete symbol by interpolation.
- MathCan [TOE-08C](TOE08_TWO_GAUGE_TRIADS.md), [TOE-09](TOE09_LORENTZ_BIVECTOR_SPECTRUM.md), and [TOE-10](TOE10_NONABELIAN_KREIN_DYNAMICS.md) define the triad matter fields, Lorentzian Krein gate, and trial action examined here.

Use signature `(-,+,+,+)`, bivector ordering `(01,02,03,23,31,12)`, and the corresponding raised-pair signature `S=diag(-I3,+I3)`. Let `I` range over gauge flavors and `a` over their three SU(2) colors. With homogeneous triads, `F^a_I` has electric components `E_I δ_i^a` and magnetic components `B_I δ_i^a`; the Killing-form contracted covariant bivector Gram matrix is `G = Σ_{I,a} F_I^a (F_I^a)^T`. Its mixed operator has three repeated blocks

\[
\Theta_* = \begin{pmatrix} s&\alpha c\\-\alpha c&t\end{pmatrix},\quad
s=1-\alpha e-2\beta A,\quad t=1+\alpha b-2\beta B,
\quad e=\sum E_I^2,\ b=\sum B_I^2,\ c=\sum E_IB_I,
\quad D=st+\alpha^2c^2. \tag{1}
\]

Here `A=H²+Hdot`, `B=H²` on flat FLRW. The physical positive-real semisimple condition additionally demands a nonnegative discriminant, positive trace/determinant and diagonalizability; a positive `D` **alone** is only the domain of the real logarithm of the determinant. We keep those gates separate.

## T1. The exact homogeneous rank-one mixed Hessian

The *declared* trial Lagrangian per physical volume is

\[
\mathcal L(A,B,E_I,B_I)=\frac32(e-b)-3\sigma\ln D.
\tag{2}
\]

Fix `B` and the magnetic field strengths `B_I` while differentiating with respect to the curvature acceleration `A` and the electric field strengths `E_I`. Since `A` contains `ddot(a)/a` and `E_I` contains `dot(psi_I)`, these are the highest derivative jets in this homogeneous restricted action. Put

\[
v_I=tE_I-\alpha cB_I,\qquad w=1-2\beta B=t-\alpha b.
\]

Direct differentiation gives

\[
\begin{aligned}
\mathcal H_{AA}&=\frac{12\sigma\beta^2t^2}{D^2},\\
\mathcal H_{AE_I}&=\frac{12\sigma\alpha\beta t}{D^2}v_I,\\
\mathcal H_{E_IE_J}&=3\delta_{IJ}
+\frac{6\sigma\alpha}{D}(t\delta_{IJ}-\alpha B_IB_J)
+\frac{12\sigma\alpha^2}{D^2}v_Iv_J.
\end{aligned}\tag{3}
\]

Consequently, with `K0=3I+(6σα/D)(tI−α BBᵀ)`,

\[
\boxed{\mathcal H=\operatorname{diag}(0,K_0)
+\frac{12\sigma}{D^2}
\binom{\beta t}{\alpha v}
\begin{pmatrix}\beta t&\alpha v^\top\end{pmatrix}.}\tag{4}
\]

**Proof:** The logarithmic derivative is `∂_A D=−2βt` and `∂_{E_I}D=−2αv_I`; furthermore `∂_{E_J}v_I=tδ_IJ−α B_IB_J`. Substitution into the Hessian of `−3σ log D` gives Eq. (3) and therefore Eq. (4). In the Schur complement with respect to `H_AA`, the complete rank-one `vvᵀ` term cancels:

\[
\boxed{\det\mathcal H=\mathcal H_{AA}\det K_0.}\tag{5}
\]

For exactly two flavors, use the directions parallel/perpendicular to the magnetic flavor vector. The eigenvalues of `K0` are

\[
k_\perp=3+\frac{6\sigma\alpha t}{D},\quad
k_\parallel=3+\frac{6\sigma\alpha w}{D}.
\]

Thus

\[
\boxed{\det\mathcal H=
\frac{12\sigma\beta^2t^2}{D^2}
\left(3+\frac{6\sigma\alpha t}{D}\right)
\left(3+\frac{6\sigma\alpha w}{D}\right).}\tag{6}
\]

### Completed-square certificate

For a curvature perturbation `δA` and gauge-electric perturbations `δE_I`, the quadratic form is exactly

\[
\begin{aligned}
\delta j^\top\mathcal H\delta j
&=\frac{12\sigma}{D^2}
\left(\beta t\,\delta A+\alpha\sum_Iv_I\delta E_I\right)^2\\
&\quad+3\sum_I(\delta E_I)^2
+\frac{6\sigma\alpha}{D}
\left[w\sum_I(\delta E_I)^2
+\alpha\left(b\sum_I(\delta E_I)^2
-\left(\sum_I B_I\delta E_I\right)^2\right)\right].
\end{aligned}\tag{7}
\]

The final bracket is a nonnegative flavor-plane Gram determinant by Cauchy–Schwarz. With `σ,α,β>0`, `D,t,w>0`, Eq. (7) is strictly positive for every nonzero `(δA,δE)`. At `σ=0` the curvature row vanishes and the gauge Hessian reduces to `3I`; Eq. (5) then gives zero for the full determinant. This *positive homogeneous jet* is **not** a positive Hamiltonian theorem: any nondegenerate metric acceleration can introduce a higher-derivative/Ostrogradsky mode unless removed by the complete G-field/metric constraint structure.

**Independent checks:** The optional `derive_mixed_principal_sympy.py` recomputes all nine two-flavor Hessian entries directly from Eq. (2). `tests/test_toe11_mixed_principal.py` checks Eq. (5) by an independent rational matrix determinant on random two- and three-flavor inputs, verifies Eq. (7), and differentiates the logarithmic action numerically without reusing the analytic Hessian.

## T2. Six-dimensional curvature–field-strength principal coupling

Let `F_κ` denote every color/flavor 6-vector and `S` the above bivector signature. With `R_(2)` the mixed Riemann pair operator (the FLRW background has electric diagonal `2A` and magnetic diagonal `2B`), the declared full 2-form block is

\[
\Theta_6=I_6+\alpha\Big(\sum_\kappa F_\kappa F_\kappa^\top\Big)S
-\beta\mathcal R_{(2)}.
\]

For an independent curvature perturbation `r` and matter-field-strength perturbations `f_κ`, define

\[
P_R=-\beta r,\quad
P_F=\alpha\sum_\kappa(f_\kappa F_\kappa^\top+F_\kappa f_\kappa^\top)S,
\quad P_{FF}=2\alpha\sum_\kappa f_\kappa f_\kappa^\top S.
\]

Writing `J=Θ6⁻¹`, the second variation of the declared action satisfies

\[
\boxed{K_{RR}=\sigma\operatorname{tr}(JP_RJP_R),\quad
K_{RF}=\sigma\operatorname{tr}(JP_RJP_F),\quad
K_{FF}=K_{\rm YM}+\sigma\operatorname{tr}(JP_FJP_F-JP_{FF}).}\tag{8}
\]

Here `K_YM=−Σ_κ f_κᵀSf_κ` is the exact minimal Yang–Mills field-strength Hessian. The trace follows from `d² log det Θ = tr(J d²Θ−J dΘ J dΘ)`. **This is the missing third-derivative mixed response in the declared 2-form theory.** The 6×6 implementation independently reduces Eq. (8) to *every component* of the homogeneous two-flavor Hessian (3), while a direct finite-difference of the full six-dimensional determinant checks the mixed formula.

A linearized metric plane wave `h` and gauge-field perturbation `a_μ` with formal wave covector `ξ` supply `r~ξ² h` via the Riemann principal symbol and `f~ξ∧a` via the gauge field-strength symbol. The program reconstructs `R_{ab cd}` with pair-exchange and first-Bianchi checks. Its explicit tests confirm that pure metric-gauge perturbations have `r=0` and ordinary Yang–Mills pure gauges have `f=0`. The resulting symbol has leading derivative orders `(4,3,2)` in its `(metric-metric, metric-gauge, gauge-gauge)` blocks. Overall Fourier factors of `i` and a physical gauge-fixing reduction have not been imposed.

## T3. One restricted TT/gauge-tensor wave projection

Choose a local frozen orthonormal frame, `ξ=(ω,0,0,p)`, a single metric TT polarization `h_xx=−h_yy`, and one SU(2) gauge tensor polarization `a_x^(flavor1,color1)=−a_y^(flavor1,color2)`. In this **two-dimensional subspace of perturbations**, the exact rational computation produces

\[
P(\omega,p)=\begin{pmatrix}
P_{hh}^{(4)}(\omega,p)&P_{ha}^{(3)}(\omega,p)\\
P_{ha}^{(3)}(\omega,p)&P_{aa}^{(2)}(\omega,p)
\end{pmatrix},
\]

with superscripts indicating polynomial degree in formal `ξ`. For the chosen isotropic backgrounds, the 2-form-only polynomial has the factorization

\[
\boxed{\det P(\omega,p)=
\bigl(\omega^2-v_g^2p^2\bigr)^2
\bigl(C_1\omega^2+C_0p^2\bigr)\,\mathcal C,\quad
v_g^2=\frac{s}{t}.}\tag{9}
\]

`mathcan.toe11.projected_wave.v1` records exact rational coefficients. In the strict-real TOE-10 reference background with `E=(2,1001/1000)`, `B=(1,0)`, `A=2/5`, `Bcurv=1`, `α=3/500`, `β=1/100`, `σ=1/100`, the double root is

\[
v_g^2=\frac{480993997}{493000000},
\]

and the remaining linear root is

\[
v_{\rm rem}^2=\frac{2812732928347778628181199}{2812735172899996567572050}>0.
\]

Direct six-dimensional evaluations at seven distinct formal frequencies reconstruct the degree-6 determinant; an independent polynomial-division check verifies that the `s/t` root has multiplicity at least two. Twenty rational background trials independently passed the same factor test. **Root reality in this isolated 2-form plus YM polarization is a kinematic necessary check, with a repeated root and no established bounded symmetrizer.** The omitted source sectors, auxiliary G-field, gauge-fixing, constraints, all other gauge polarizations, curvature-waveform principal terms, and background field equations may change the full determinant. These results cannot establish a healthy gravitational-wave cone or rescue Pereira's obstruction.

## Spectral versus kinetic gates

On the TOE-10 neighboring backgrounds with `E=(2, 1±1/1000)`, `B=(1,0)` and the other above parameters, the semisimple positive-real Krein gate holds on one side and fails on the other. Eq. (7) gives a **strictly positive homogeneous jet Hessian on both sides**. At the defective boundary, the jet Hessian stays invertible. These are genuinely different diagnostics. In particular, the existence of a real logarithm of the determinant of the 2-form operator does not guarantee the real individual eigenvalue condition of the underlying GfE proposal.

## Reproduce and next physics gates

```sh
python -m unittest tests.test_toe11_mixed_principal tests.test_toe11_operator_principal tests.test_toe11_wave_principal -v
python -m research.toe.mixed_principal
python -m research.toe.wave_principal
python research/toe/derive_mixed_principal_sympy.py  # optional SymPy
python -m unittest discover -s tests -q
lake build MathCan
lake env lean MathCan/TOEMixedPrincipal.lean
```

Next: construct the **full** 4D GfE 0/1/2-form plus independent G-field variation, metric and SU(2) gauge constraints, and a covariant principal pencil `P(ξ)` for every physical polarization. Prove a constant-rank gauge reduction and find a frequency-uniform symmetrizer or a concrete ill-posedness counterexample. Repeat with a physical Einstein/ΛGfE background instead of a frozen off-shell FLRW trial state, then assess finite-frequency EFT cutoff conditions. These are explicit unresolved obligations.
