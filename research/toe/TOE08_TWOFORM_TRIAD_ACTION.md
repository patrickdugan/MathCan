# TOE-08: a covariant two-form trial action, isotropic response rank, and tensor-cone dynamics

**11 November 2026. Status:** a self-contained **trial** multi-field action, exact flat-FLRW background stress and Euler equations, algebraic curvature response, a rank obstruction for one/two *simple 2-forms*, exact rational tests and a small spectator evolution. A full Bianconi dressed stress tensor, complete Dirac–Kähler multiplet, and coupled four-dimensional metric–matter characteristic operator remain open. In particular, the action here is **proposed for MathCan**, not extracted from Bianconi or claimed to be equivalent to her source action.

## Source boundary

- Bianconi, [*Λ-Gravity from Entropy*](https://arxiv.org/abs/2610.34496), uses a form-space induced metric with 0-, 1-, and 2-form sectors, a dressed stress-energy tensor, an algebraic G-field and a constant volume multiplier. Her curvature 2-form sector involves the Riemann operator.
- Pereira, [*Gravitational Waves and Matter Constraints in Gravity from Entropy*](https://arxiv.org/abs/2609.03082), shows a strict-principal tensor-cone obstruction in vacuum and several restricted matter sectors. A sufficiently rich **two full Dirac–Kähler multiplet** extension is a candidate beyond his one-multiplet rank theorem. His paper does not assert that two simple antisymmetric 2-form potentials suffice.
- [TOE-07](TOE07_MULTIPLET_CONE_AND_COVARIANT_COMPLETION.md) derived the **conditional** isotropic matching requirement `alpha (mE-mB)=2 beta (Hdot-K/a²)` and demonstrated a rank obstruction when each species contributes one spatial electric/magnetic vector.

All calculations below use a spatially flat background, signature `(-+++)`, three internally indexed real antisymmetric potentials, and positive scale factor/lapse. The pointwise cone-matching ansatz introduced in Section 5 is an additional constitutive assumption, distinct from the curvature coupling in the action.

## 1. Microscopic field action

For `a=1,2,3` let `B^(a)_(mu nu)=-B^(a)_(nu mu)` and `H^(a)_(mu nu rho)=3 partial_[mu B^(a)_(nu rho)]`. Define

\[
S_B=\sum_{a=1}^{3}\int d^4x\sqrt{-g}\left[
-\frac1{12}H^{(a)}_{\mu\nu\rho}H^{(a)\mu\nu\rho}
-\frac{m^2}{4}B^{(a)}_{\mu\nu}B^{(a)\mu\nu}
+\frac{\lambda}{4}R_{\mu\nu\rho\sigma}
 B^{(a)\mu\nu}B^{(a)\rho\sigma}\right].\tag{1}
\]

Here `m²≥0`, while `lambda` is a separately registered nonminimal coupling. A common internal `O(3)` transformation rotates the three potentials. For background isotropy choose the diagonal combination of spatial and internal rotations, and set

\[
 B^{(a)}_{0i}=0,\qquad B^{(a)}_{ij}=a(t)^2 b(t)\epsilon_{ija},
 \qquad q=\dot b+2Hb,\quad H=\frac{\dot a}{Na}.\tag{2}
\]

The `q` here denotes the **three-form field strength**, unrelated to the Hubble derivative. The physical 2-form amplitude is `b`; the coordinate potential `w=a²b` must be held fixed when varying the metric. This distinction is important for the correct stress tensor.

### Curvature derivative and isotropic magnetic tensor

For the independent pair-curvature operator at fixed metric and fields, (1) has response

\[
\boxed{\mathcal P^{\mu\nu\rho\sigma}
=\frac{\partial\mathcal L_{\rm int}}{\partial R_{\mu\nu\rho\sigma}}
=\frac{\lambda}{4}\sum_a B^{(a)\mu\nu}B^{(a)\rho\sigma}.}\tag{3}
\]

On the pure-magnetic triad, in an orthonormal frame,

\[
 \mathcal P^{ijkl}=\frac{\lambda b^2}{4}
 (\delta^{ik}\delta^{jl}-\delta^{il}\delta^{jk}),
\quad \mathcal P^{0i\rho\sigma}=0.\tag{4}
\]

It has antisymmetry in each pair, pair-exchange symmetry, and the algebraic first Bianchi identity. The code checks those symmetries using exact fractions. Flat-FLRW curvature has `R_ijkl=H²(delta_ik delta_jl-delta_il delta_jk)` in the orthonormal frame, yielding

\[
\mathcal P^{\mu\nu\rho\sigma}R_{\mu\nu\rho\sigma}
=3\lambda H^2b^2.\tag{5}
\]

An arbitrary superposition of simple 2-forms need not satisfy the first Bianchi identity before the algebraic-Riemann projection; (4) does. This response is *to the explicit RBB term*. It is **not** a calculation of Bianconi's full dressed curvature response, which also includes the logarithmic G-field response across the other form sectors.

## 2. The homogeneous action and both variations

Work with the independent coordinate field `w=B^(3)_12=a²b`, the scale factor `a`, and the lapse `N`. After inserting the three-field triad in the four-dimensional action and setting spatial curvature to zero,

\[
\boxed{
 L_{\rm mini}=\frac{3\dot w^2}{2Na}
 -\frac{3Nm^2w^2}{2a}
 +\frac{3\lambda\dot a^2w^2}{Na^3}.}\tag{6}
\]

This is a symmetry-reduced matter action, with no independent gravitational action yet added. The contraction of the nonminimal term is Eq.(5). The optional SymPy script independently differentiates (6) at fixed `w`.

**T1 (2-form Euler equation).** Variation of `w` followed by `N=1` gives

\[
 \boxed{\dot q+Hq+(m^2-2\lambda H^2)b=0,\qquad
 \dot b=q-2Hb.}\tag{7}
\]

A homogeneous electric ansatz `B^(a)_{0i}=a e delta_ia` produces no `H=dB` kinetic term. Its algebraic equation is

\[
(m^2-2\lambda(\dot H+H^2))e=0.\tag{8}
\]

For generic expanding backgrounds away from the effective-mass zero surface, `e=0`. Turning on an electric amplitude in this simple trial action therefore requires a special algebraic branch or a different field theory.

**T2 (full background stress of action (1)).** Using the lapse and spatial scale-factor variations of (6) at fixed `w` gives

\[
\boxed{\rho_B=\frac32(q^2+m^2b^2)+3\lambda H^2b^2,}\tag{9}
\]

\[
\boxed{p_B=\frac12(-q^2+m^2b^2)
+3\lambda H^2b^2-2\lambda(\dot H+H^2)b^2
-4\lambda Hbq.}\tag{10}
\]

This computes the **entire homogeneous isotropic stress** of the declared action, including its curvature coupling. Eq.(10) contains the derivative terms from varying `RBB`; keeping `b` fixed during metric variation would miss them. With `lambda=0`, it reduces to `rho=3(q²+m²b²)/2` and `p=(-q²+m²b²)/2`. The off-FLRW components of the full covariant stress variation are a separate, still-open calculation.

**T3 (matter continuity).** Differentiate (9), substitute Eq.(7), and obtain

\[
\boxed{\dot\rho_B+3H(\rho_B+p_B)=0.}\tag{11}
\]

This is an identity of the concrete matter theory on an externally specified FLRW metric, verified exactly for 1,000 random rational states. It does **not** assert that Bianconi's separately defined dressed stress tensor conserves without its G-field terms, nor does it establish a solution of the full coupled Einstein/GfE equations.

## 3. Response rank and an electric/magnetic cross term

Represent a 2-form in the six basis pairs `(01,02,03,23,31,12)`. An aligned simple field has components `B^(a)=(e e_a, b e_a)`, so summing the outer-product Gram over three internal orientations produces

\[
 M_{(2)}=\begin{pmatrix}e^2I_3&ebI_3\\ebI_3&b^2I_3\end{pmatrix}.\tag{12}
\]

**T4 (rank/isotropy).** Eq.(12) has rank three when `(e,b) != (0,0)`; two independent simple 2-forms supply a matrix of rank at most two. A strictly positive rotationally invariant **magnetic** block `b² I_3` therefore needs at least three independent simple orientations under this outer-product construction. The magnetic triad realizes it exactly.

The off-diagonal `eb I_3` in Eq.(12) also matters. A triad with both electric and magnetic amplitudes has an isotropic **mixed E/B block**, while the simple diagonal `W_E,W_B` source ansatz of TOE-07 assumes this block vanishes. To retain the diagonal model one must take `eb=0` or arrange additional field content whose cross contributions cancel.

**Interpretation:** Pereira's possible *two Dirac–Kähler multiplets* each have richer form-space structure than a single simple 2-form. Our lower bound of three applies only to this narrower Gram construction. It is a constraint on one possible model architecture.

## 4. Matching the TT cone requires a time-dependent field solution

Add a registered *constitutive* map from the physical 2-form amplitudes to the induced form-space tensor block,

\[
 m_E=0,\qquad m_B=\chi b^2,\quad \chi>0,\tag{13}
\]

with the TOE-07 diagonal definition
`theta_E=1-2 beta (Hdot+H²)`, `theta_B=1+alpha m_B-2 beta H²`. This postulate is not implied just by the explicit curvature coupling `lambda RBB` in (1); reproducing it within the actual ΛGfE induced metric requires an additional source-specific derivation. Under Eq.(13), equality `theta_E=theta_B` gives

\[
\boxed{b^2=-\frac{2\beta\dot H}{\alpha\chi}.}\tag{14}
\]

For `alpha,beta,chi>0` and nonzero `b`, it requires `Hdot<0` on a flat background. It only matches the **isolated** TT tensor blocks at the chosen instant. Eq.(7) must simultaneously hold.

**T5 (dynamical compatibility).** On the branch `b²=-c Hdot`, with positive constant `c`, set `J=Hddot` and `K=H'''`. Substituting Eq.(14) into Eq.(7) yields the independent necessary condition

\[
\boxed{\frac{K}{2\dot H}-\frac{J^2}{4\dot H^2}
+2\dot H+\frac{3HJ}{2\dot H}
+2H^2+m^2-2\lambda H^2=0.}\tag{15}
\]

The exact-rational implementation verifies the identity by independently substituting a power-law scale factor, including positive curvature coupling. It fails closed at `Hdot=0`, where the branch derivation divides by `Hdot`.

For `a(t) proportional to t^p` with `p>0`, this becomes

\[
\boxed{(p-2)(2p-1)-2\lambda p^2 +m^2 t^2=0.}\tag{16}
\]

For constant `m²>0`, (16) cannot hold for **every** time on a nontrivial interval; it differs at `t=1` and `t=2` by `3m²`. For `lambda=m=0`, the admissible exponents are `p=1/2` and `p=2`. The first has `q=0`, so `H=dB=0`: locally it is a pure-gauge configuration in the massless gauge-invariant kinetic theory, although a `B²` constitutive law would change under a gauge transformation. The `p=2` solution has `q != 0` and is a **spectator** field on a prescribed background; the energy scales as `t^-4`, whereas the Friedmann curvature scales as `t^-2`. A self-consistent backreacted branch needs further equations.

**Numerical gate:** for `p=2`, `beta=.01`, `alpha=.04`, `chi=1`, `b(1)=1`, `q(1)=3`, the massless `lambda=0` analytic solution has `b(2)=0.5`, `q(2)=0.75`. The RK4 solver agrees within `10^-8`. Raising `m²` to `0.1`, while keeping the initial data, gives `b(2)≈0.48799678446` and `b(2)^2-0.25≈-0.01185913836`; step doubling agrees to eight decimal places.

## 5. What is known about the coupled characteristic matrix

This particular matter theory has a calculable homogeneous kinetic Hessian. Add only the Einstein–Hilbert minisuperspace kinetic contribution `-3 M_P² a dot(a)²/N` for comparison. In the variables `(a,w)`, the velocity Hessian is

\[
 K_{\rm homogeneous}=\begin{pmatrix}
6\lambda w^2/(Na^3)-6M_P^2a/N&0\\
0&3/(Na)
\end{pmatrix}.\tag{17}
\]

The calculation is exact and uses independent coordinate fields. This **is not** the four-dimensional gravitational-wave/matter characteristic matrix: the lapse constraint, form-gauge redundancy, spatial wavevectors and higher-curvature metric derivatives are omitted by homogeneous reduction. In particular, the negative Einstein conformal minisuperspace direction is not itself a propagating graviton ghost.

For a general coupled principal block, the relevant step is the **Schur complement**

\[
 \mathscr K(k)=\begin{pmatrix}Q_{TT}(k)&C(k)\\
 C(k)^\top&M(k)\end{pmatrix},\qquad
 \det\mathscr K=\det M\,\det(Q_{TT}-CM^{-1}C^\top).\tag{18}
\]

The equality `theta_E=theta_B` only controls the isolated tensor block `Q_TT`; it cannot certify the coupled roots until the actual mixing block `C`, matter principal block `M`, constraints, and strong-hyperbolicity symmetrizer are derived from the complete action. The generic scalar 2-by-2 Schur identity has 500 exact rational checks. No source-specific `C(k)` is assumed or claimed here.

## 6. Relation to the source and remaining work

The paper has now instantiated a *concrete* three-species antisymmetric action with exact isotropic response, a matter stress/continuity calculation, a derived candidate cone-matching law, and an overdetermination test on power-law expansion. These results are independent MathCan mathematics. They do not supply Bianconi's functional metric variation of the **full** dressed matter term, which mixes form-space sectors; the 2-form matter tensor of the underlying Dirac–Kähler theory may involve derivatives of the fields instead of the direct-potential Gram (12).

What remains for full TOE-08 completion is to (i) derive `M_(2)` from an actual set of complete Dirac–Kähler multiplets, (ii) vary the complete logarithmic induced metric in four dimensions, (iii) solve its modified matter equations with backreaction, (iv) derive the coupled metric–matter principal matrix including constraint and gauge sectors, and (v) check real characteristics, eigenvector completeness and energy sign over a declared EFT frequency window. Distinguish all of these from a synthetic background fit.

### Reproduction

```sh
python -m unittest tests.test_toe08_twoform -v
python -m research.toe.twoform_triad
python research/toe/derive_twoform_sympy.py  # optional sympy
lake build MathCan
lake env lean MathCan/TOETwoFormTriad.lean
```

The standard-library Python module uses `Fraction` for every algebraic certificate and separately labels its RK4 spectator calculation. Its tests include exact rank checks, curvature response symmetry and contraction, continuity for 1,000 rational states, power-law compatibility, and integer-growth constraints. The new Lean module proves ten finite structural statements. Its proofs do not certify the four-dimensional variational calculus.

## 7. Two independent magnetic triad multiplets: a dynamical flavor-area obstruction

To give the two-multiplet question an explicit trial action, take **two copies** of the O(3)-indexed action (1), indexed by `r=1,2`, with their own `m_r²,lambda_r` and physical magnetic amplitudes `b_r`. There are six antisymmetric tensor potentials in total. A multiplet here means a magnetic SO(3) *triad*; this construction is **not** a pair of complete Dirac–Kähler multiplets as in Pereira's rank discussion. All claims about the source GfE response continue to require the independent constitutive hypothesis below.

The combined homogeneous action is `L_mini=sum_r L_mini[r]`. Each triad obeys

\[
 \dot b_r=v_r-2Hb_r,\qquad
 \dot v_r=-Hv_r-M_rb_r,\qquad M_r=m_r^2-2\lambda_rH^2.
 \tag{19}
\]

The stress tensor is the sum of the two complete homogeneous stress tensors (9)--(10). With independent Riemann couplings, the curvature response becomes

\[
 \mathcal P^{ijkl}=\frac{\lambda_1b_1^2+\lambda_2b_2^2}{4}
 (\delta^{ik}\delta^{jl}-\delta^{il}\delta^{jk}).\tag{20}
\]

Let `S=b1²+b2²`, `Q=b1*v1+b2*v2`, and the **flavor area**
`W=b1*v2-b2*v1`. All are directly calculated from the field variables.

**TOE-08/T6 (exact flavor-area transport).** The two field equations imply

\[
\boxed{\dot S=2Q-4HS,\qquad
\dot W=-3HW+(M_1-M_2)b_1b_2.}\tag{21}
\]

For identical couplings, `M_1=M_2`, the comoving flavor area `a³W` is conserved. This is a conserved SO(2) charge in the internal two-triad plane. For different couplings, the last term describes explicit flavor torque.

The ordinary two-dimensional Lagrange identity gives

\[
\boxed{S(v_1^2+v_2^2)=Q^2+W^2.}\tag{22}
\]

**TOE-08/T7 (radial compatibility identity).** Differentiate `S` using (19), substitute (22), and obtain for all `S>0`:

\[
\boxed{
 \ddot S+7H\dot S+(12H^2+4\dot H)S
 +2\sum_{r=1}^2M_rb_r^2
 =\frac{(\dot S+4HS)^2+4W^2}{2S}.}\tag{23}
\]

Thus radial response evolution records an additional nonnegative contribution `2W²/S` from flavor rotation. For identical multiplets, the response obeys the same scalar radial equation as a single triad only on `W=0` trajectories. The Python oracle checks the exact identity at 500 reproducible rational states with independent masses and couplings.

Under the **separate, provisional GfE constitutive map** `m_E=0`, `m_B=chi*S`, the isolated TT matching condition becomes

\[
\boxed{\alpha\chi S=-2\beta\dot H.}\tag{24}
\]

Equation (23) is an additional necessary condition for this equality to persist. Even exact matching at one time does not determine the later field orientation.

### Exact counterexample: rotation breaks sustained matching

Take a prescribed power-law geometry `a(t)=t²`, with `H=2/t`, `m_r=lambda_r=0`. An exact two-triad solution of (19) is

\[
 b_1=\frac1t,\quad v_1=\frac3{t^2},\qquad
 b_2=\frac{t^3-1}{6t^4},\quad v_2=\frac1{2t^2}.\tag{25}
\]

Choose `beta=1/100`, `alpha=1/25`, `chi=1`. At `t=1`, its total amplitude `S=1` exactly satisfies (24), and `dot(S)=-2` matches the target's first derivative. Its nonzero `W(1)=1/2` evolves as `W(t)=1/(2t^6)`. At `t=2`,

\[
S(2)=\frac14+\frac{49}{9216},\quad
W(2)=\frac1{128},\quad
S_{\mathrm{target}}(2)=\frac14.\tag{26}
\]

The positive mismatch `49/9216` is exact. The model's two-form equations are satisfied identically at every positive time, and the **background is prescribed** rather than backreacted. This supplies a concrete dynamically consistent matter-sector counterexample to the proposition that instantaneous `W_E=W_B` guarantees matching at later times.

### The homogeneous kinetic degeneracy locus

Including a comparison Einstein--Hilbert kinetic term `-3M_P² a dot(a)²/N`, the exact `(a,w1,w2)` velocity Hessian is diagonal, with

\[
 K_{aa}=\frac{6a}{N}\big(\lambda_1b_1^2+\lambda_2b_2^2-M_P^2\big),
 \qquad K_{w_rw_r}=\frac3{Na}.\tag{27}
\]

Consequently the **homogeneous** Hessian degenerates at
`lambda1*b1²+lambda2*b2²=M_P²`. This is a Cauchy-data diagnostic for the toy minisuperspace model; due to the gravitational constraint and the higher-derivative GfE sector, it is not a ghost criterion or a substitute for the complete coupled wave symbol. Numerical and rational checks explicitly label these limitations.

Reproduce the new branch with:

```sh
python -m unittest tests.test_toe08_two_multiplet -v
python -m unittest discover -s tests -v
lake build MathCan
```

**Next gates:** derive the actual Dirac--Kähler two-multiplet `M_(2)` construction with its indefinite form-space metric; examine how the nonminimal `RBB` coupling alters the GfE *joint* field equations and principal matrix; track the fate of the flavor-area charge in the coupled GfE action; and test the full constraint/gauge-fixed symmetrizer in a declared finite-frequency regime.
