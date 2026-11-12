# TOE-16: rank-three dynamical isotropy gate in GfE matter

**November 12, 2026.** A two-multiplet background can satisfy the exact curvature cone matching condition from Pereira's GfE study while its *fundamental one-form fluctuations* carry an anisotropic source kinetic Hessian. TOE-16 identifies the independent Gram matrix responsible, derives its exact trace-log variation, and constructs a three-multiplet candidate with a rotationally equivariant derivative channel.

## Models, source pins, and scope

- Ginestra Bianconi, [*Gravity from entropy*, Phys. Rev. D 111, 066001 (2025)](https://doi.org/10.1103/PhysRevD.111.066001), using the published March 2026 correction where applicable. The source fields are a Dirac–Kähler-like sum of 0-, 1-, and 2-forms; the matter response has components of \(D\Phi=d\Phi+\delta_D\Phi\) and the potential factor \(m^2+\xi R\).
- David S. Pereira, [*Gravitational Waves and Matter Constraints in Gravity from Entropy*, arXiv:2609.03082 (2026)](https://arxiv.org/abs/2609.03082), especially source Eqs. (18), (34), (38)–(43), and the explicit warning following Eq. (38) that full principal isotropy and new matter helicity-two combinations remain to be checked.
- [TOE-15](TOE15_HELICITY_MULTIPLET_CONSTRAINTS.md) pins a **pointwise** two-multiplet response \(M_B=2I_3\) and exact local normal-coordinate Dirac–Kähler first jets. Its jets are neither on-shell nor demonstrated to extend to a globally isotropic FLRW configuration.

This module is **a source-structured, exact-rational sub-Hessian** of the two-form trace-log action, on a frozen local background. It does not contain all metric-dependent Hodge variations, 0/1-form kinetic terms, variation of the curvature-dependent potential \(\xi R\), auxiliary G-field constraints, or the matter equations of motion. The claims concern a specified static transverse-curl subchannel; the full physical Cauchy problem remains open.

## TOE-16/T1. The response Gram and the derivative Gram are different objects

For \(N\) multiplets with background magnetic two-form vectors \(u_i=(D\Phi_i)_{B}\) and \(v_i=(\Phi_i)_{B}\), define

\[
U=\sum_i u_i u_i^\top,\qquad V=\sum_i v_i v_i^\top,\qquad
M_B=U+\lambda V,\quad\lambda=m^2+\xi R>0.
\]

With the positive isotropic branch \(M_B=m_B I_3\), the mixed magnetic curvature response is

\[
\Theta_B = (1-2\beta B_c+\alpha m_B)I_3
=\theta_B I_3,\qquad W_B=\theta_B^{-1} I_3.
\]

The TOE-15 construction has

\[
u_1=u_2=e_z,\quad v_1=e_x,\quad v_2=e_y,\quad\lambda=2,
\]
\[
\boxed{M_B=2I_3,\qquad U=2e_ze_z^\top,\qquad \operatorname{rank}(U)=1.}
\]

Its matched \(\theta_B=\theta_E=124/125\) remains exact. The equality of total response matrices does not imply isotropy of the derivative-resolved source. The first variation of the source operator depends on the individual \(u_i\).

## TOE-16/T2. The exact fundamental one-form curl Hessian

Choose metric perturbations zero and keep 0- and 2-form field perturbations fixed. In a local orthonormal frame take an individual transverse, static one-form perturbation \(\delta\omega_i\), with magnetic curl \(a_i=(d\,\delta\omega_i)_B\). This makes the 0-form coderivative perturbation vanish and isolates the two-form kinetic response. At fixed \(\lambda\),

\[
D_M=\delta M_B=\sum_i(u_i a_i^\top+a_i u_i^\top),
\quad
Q_M=\delta^2M_B=2\sum_i a_i a_i^\top.
\]

The second derivative of \(-\operatorname{tr}\log\Theta_B\) is

\[
\boxed{
H(a_1,\dots,a_N)=\alpha^2 W_B^2\operatorname{tr}(D_M^2)
-2\alpha W_B\sum_i |a_i|^2.
}\tag{T2}
\]

This equation includes the \(-\operatorname{tr}(W\delta^2\Theta)\) term. It is important: keeping only the first trace term would give a wrong kinetic Hessian.

With one flavor \(i\) varied,

\[
H_i(a)=2\alpha^2 W_B^2\bigl(
|u_i|^2|a|^2+(u_i\cdot a)^2\bigr)-2\alpha W_B|a|^2.
\]

For TOE-15's \(u_1=e_z\), the exact reference values are

\[
H_\perp=-\frac{1479}{123008},\quad
H_\parallel=-\frac{735}{61504},
\quad
\boxed{H_\parallel-H_\perp=\frac9{123008}>0.}
\]

This establishes a small, finite anisotropy in the normalized **matter-derivative subblock** even at exact curvature cone matching.

An *independent* oracle forms the full 3-by-3 response matrix \(\Theta_B(t)\) with \(u_i\mapsto u_i+t a_i\), interpolates the exact degree-at-most-six polynomial \(\det\Theta_B(t)\) from seven rational nodes, and computes

\[
-\left.\frac{d^2}{dt^2}\log\det\Theta_B(t)\right|_{t=0}
=\frac{D_1^2}{D_0^2}-\frac{2D_2}{D_0},
\]

where \(D_j\) are the ascending determinant coefficients. This is checked against Eq. (T2), without using its trace formula to calculate the answer.

## TOE-16/T3. A conditional two-multiplet principal-isotropy obstruction

Sum the diagonal flavor Hessians over \(i\), with a shared magnetic variation vector \(a\). This forms a spatial quadratic tensor invariant under an orthogonal rotation of the flavor basis:

\[
\boxed{
T=2\alpha^2W_B^2\bigl[(\operatorname{tr}U)I_3+U\bigr]
-2N\alpha W_B I_3.
}\tag{T3}
\]

When \(\alpha W_B\ne0\), SO(3) isotropy of this derivative-channel tensor requires \(U=cI_3\). With \(N=2\), \(\operatorname{rank}U\le2\), so any isotropic \(U\) is zero. Since \(U\) is a sum of real positive-semidefinite rank-one matrices, \(U=0\) forces both \(u_i=0\). Then \(M_B=\lambda V\) has rank at most two. This contradicts the nonzero isotropic rank-three response \(M_B=m_B I_3\).

**Conditional rank gate:** with two independent foundational multiplets, \(\lambda>0\), a nonzero isotropic magnetic response, positive scalar \(W_B\), and the source curl sub-Hessian (T2), the flavor-traced matter derivative channel cannot be rotationally isotropic. The necessary rank count for isotropy of **both** the background magnetic response and this independent curl channel becomes \(N\ge3\).

This is a necessary gate on a **particular principal source subblock**. Additional dynamical cancellations, gauge constraint quotients, and the full source-defined 0/1-form tensor analysis require explicit derivation before translating it into a theorem about physical gravitational propagation.

For the explicit two-multiplet witness, \(T_{zz}-T_{xx}=4(\alpha W_B)^2=9/61504\).

## TOE-16/T4. Direct metric–one-form mixing under a change of wave direction

The two-form mixed trace-log Hessian includes a highest-derivative cross pairing

\[
H_{h,a}=-\alpha\beta W_B^2
\operatorname{tr}\!\bigl((\delta \mathcal R_{(2)})_B\,D_M\bigr)
\]

for one curvature TT perturbation \(h\) and one independent one-form curl \(a\), at fixed \(\lambda\) and frozen response. The existing independently audited TOE-11 Riemann-pair operator provides \((\delta\mathcal R_{(2)})_B\). At equal \(|\mathbf p|=1\), with the same one-form perturbation \(a_x=1\), choose the transverse traceless polarizations

\[
\begin{array}{ll}
\mathbf p=e_z:& h_{xx}=1,\ h_{yy}=-1,\quad H_{h,a}=0,\\
\mathbf p=e_y:& h_{xx}=1,\ h_{zz}=-1,\quad
\boxed{H_{h,a}=-15/123008}.
\end{array}
\]

The exact operator uses \(\delta\mathcal R_{(2)}\) and \(d\,\delta\omega\); it is invariant under adding a longitudinal pure-gauge one-form amplitude. This direction-sensitive cross pairing is another diagnostic of how a background with \(U\propto e_z e_z^\top\) can distinguish wave directions, even though \(M_B=2I_3\).

## TOE-16/T5. Three-multiplet flavor-locked candidate

A pointwise three-multiplet replacement can retain the same E/B response while making the derivative Gram isotropic. Choose

\[
u_i=e_i,\quad v_i=e_i,\quad \lambda=1,\qquad i=x,y,z.
\]

Then

\[
\boxed{U=V=I_3,\quad M_B=2I_3,\quad
\theta_B=\theta_E=124/125.}
\]

It also admits smooth local Dirac–Kähler first jets: take one-forms whose exterior derivatives are the three spatial area forms and constant background two-forms with the same values. Let the three multiplets transform in the vector representation of an orthogonal internal flavor symmetry. The joint spatial/flavor rotation preserves the locked background \(U=V=I_3\).

The exact curl Hessian is invariant under the rational orthogonal rotations
\(A\mapsto R A R^\top\) of the matrix of multiplet one-form variations. The oracle tests a nontrivial \(3/5,4/5\) plane rotation and a cyclic spatial permutation. The flavor-traced tensor (T3) is isotropic.

**This is a candidate that passes the new necessary derivative-isotropy gate**, not an established dynamical escape. Its covariant FLRW continuation, total form-sector kinetic Hessian, background stress tensor, \(\xi R\) mixing, full linearized metric/G-field equations and constraint-reduced characteristic polynomial still have to be derived.

## Reproduce and next exact tasks

- [Source module](multiplet_kinetic.py) implements the rational Hessian, independent determinant interpolation, flavor trace, rank/isotropy checks, static curvature–one-form mixing and locked-triplet rotations.
- [Tests](../../tests/test_toe16_multiplet_kinetic.py) compare exact determinant and trace results at seeded rational variations; validate the exact orientation-dependent mixing and a pure-gauge shift; prove synthetic 2- vs 3-multiplet gates and preserve all physical uncertainty flags.
- MathCan/TOEMultipletKinetics.lean proves the structural integer anisotropy and conditional rank inequalities. The exact finite-matrix statements are covered by executable rational tests; the Lean module does not formalize arbitrary 3-by-3 real matrix rank.

    python -m unittest tests.test_toe16_multiplet_kinetic -v
    python -m research.toe.multiplet_kinetic
    python -m unittest discover -s tests -v
    lake build MathCan
    lake env lean MathCan/TOEMultipletKinetics.lean

**Next source-based gate, TOE-17:** construct the actual three-triplet Dirac–Kähler first-order action in a locally isotropic field frame; include variations of \((D\Phi)_{(0)}\), \((D\Phi)_{(1)}\), \((D\Phi)_{(2)}\), \(\lambda=m^2+\xi R\), the metric-dependent Hodge adjoints, and the auxiliary G-field equations. Solve the homogeneous background constraints and compare the full physical tensor determinant with both the vacuum and the frozen multiplet sources.
