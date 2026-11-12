# TOE-17: source three-multiplet tensor pencil and a returned Jordan chain

**12 November 2026.** Starting with TOE-16's flavor-locked three-multiplet Dirac–Kähler *local jet*, this module derives the full frequency- and momentum-dependent strict-principal sub-Hessian in the two transverse gravitational polarizations and their two transverse one-form matter spin-two partners. The underlying 6×6 bivector curvature and Gram variations are evaluated independently of a closed polynomial formula, along with the full 4×4 Ricci tensor principal. The tensor source has a repeated light cone with a defective root at the exact reference cone-matching point. Two explicitly bracketed nearby matter-response detunings instead have three distinct positive squared-frequency roots in the same restricted symbol.

## Source and the physical boundary

The starting field theory is the **foundational** GfE trace-log action, not the synthetic SU(2)² Yang–Mills action used in TOE-11/12:

\[
S_{\rm ent}=-\ell_P^{-4}\int d^4x\sqrt{-g}\,\operatorname{Tr}_{\Lambda^0\oplus\Lambda^1\oplus\Lambda^2}
\log\widetilde\Theta,\quad
\widetilde\Theta=I+\alpha\widetilde M\,\widetilde g^{-1}
-\beta\widetilde{\mathcal R}\,\widetilde g^{-1}.
\]

Here \(M_{(p)}=\sum_{i=1}^3(u_{i,p}u_{i,p}^\dagger+\lambda v_{i,p}v_{i,p}^\dagger)\), \(\lambda=m^2+\xi R\), \(u_{i,p}=(D\Phi_i)_{(p)}\), and \(v_{i,p}=(\Phi_i)_{(p)}\), with \(D=P_F(d+\delta_D)P_F\).

Primary references: G. Bianconi, [*Gravity from Entropy*](https://doi.org/10.1103/PhysRevD.111.066001) (2025; corrected conventions) and D. S. Pereira, [*Gravitational Waves and Matter Constraints in Gravity from Entropy*](https://arxiv.org/abs/2609.03082) (2026), especially Eqs. (4)–(7), (16)–(19), (34), (38)–(43). Pereira's source-normalized TT curvature polynomial is \(\beta^2[\frac12W_s^2(\omega^2-p^2)^2+2(W_E\omega^2-W_Bp^2)^2]\). The module reconstructs both terms directly from their form blocks.

**Scope:** frozen normal-frame local first jets; \(A=H^2+\dot H=2/5\), \(B=H^2=1\), \(K=0\), \(\alpha=3/500\), \(\beta=1/100\), \(\lambda=1\). At the event, the three multiplets have two-form values \(v_i=e_{B_i}\) and Dirac–Kähler two-form derivatives \(u_i=e_{B_i}\), giving \(U=V=I_3\) and \(M_B=2I_3\). The scalar and one-form background matter blocks vanish. Each transverse spin-two one-form fluctuation has zero coderivative at the linear principal level. This is an exact form-space *sub-Hessian*, not a background solution of the coupled matter/metric/G equations, and no full Cauchy constraint quotient is claimed.

## T1. A true 6D bivector-source second variation

The frozen inverse E/B response is

\[
W_{(2)}=\operatorname{diag}(W_E I_3,W_B I_3),\quad
W_E=\frac{1}{1-2\beta A},\quad
W_B=\frac{1}{1+\alpha(1+\lambda)-2\beta B}.
\]

The spatial 1-form Ricci response is \(W_s=[1-\beta(A+2B)]^{-1}\). Each real gravitational spin-two tensor has polarization normalization \(h_{ij}h^{ij}=2\). Along \(k=(\omega,0,0,p)\), define its metric curvature perturbation \(P_R=-\beta\delta\mathcal R_{(2)}\). For an independent matter spin-two one-form polarization with six-component curls \(f_i=d(\delta\omega_i)\), set

\[
P_M=\alpha\sum_i(u_i f_i^\top+f_i u_i^\top)S,\quad
P_{MM}=2\alpha\sum_i f_if_i^\top S,\quad
S=\mathrm{diag}(-I_3,+I_3).
\]

The exact source trace-log Hessian has

\[
H_{hh}^{(2)}=\operatorname{tr}(W_{(2)}P_RW_{(2)}P_R),\quad
H_{ha}^{(2)}=\operatorname{tr}(W_{(2)}P_RW_{(2)}P_M),
\]

\[
H_{aa}^{(2)}=\operatorname{tr}(W_{(2)}P_MW_{(2)}P_M)
-\operatorname{tr}(W_{(2)}P_{MM}).
\]

Add the independent 1-form Ricci contribution \(H_{hh}^{(1)}=\beta^2 W_s^2(\omega^2-p^2)^2/2\). For this transverse one-form matter spin-two subspace, \(D\Phi_{(0)}=\delta_D\omega=0\) at principal order and \(D\Phi_{(1)}\) has no fluctuating derivative from \(\delta\omega\) alone. The source \(\lambda(\Phi_i)_{(2)}(\Phi_i)_{(2)}^\dagger\) is held at its background value, and its \(\delta\lambda=\xi\delta R\) term has zero TT scalar curvature principal.

**Independent matrix oracle:** each variation is reconstructed from 6×6 independent-pair Riemann and 2-form Gram matrices; the metric vector part is separately evaluated from the full 4×4 Ricci tensor. The real 4×4 matrix in \((h_+,h_\times,a_+,a_\times)\) has the form

\[
P_4=\begin{pmatrix}
H_{hh}&0&H_{ha}&0\\
0&H_{hh}&0&H_{ha}\\
H_{ha}&0&H_{aa}&0\\
0&H_{ha}&0&H_{aa}
\end{pmatrix}.
\]

Write \(Q=W_E\omega^2-W_Bp^2\), \(\delta=\omega^2-p^2\). Independent symbolic contraction yields the closed entries

\[
\boxed{\begin{aligned}
H_{hh}&=\beta^2\left[\frac{W_s^2}{2}\delta^2+2Q^2\right],\\
H_{ha}&=4\alpha\beta W_Bp\,Q,\\
H_{aa}&=4\alpha\left[W_E(1-\alpha W_B)\omega^2+
W_B(2\alpha W_B-1)p^2\right].
\end{aligned}}
\]

The last line contains both the square of the linear first response and the negative second response \(-\mathrm{tr}(W P_{MM})\). No bare Yang–Mills \(F^2\) kinetic term appears in this foundational source calculation.

For real Fourier variables, the odd-total-derivative mixed term acquires a factor of \(i\), and the Hermitian Fourier quadratic form is related by the constant phase congruence \(U^\dagger P U\), \(U=\mathrm{diag}(-1,i)\). Its determinant and characteristic zeros are preserved; as in TOE-14, this observation alone does not fix lower derivative terms or a physical first-order evolution system.

## T2. Exact matched response and the source Jordan chain

At the pinned reference,

\[
W_E=W_B=\frac{125}{124},\quad W_s=\frac{125}{122}.
\]

With \(p=1\), the exact **one-helicity** rational polynomial matrix is

\[
\boxed{
P(\omega)=
\begin{pmatrix}
\frac{58525}{228856384}(\omega^2-1)^2&
\frac{15}{61504}(\omega^2-1)\\[2pt]
\frac{15}{61504}(\omega^2-1)&
\frac{3}{61504}(493\omega^2-490)
\end{pmatrix}.
}
\]

Its determinant is

\[
\boxed{
\det P(\omega)=\frac{75}{14075583041536}
(\omega^2-1)^2(1154113\omega^2-1158253).
}\tag{17.1}
\]

Thus the non-lightcone real squared-frequency root is \(x_* = 1158253/1154113\), while \(x=1\) is a repeated root of multiplicity exactly two. At \(\omega=1\),

\[
P(1)=\operatorname{diag}(0,9/61504),\qquad
\dim\ker P(1)=1.
\]

For a regular polynomial matrix, algebraic multiplicity two with geometric multiplicity one implies a length-two Jordan chain in a companion linearization. The explicit vectors are

\[
v_0=(1,0)^\top,\qquad
v_1=(0,-10/3)^\top,\qquad
P(1)v_0=0,\quad P(1)v_1+P'(1)v_0=0.
\]

The weighted temporal-leading matrix is regular because \(H_{hh}\) has a nonzero \(\omega^4\) coefficient and \(H_{aa}\) a nonzero \(\omega^2\) coefficient; the mixed \(H_{ha}\) has only \(\omega^2\) temporal dependence. The repeated lightcone therefore gives an exact nonsemisimple root of the **restricted frozen source tensor system**. The real 4×4 spin-two block comprises two equivalent copies.

The integer-scaled Lean module multiplies \(P\) by 228856384 to get \(58525(x-1)^2\), \(55815(x-1)\), and \(11163(493x-490)\); the integer determinant is

\[
(x-1)^2\,279075(1154113x-1158253).
\]

Lean verifies this exact factorization, the rank-one lightcone kernel implication and the integer-rescaled Jordan-chain equation.

## T2a. A parameter-independent matched-source Jordan theorem

The source root defect is structural within this prescribed three-triplet normal-frame tensor subblock. Let \(\alpha,\beta>0\), \(p\ne0\), and let \(W_E=W_B=W>0\), \(W_s>0\). The matched requirement can be solved on a family of local FLRW response values by

\[
\lambda=\frac{2\beta(B-A)}{\alpha}-1>0,\qquad
\theta_E=\theta_B>0.
\]

For either helicity, the exact polynomial reduces to

\[
P_{hh}=\beta^2 C(\omega^2-p^2)^2,\qquad
P_{ha}=4\alpha\beta W^2p(\omega^2-p^2),
\]

\[
P_{aa}=4\alpha W[(1-\alpha W)\omega^2+(2\alpha W-1)p^2],
\qquad C=W_s^2/2+2W^2.
\]

At \(\omega_0=\pm p\), the matter diagonal is \(4\alpha^2W^2p^2\ne0\), while the first row vanishes. The regular leading temporal matrix exists when \(0<\alpha W<1\). The doubled light-cone root has an exact generalized eigenvector pair

\[
\boxed{
v_0=(1,0)^\top,\qquad
v_1=\left(0,-\frac{2\beta\omega_0}{\alpha p}\right)^\top .
}
\]

The coefficient multiplying the double factor \((\omega^2-p^2)^2\), evaluated at the light cone, equals

\[
\boxed{4\alpha^2\beta^2W^2p^2\left(\frac{W_s^2}{2}-2W^2\right).}
\]

When \(W_s\ne2W\), the multiplicity is exactly two. At \(W_s=2W\), the cofactor also vanishes and the restricted characteristic has a higher collision multiplicity. These identities are independent of the reference numerical parameters. Tests check four sets of rational background coefficients and three nonzero spatial wavenumbers for each, verifying both signs \(\omega_0=\pm p\).

The theorem is conditional on this selected source-mode subspace and on the positive background response; it leaves the background equations and all other Dirac–Kähler field components to the complete GfE evolution problem.

## T3. Detuning produces three distinct real roots in the restricted pencil

Hold \(u_i=e_{B_i}\), \(v_i=e_{B_i}\) and vary \(\lambda=1+\varepsilon\). Then \(W_E=125/124\) is fixed, while

\[
W_B(\varepsilon)=\frac1{124/125+\alpha\varepsilon}.
\]

The exact determinant becomes a cubic \(d_\varepsilon(x)\) in \(x=\omega^2\). The Python oracle reconstructs its coefficients directly from the source-derived closed entries and computes its **exact rational discriminant**. At either registered detuning \(\varepsilon=\pm1/1000\), that discriminant is strictly positive. Each cubic has three roots in independently checked disjoint intervals of positive rational \(x\):

| \(\varepsilon\) | First root bracket | Second root bracket | Third root bracket |
|---|---|---|---|
| \(+1/1000\) | \((0.999987,0.999989)\) | \((0.999995,0.999997)\) | \((1.003587,1.003589)\) |
| \(-1/1000\) | \((1.000003,1.000005)\) | \((1.000011,1.000013)\) | \((1.003585,1.003588)\) |

These intervals are verified by exact sign changes using Fraction coefficients, which proves existence of three simple positive real roots for each registered background.

At infinitesimal detuning, write \(x=1+\kappa\varepsilon+O(\varepsilon^2)\). The double-root blow-up gives

\[
\frac{W_s^2}{2}\kappa^2
-2W^2(\kappa+\alpha W)^2=0,\qquad W=125/124.
\]

Its two distinct exact rational slopes are

\[
\boxed{
\kappa_{\rm steep}=-\frac{61}{4960},\qquad
\kappa_{\rm shallow}=-\frac{183}{45632}.
}
\]

The detuned **restricted** tensor pencil therefore has a real-spectrum neighborhood on each side of the matched point, including the two registered cases. Real roots of this frozen principal are an algebraic spectral test; no positive-definite symmetrizer for the full Dirac–Kähler system follows from them.

## T4. The full Dirac–Kähler operator changes the longitudinal quotient

The outer derivative \(d\) annihilates a one-form amplitude proportional to \(k_\mu\), because \(k\wedge k=0\). The **full** Dirac–Kähler derivative \(D=d+\delta_D\) retains its scalar coderivative \(\delta_D\omega\). For a longitudinal one-form \(\delta\omega_\mu=k_\mu v\),

\[
(\delta_D\delta\omega)\propto k^\mu k_\mu\,v.
\]

At \(k=(0,0,0,1)\), it is nonzero even though \(d\,\delta\omega=0\). Since the scalar background derivative response vanishes, the scalar trace-log second variation supplies a nonzero source term

\[
\boxed{
H_{\rm scalar,long}=-2\alpha/\theta_0=-3/229
}
\]

for the unit longitudinal amplitude at the reference geometry. The Yang–Mills gauge quotient from TOE-12 applies to its separate declared Yang–Mills trial. A foundational Dirac–Kähler one-form requires the scalar \(D\)-component and its own constraints in the complete Cauchy system.

## Verification and open physical work

Run the standard-library exact oracle and its regression tests:

    python -m unittest tests.test_toe17_triplet_tensor_pencil -v
    python -m research.toe.triplet_tensor_pencil
    python -m unittest discover -s tests -v
    lake build MathCan
    lake env lean MathCan/TOETripletJordan.lean

This module verifies the source-derived **strict-principal** tensor subblock at a local off-shell triplet jet and the two explicitly detuned matrices. It still lacks a homogeneous on-shell FLRW triplet configuration, the complete metric dependence of the Hodge adjoints, all scalar/vector/2-form perturbations and potential terms, lower-order pieces that affect finite-frequency stability, the lapse/shift and auxiliary G-field constraint reductions, and a uniform time-evolution symmetrizer. The next source-level task should begin with an actual on-shell triplet background and construct the complete Douglis–Nirenberg symbol including its matter constraints; the strict-root Jordan obstruction must then be tested for survival on the physical invariant subsystem.
