# TOE-06: Componentwise FLRW gates, tensor cone matching, and a source-verification boundary

**Status, 11 November 2026.** Exact finite FLRW Ricci and TT discriminant identities, an independent spatial reduced-action Euler–Lagrange residual, a numerical Weyl-trace *target*, and a typed validation interface for Bianconi's covariant equations. These are synthetic calculations on TOE-05's reduced scalar trajectory. **The dressed stress tensor and derivative tensor have not yet been computed independently from Bianconi's complete 4D action; a full covariant solution has not been certified.**

## Primary sources and provenance

* [G. Bianconi, *Λ-Gravity from Entropy*](https://arxiv.org/abs/2610.34496), Eqs. (5), (7), (16), (45), (47), and (48), for the induced G-field spectrum, covariant Weyl trace, trace-free metric equation and joint conservation identity.
* [D. S. Pereira, *Gravitational Waves and Matter Constraints in Gravity from Entropy*](https://arxiv.org/abs/2609.03082), for the strict-principal transverse-traceless (TT) characteristic test on vacuum, symmetry-inheriting single-multiplet, and a specific algebraic fluid sector. We use the quadratic-in-ω² two-square symbol from that analysis. This is a theoretical result under stated sector assumptions, not a demonstration of finite-frequency instability on an observed cosmological background.
* [MathCan TOE-05](BIANCONI_DRESSED_SCALAR_FLRW.md), the pinned background ODE. All measurements are dimensionless, with no cosmological data.

**Extension caveat:** Pereira's calculation studies GfE, while TOE-05 uses Bianconi's constrained-volume ΛGfE extension. Applying its strict-principal symbol to ΛGfE assumes that the constant-volume term contributes no fourth-derivative TT principal part. The matter sector here has one homogeneous *real scalar*, with no homogeneous two-form component. Multimultiplet and higher-order matter responses fall outside this test.

## 1. Exact Ricci projections

Write \(A=H^2+\dot H\), \(B=H^2+K/a^2\) for FLRW. With signature \((-+++)\), the orthonormal-frame Ricci components are

\[
R_{00}=-3A,\quad R_{ii}=A+2B,\quad R=6(A+B).
\]

After subtracting the trace, \(\mathring R_{00}=\frac32(B-A)\) and \(\mathring R_{ii}=\frac12(B-A)\). Hence

\[
\boxed{\mathring R^\mu{}_{\nu}\mathring R^\nu{}_{\mu}
     =3(A-B)^2=3(\dot H-K/a^2)^2.}\tag{1}
\]

The identity is verified in exact rational arithmetic over 500 reproducible curved-FLRW samples. The normalized form-space curvature trace with unit G-field response is \(\sum_i z_iR_i=18(A+B)=3R\), a distinct trace from the four-dimensional scalar curvature.

## 2. Tensor cone and a negative discriminant

The relevant inverse G-field sectors are

\[
W_s=[1-\beta(A+2B)]^{-1},\quad
W_E=[1-2\beta A]^{-1},\quad W_B=[1-2\beta B]^{-1}.
\]

Pereira's strict-principal TT characteristic in the symmetry-inheriting single-multiplet sector has a two-square form, for real frequency \(\omega\) and spatial momentum \(p\):

\[
q_4(\omega,p)=\tfrac12W_s^2(\omega^2-p^2)^2
                    +2(W_E\omega^2-W_Bp^2)^2.\tag{2}
\]

For \(p\ne0\) put \(x=\omega^2/p^2\), so \(q_4/p^4=ax^2+bx+c\), with

\[
a=\tfrac12W_s^2+2W_E^2,\quad b=-(W_s^2+4W_EW_B),\quad
c=\tfrac12W_s^2+2W_B^2.
\]

Exact expansion gives a discriminant that is never positive:

\[
\boxed{\Delta=b^2-4ac=-4W_s^2(W_E-W_B)^2
=-\tfrac{16}{3}\beta^2W_s^2W_E^2W_B^2\,
\mathring R^\mu{}_{\nu}\mathring R^\nu{}_{\mu}.}\tag{3}
\]

The denominator identity \(W_E-W_B=2\beta(A-B)W_EW_B\) supplies the last equality. The exact positive-eigenvalue domain makes all response factors strictly positive. On \(\dot H\ne K/a^2\), the squared-frequency characteristic roots form a complex-conjugate pair. Only \(\dot H=K/a^2\) permits the common real null cone \(\omega^2=p^2\). This gives a quantitative correspondence between a gauge-invariant curvature scalar and the TT-cone mismatch.

For the reference flat scalar trajectory \(\dot H\) is negative from \(z=0\) through \(z=0.5\). Every sampled branch point fails the **strict-principal** test. A small imaginary frequency ratio \(|\mathrm{Im}(\omega)|/|p|\) comes from the principal polynomial; treating it as a physical growth rate requires checking the EFT cutoff, wavelength, and lower-derivative terms. This gate is independent of an observational H(z) fit.

## 3. Independent reduced spatial variation

For \(N=1\), TOE-05's on-shell reduced action is \(L=a^3[F]\), \(F=f(A,B,\phi,\pi)-6\beta\Lambda\) with \(A=\ddot a/a\), \(B=(\dot a/a)^2\), and \(\pi=\dot\phi\). Varying **the scale factor** independently of the lapse and scalar equations yields

\[
\boxed{
\frac{E_a}{a^2}=3F+(3H^2+\dot H)f_A-(6H^2+2\dot H)f_B
+4H\dot f_A-2H\dot f_B+\ddot f_A.}\tag{4}
\]

We evaluated \(\dot f_A,\dot f_B\) from analytically differentiated sector denominators. A centered time derivative of \(\dot f_A\), sampled using RK4 on the TOE-05 equations, gives \(|E_a/a^2|<2\times10^{-8}\) on all six reference states, including a second step-size calculation. This checks an independent **symmetry-reduced** Euler–Lagrange equation. It cannot substitute for the 4D dressed matter tensor, curvature-response derivative tensor, or perturbative stability audit.

## 4. Explicit source Weyl-trace target

For the five sectors with multiplicities \(z=(1,1,3,3,3)\), define

\[
\mathcal R_{\mathcal G}=\sum_i z_i\mathcal G_i\,(c_{Ai}A+c_{Bi}B),\qquad
\Lambda_{\mathcal G}=\frac{1}{6\beta}\sum_i z_i(\mathcal G_i-1-\ln\mathcal G_i).
\]

The source's Weyl trace equation requires

\[
\boxed{\mathcal D-3\kappa\mathcal T
    =\mathcal R_{\mathcal G}-12(\Lambda+\Lambda_{\mathcal G}).}\tag{5}
\]

The executable audit calculates the right-hand side along the synthetic trajectory. It is the **target** that independent evaluations of the full \(\mathcal D\) and *dressed* \(\mathcal T\) tensors must match. Its values change throughout the trajectory. The de Sitter, zero-scalar reference has target zero and matches TOE-04's covariant Weyl-trace normalization.

The source's isotropic trace-free metric condition remains

\[
X_0+X_s=3\kappa(\rho_{\mathcal G}+p_{\mathcal G}),
\quad X_{\mu\nu}=R^{\mathcal G}_{(\mu\nu)}+\mathcal D_{(\mu\nu)}.
\]

The Noether condition uses \(\dot X_0+3H(X_0+X_s)+\frac12(\dot{\mathcal R}_{\mathcal G}-6\dot\Lambda_{\mathcal G})=3\kappa[\dot\rho_{\mathcal G}+3H(\rho_{\mathcal G}+p_{\mathcal G})]\). An explicit `CovariantComponents` schema requires independently constructed \(X_0,X_s,\rho_{\mathcal G},p_{\mathcal G},\mathcal R_{\mathcal G},\mathcal D,\Lambda_{\mathcal G}\) and time derivatives before returning the three componentwise source residuals. The TOE-05 background curve cannot populate that schema without a 4D tensor derivation, so `full_covariant_tensor_evidence` remains **false**.

## 5. Reproduce and research gates

```bash
python -m unittest tests.test_toe06_covariant -v
python -m research.toe.covariant_tensors
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOECovariantGates.lean
```

The new module has 23 independent standard-library test methods, plus a deterministic exact-rational grid of response and discriminant identities. The Lean module certifies algebraic Ricci normalization, conditional two-square implications, and Weyl rearrangement. It does **not** kernel-prove the fourth-order tensor action or the complete coupled 4D field equations.

**Outstanding source-level work:** compute the metric variation of Bianconi's full induced matter tensor to obtain \(\mathcal T_{\mu\nu}\), evaluate \(\mathcal D_{\mu\nu}\) with all covariant derivatives, and check Eqs. (45), (47), and (48) against an independently computed 4D geometry. For dynamical viability, examine Pereira's cutoff/strict-principal assumptions and explicit two-multiplet escape sectors before investing in an observational parameter fit.
