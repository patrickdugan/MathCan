# TOE-03: G-field cosmology, algebraic blind spots and correlated-covariance profiling

**Date:** 2026-11-11. **Status:** primary-source reading, conditional mathematical propositions, exact-rational tests and synthetic observations. A gravitational field-equation solution, parameter estimate from sky data, and empirical confirmation of Gravity from Entropy (GfE) are **not** claimed.

## Primary sources and attribution

- Ginestra Bianconi, [*Gravity from Entropy*](https://arxiv.org/abs/2408.14391), *Phys. Rev. D* **111**, 066001 (2025).
- Ginestra Bianconi, [*Thermodynamics of the Gravity from Entropy Theory*](https://arxiv.org/pdf/2510.22545), *Phys. Rev. D* **114**, 024042 (2026), especially Eqs. (16), (20), (31), (37) and the FRW approximation in Sec. IV.
- Ginestra Bianconi, [*Λ-Gravity from Entropy*](https://doi.org/10.1016/j.physletb.2026.141014), *Phys. Lett. B* **882**, 141014 (2026), also [arXiv:2610.34496](https://arxiv.org/abs/2610.34496). This paper introduces an additional volume-constraint Lagrange multiplier Λ alongside the G-field-generated Λ_G. The ΛGfE article postdates Bianconi's July 2026 interview with Curt Jaimungal.
- [TOE Bianconi timestamped interview](https://podscan.fm/podcasts/theories-of-everything-with-curt-jaimungal/episodes/ginestra-bianconi-the-physicist-who-unexpectedly-derived-gravity-from-entropy): 07:38 geometric relative entropy; 23:45 emergent dark energy. Transcript accuracy needs comparison to the recording; the primary papers ground the equations below.

The next calculations are original MathCan *conditional* tests of a well-defined family of toy redshift histories, inspired by the cited papers. They are not equations or empirical predictions attributed to Bianconi.

## 1. What the field equations provide

The July 2026 thermodynamics paper gives the schematic metric field equation (its Eq. 20), with its tensor names retained:

\[
R^{\mathcal G}_{(\mu\nu)}-\tfrac12g_{\mu\nu}
(\mathcal R_{\mathcal G}-2\Lambda_{\mathcal G})
+\mathcal D_{(\mu\nu)}=\tfrac{\alpha}{2\beta}\,\mathcal T_{\mu\nu}.
\]

Here \(R^{\mathcal G}\) and \(\mathcal R_{\mathcal G}\) involve the **dressed** geometry, while \(\mathcal D\) includes derivatives of the G-field. At the level of the G-field's positive eigenvalues, the emergent cosmological quantity (Eqs. 16 and 37) is

\[
2\beta\Lambda_{\mathcal G}=\sum_k z_k
\bigl(\mathcal G_k-1-\ln\mathcal G_k\bigr),\qquad \mathcal G_k>0.
\]

For \(\beta>0\) and positive multiplicities \(z_k\), this local scalar is nonnegative and vanishes when all eigenvalues equal 1. The low-coupling limit reproduces ordinary GR. The 2026 ΛGfE extension adds a constant contribution, but still involves the dressed and derivative field terms. **The equations do not determine one numerical \(H(z)\) until the G-field evolution, matter stress tensor, initial conditions and normalization have been supplied and solved.** In particular, directly adding \(\Lambda_{\mathcal G}(z)/(3H_0^2)\) to a standard Friedmann equation would impose extra physical assumptions.

## 2. Explicit test closure: a conventional FRW proxy

For any redshift \(z\ge0\), put \(x=1+z\), \(E(z)=H(z)/H_0\), and define the *assumed proxy*

\[
E^2(z)=\Omega_\Lambda+\Omega_k x^2+\Omega_m x^3+\Omega_r x^4
+\varepsilon f_p(x),\qquad f_p(x)=x^p-1.
\tag{P}
\]

The four \(\Omega\) are nuisance coefficients fitted freely for a **conservative local-identification test**. The example fixes the baseline \((\Omega_\Lambda,\Omega_k,\Omega_m,\Omega_r)=(0.68,0,0.32,0)\), so \(E(0)=1\); since \(f_p(1)=0\), the perturbation preserves this normalization. The square-root rule \(H(z)=H_0\sqrt{E^2(z)}\) applies only where the right-hand side is positive.

The function \(f_p\) is a phenomenological basis function, **not a GfE field-equation solution**. A fitted \(\varepsilon\) is therefore a constraint on (P), not on the theory without a demonstrated theory-to-proxy mapping.

If future measurements are supplied as \(H_i\) with covariance \(C_H\), an approximate \(E_i^2\) covariance (for fixed \(H_0\)) is \(C_{E^2}\simeq J C_H J^\top\), with \(J_{ij}=\delta_{ij}\,2H_i/H_0^2\). Uncertain \(H_0\) contributes a correlated term and possibly cross-covariances. This project instead specifies its \(C_{E^2}\) directly as a synthetic test fixture.

## 3. Exact nuisance elimination with full covariance

At \(n\ge4\) distinct redshifts, form the \(n\times4\) matrix \(B=[1,x^2,x^3,x^4]\). Let \(C\) be a symmetric positive-definite covariance and \(W=C^{-1}\). For an arbitrary sampled deviation vector \(f\), the *profiled information per unit squared amplitude* is

\[
\boxed{\mathcal I_C(f)
=\min_{b\in\mathbb R^4}(f-Bb)^\top W(f-Bb)
=f^\top Wf-f^\top WB(B^\top WB)^{-1}B^\top Wf.}
\tag{1}
\]

**TOE-03/T1 (Schur-complement certificate).** With \(A=[B\;f]\),

\[
\boxed{\mathcal I_C(f)
=\frac{\det(A^\top W A)}{\det(B^\top W B)}.}
\tag{2}
\]

**Proof.** The GLS normal equation yields \(b_*=(B^\top WB)^{-1}B^\top Wf\). Insert it into the quadratic to get (1); the block-determinant Schur complement of \(B^\top WB\) is (2). Positive definiteness gives \(\mathcal I_C(f)=0\) precisely when \(f\in\operatorname{col}(B)\). For a noiseless injection \(y=B\theta+\varepsilon f\), profiling gives \(\chi^2_{\rm profile}=\varepsilon^2\mathcal I_C(f)\) exactly. QED.

**TOE-03/T2 (background degeneracy).** Powers \(p=0,2,3,4\) have zero profiled information for \(f_p=x^p-1\) at every redshift sample, with every positive-definite covariance. For \(p=2\), an amplitude \(\varepsilon\) is absorbed by \(\Omega_k\mapsto\Omega_k+\varepsilon\) and \(\Omega_\Lambda\mapsto\Omega_\Lambda-\varepsilon\); the same argument holds with matter and radiation for \(p=3,4\). Distinct positive \(x\) samples beyond four can detect modes with a component outside the column space. QED.

**TOE-03/T3 (calibration-gauge invariance).** Suppose \(C_0\succ0\), \(S\succeq0\), and the noise model adds an arbitrary nuisance-aligned systematic \(C=C_0+BSB^\top\). Then

\[
\boxed{\mathcal I_C(f)=\mathcal I_{C_0}(f).}
\tag{3}
\]

**Proof.** Regard the added covariance as Gaussian random shifts of the unconstrained nuisance coefficients. In the variational expression for the inverse of \(C_0+BSB^\top\), the shift is absorbed into the free least-squares coefficient. Equivalently, use Woodbury and the GLS normal equations; the residual is orthogonal to \(B\) in the \(C_0^{-1}\) metric. Continuous extension covers singular \(S\). QED. This result relies on the four nuisance amplitudes being entirely free; external calibration priors can make the added systematic relevant.

The quantity \(\mathcal I_C\) is the squared norm of the signal in the covariance-weighted **quotient by the conventional-FRW subspace**. This is mathematically the same projection pattern as TOE-01's graph gauge quotient, with vertex gradients replaced by cosmological nuisance histories.

## 4. A sharper G-field-inspired blind spot

For a homogeneous eigenvalue ansatz \(\mathcal G_k(z)=1+g_k h_q(x)\), with \(h_q=x^q-1\) and \(|g_k h_q|<1\), the source-defined scalar contributes

\[
\mathcal G_k-1-\ln\mathcal G_k
=\frac{g_k^2}{2}h_q^2-\frac{g_k^3}{3}h_q^3+O(g_k^4h_q^4).
\tag{4}
\]

**TOE-03/T4 (quadratic blind direction).** For \(q=2\),

\[
h_2^2=(x^2-1)^2=x^4-2x^2+1\in\operatorname{col}(B).
\]

Thus \(\mathcal I_C(h_2^2)=0\) exactly at any samples with a rank-four FRW design. Meanwhile

\[
h_2^3=(x^2-1)^3=x^6-3x^4+3x^2-1
\]

has an \(x^6\) component, and for a sufficiently rich set of distinct positive redshifts it produces a positive residual. The exact tests give \(\mathcal I_C(h_2^3)>0\) on the seven-point grid. This statement concerns a chosen G-field eigenvalue **and an assumed additive response in the proxy (P)**. Metric dressing and derivative terms may introduce lower-order signals, so the full GfE theory is not shown to possess this blind spot.

For \(0\le u<1\), truncating \(u-\ln(1+u)\) after term \(N\ge2\) has absolute error at most \(u^{N+1}/(N+1)\) by the alternating-series test. The Python oracle constructs these finite rational brackets without numerically evaluating logarithms.

## 5. Transparent covariance experiment

All data in this example are synthetic. The seven redshifts are \(z_i=i/5\), for \(i=0,\ldots,6\). The complete covariance is generated exactly by

\[
C_{ij}=\sigma_i\sigma_j\rho^{|i-j|}+\tau^2,
\qquad \sigma_i=\frac1{25}+\frac{z_i}{100},\quad
\rho=\frac12,\quad \tau=\frac1{50}.
\tag{5}
\]

Its AR(1)-type correlation block is positive definite, while \(\tau^2\boldsymbol1\boldsymbol1^\top\) is a common calibration-mode covariance. The full rational matrix is committed as `fixtures/bianconi_synthetic_covariance.json`, including every exact fraction. The simulator uses \(\varepsilon=1/1000\) and \(p=5\), providing the purely illustrative numbers:

- \(\mathcal I_C(f_5)=662010585944023168/168814087758438125\approx3.9215\).
- The unit-amplitude standard deviation after profiling is \(1/\sqrt{\mathcal I}\approx0.5050\).
- Synthetic noiseless injected signal-to-noise is \(|\varepsilon|\sqrt{\mathcal I}\approx0.00198\). This is far below unity under the chosen covariance.
- \(f_2,f_3,f_4\), and the quadratic G-field \(h_2^2\), yield **exactly zero** profiled information; the cubic \(h_2^3\) yields positive information.

No value in this fixture represents a measured BAO, cosmic-chronometer, supernova or CMB observation. No statistical significance or constraint on Bianconi's theory is inferred. The covariance is documented to expose how correlated calibration and redshift sampling affect observability.

## 6. Remaining physical work

The next scientific stage requires a homogeneous-isotropic reduction of the **full** ΛGfE field equations, including the dressed Ricci tensor, the derivative tensor \(\mathcal D_{\mu\nu}\), matter equations, and the G-field constraints. One must then impose regular initial data and positivity conditions, integrate the coupled system, and use its predicted \(H(z)\) as the forward model, retaining the same nuisance-profile and covariance machinery. Independent cosmological observations require a curated release with actual values, windows, units, covariance provenance and likelihood conventions.

Run:

```sh
python -m unittest tests.test_toe03_bianconi -v
python -m research.toe.bianconi_profile > /tmp/toe03_synthetic_receipt.json
```
