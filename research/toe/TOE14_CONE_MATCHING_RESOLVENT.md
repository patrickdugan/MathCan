# TOE-14: exact cone matching, near-Jordan resolvent, and a vacuum source benchmark

**2026-11-12.** The TOE-13 source-sector completion removed the old six-mode tensor root at the exact TOE-12 characteristic. TOE-14 quantifies the restricted symbol's surviving near-singularity and derives an exact two-cone discriminant certificate. It also records a **separate vacuum benchmark** against Pereira's strict-principal FLRW and Minkowski calculations.

The two benchmark models have different actions and parameters. The TOE-11/12/13 two-SU(2) action is an explicitly proposed two-form/Yang-Mills trial coupling. Its sigma parameters have not been matched to Bianconi's complete 0/1/2-form action. The vacuum benchmark therefore cannot be substituted into the coupled tensor matrix.

## Primary sources and the normalization gate

- Bianconi, *Gravity from entropy*, Phys. Rev. D 111, 066001 (2025), https://doi.org/10.1103/PhysRevD.111.066001, arXiv:2408.14391. Form-space curvature coupling and the auxiliary G-field, including errata.
- Pereira, *Gravitational Waves and Matter Constraints in Gravity from Entropy*, arXiv:2609.03082 (2026), https://arxiv.org/abs/2609.03082. Generic-FLRW strict TT cone matching, for specified vacuum/single-multiplet/perfect-fluid sectors.
- Pereira, *Vacuum Gravity from Entropy: Stability, Spectra, and Exact Waves*, Phys. Rev. D 114, 104029 (2026), https://doi.org/10.1103/lxlj-ppwh. Full vacuum Minkowski Hessian and poles.
- MathCan, [TOE-13](TOE13_FORM_SECTOR_PRINCIPAL_COMPLETION.md), the existing frozen 0/1-form completion of the declared two-SU(2) model.

**Primary-source normalization verified.** Pereira's September 2026 paper, equations (18), (19), (25), and (26), on page 3, fixes the relative one-form TT coefficient at \(c_s=1/2\), up to a common \(\beta^2\) factor. The source PDF is https://borowiecki.dev/pdf/2609.03082. One secondary review uses \(c_s=1\); TOE-14 retains alternate positive weights only as explicitly marked sensitivity controls. The source-normalized **vacuum** result is verified at the level of this reported strict-principal polynomial. A complete source-normalized two-SU(2) matter extension is still missing.

## T1. Exact two-cone discriminant and zero locus

Let \(A,B>0\), \(u,v\in\mathbb R\), and \(x=\omega^2/p^2\), \(p\ne0\). Consider

\[
q(x)=A(x-u)^2+B(x-v)^2.
\]

The coefficients of the quadratic in ascending order are

\[
c_0=Au^2+Bv^2,\quad
c_1=-2(Au+Bv),\quad c_2=A+B.
\]

Direct expansion gives

\[
\boxed{c_1^2-4c_2c_0=-4AB(u-v)^2.}
\]

Thus \(q\) has two nonreal conjugate \(x\)-roots if \(u\ne v\), namely

\[
\boxed{x_\pm=\frac{Au+Bv}{A+B}
\pm i\frac{\sqrt{AB}|u-v|}{A+B}.}
\]

Over real \(x\), \(q(x)=0\) exactly when \(x=u=v\). The statement concerns the specified homogeneous polynomial. Physical temporal modes require the full constrained symbol and a consistent analytic Fourier convention.

The rational oracle derives both the expanded and factored discriminants independently and checks 216 grid points. The source-specific Eq. (25) and Eq. (26) forms are also checked as exact Fraction identities. The new Lean module proves the matching root identity and the nonzero residual when two cone centers differ, and certifies the nonzero factored discriminant and the Gaussian-integer phase product. It does not kernel-prove the expanded polynomial discriminant equality.

## T2. Separate vacuum GfE benchmark

On an FLRW frame define the curvature eigenvalues \(A_c=H^2+\dot H\), \(B_c=H^2+K/a^2\), and choose positive inverse-response denominators. The vacuum responses are

\[
W_s=[1-\beta(A_c+2B_c)]^{-1},\quad
W_E=[1-2\beta A_c]^{-1},\quad
W_B=[1-2\beta B_c]^{-1}.
\]

For Pereira's source coefficient \(c_s=1/2\) (with \(c_s>0\) sensitivity variations), the vacuum two-square polynomial is

\[
q_4(x)=c_sW_s^2(x-1)^2+2(W_Ex-W_B)^2.
\]

Its exact discriminant is

\[
\boxed{\Delta=-8c_sW_s^2(W_E-W_B)^2.}
\]

The identity

\[
W_E-W_B=2\beta W_EW_B(A_c-B_c)
\]

makes the matching condition \(A_c=B_c\), equivalently \(\dot H=K/a^2\), on the declared \(\beta>0\), positive-denominator branch.

At the synthetic comparison \(\beta=1/100\), \(A_c=2/5\), \(B_c=1\), the exact values are \(W_s=125/122\), \(W_E=125/124\), \(W_B=50/49\). For \(c_s=1/2\), \(\Delta=-87890625/137371044496<0\). This reproduces the generic non-Einstein vacuum obstruction within the two-square benchmark and is independent of the trial coupled SU(2)^2 discriminant.

For Minkowski vacuum Pereira's 2026 PRD paper reports the quadratic-gravity coefficients \(3\beta/\ell_P^4\) for \(R\), \(5\beta^2/(2\ell_P^4)\) for \(R_{\mu\nu}R^{\mu\nu}\), with \(m_0^2=3/(5\beta)\) and \(m_2^2=-6/(5\beta)\). The \(\beta=1/100,\ell_P=1\) regression pins \(m_0^2=60\), \(m_2^2=-120\). These are input source benchmarks, not a new field-equation derivation.

## T3. Exact restricted six-mode resolvent lower bound

TOE-13's old formal root is

\[
r=\frac{480993997}{493000000},\quad
C_1=\frac1{1905152}.
\]

At \(\omega^2=r,p=1\), the TOE-13 tensor matrix has the exact block form

\[
P_{13}(\sqrt r)=\operatorname{diag}(\delta I_2,G(\sqrt r)),
\quad \delta=C_1(r-1)^2,
\]

where the four-mode gauge block is invertible in the TOE-13 reference computation. The rational expression is

\[
\boxed{\delta=\frac{144144108036009}
{463045288448000000000000}.}
\]

For the standard Euclidean spectral norm on this explicitly normalized six-mode coordinate basis,

\[
\boxed{\|P_{13}(\sqrt r)^{-1}\|_2\ge
\delta^{-1}=
\frac{463045288448000000000000}{144144108036009}
\approx 3.212377493\times 10^9.}
\]

This is a near-singular **static inverse-symbol** bound. It is basis-normalization-dependent, and the result itself is neither a time-domain growth-rate theorem nor a condition-number bound for the constrained physical system.

## T4. Real-frequency Fourier phases

For a real symmetric formal two-mode bilinear \(P=\left(\begin{smallmatrix}a&b\\b&c\end{smallmatrix}\right)\), the constant phase matrix \(U=\operatorname{diag}(-1,i)\) gives the Hermitian Fourier bilinear

\[
U^\dagger P U=
\begin{pmatrix}a&-ib\\ib&c\end{pmatrix},
\qquad
\det(U^\dagger P U)=ac-b^2=\det P.
\]

The Python oracle tests this determinant identity over 200 seeded rational triples. Lean proves the corresponding Gaussian-integer product and two-mode determinant formula. The result applies to the congruence of a real-frequency frozen bilinear and leaves the analytic continuation, lower-order terms, constraints and first-order Cauchy reduction open.

## Evidence, reproduction, and next physics gate

- 13 standard-library Python test methods, covering 216 exact rational cone configurations, two distinct one-form source conventions, vacuum curvature and Minkowski mass checks, a TOE-13 exact resolvent numerator/denominator, and 200 Fourier-phase instances.
- Lean structural algebra in MathCan/TOEConeMatching.lean, imported into the root MathCan library and the CI transitive-axiom audit. CI must pass before calling these Lean claims kernel-verified.
- Explicit receipts retain **vacuum_source_normalization_independently_verified=true**, **coupled_GfE_YM_constraints_derived=false**, and **physical_hyperbolicity_verified=false**.

Reproduce:

    python -m unittest tests.test_toe14_cone_matching -v
    python -m research.toe.cone_matching
    python -m unittest discover -s tests -v
    lake build MathCan
    lake env lean MathCan/TOEConeMatching.lean

The next substantial calculation needs Bianconi's complete source-normalized 0/1/2-form action, with a well-defined non-Abelian extension and background equations. Derive the complete metric/G/YM first variation, classify all SO(3) helicity channels, impose lapse/shift and Gauss constraints, and construct the physical first-order matrix before evaluating characteristic roots. The vacuum Pereira polynomial and the trial TOE-13 six-mode polynomial must remain independently reproducible controls throughout that work.
