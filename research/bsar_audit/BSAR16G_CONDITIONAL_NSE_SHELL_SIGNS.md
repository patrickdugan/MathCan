# BSAR-16G: conditional full-NSE low-shell transfer sign persistence from \(L^2\) control

Parent: [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213), target [BSAR-16G #225](https://github.com/patrickdugan/MathCan/issues/225). Inputs: merged [BSAR-16B #216](https://github.com/patrickdugan/MathCan/pull/216) rigorous rational short-time Galerkin and **conditional full-PDE** error envelopes, plus merged [BSAR-16F #223](https://github.com/patrickdugan/MathCan/pull/223) exact-rational shell-transfer reference polynomials and quantitative Galerkin sign persistence. The original eight-mode source is independently pinned to BSAR-14 Git blob \`aa25ad74be2347acf061d631f55338802eead212\`.

**Assumption:** The exact BSAR-14 smooth, divergence-free datum has a **smooth incompressible three-dimensional Navier–Stokes solution \(u\) on \([0,\tau]\)** for the specified horizon. Standard local well-posedness gives some positive interval, but this stage does not prove smooth existence through the numerical target \(3/250=0.012\) independently. All full-PDE conclusions below are expressly conditional on existence on the certified interval. The exact finite Galerkin ODE exists globally in time, independently of this PDE assumption.

## A finite-shell observable is continuous in the velocity \(L^2\) norm

For the normalized periodic Fourier convention, let \(Q_s\) project onto the integer lattice sphere

\[
\mathcal S_s=\{k\in\mathbb Z^3:|k|^2=sN^2\},\qquad s\in\{1,4,5\}.
\]

The nonlinear transfer into shell \(s\) of a smooth real solenoidal velocity \(w\) is

\[
T_s(w)=-\operatorname{Re}\sum_{k\in\mathcal S_s}
\overline{\widehat w_k}\cdot\mathbb P_k\widehat{(w\cdot\nabla)w}_k
=-\langle Q_sw,(w\cdot\nabla)w\rangle.
\]

The finite projector \(Q_s\) commutes with the Leray projector, and \(Q_sw\) is solenoidal. For smooth divergence-free \(b\), periodic integration by parts gives

\[
\langle Q_sa,(b\cdot\nabla)c\rangle
=-\langle c,(b\cdot\nabla)Q_sa\rangle.
\]

Consequently, for any smooth solenoidal \(a,b,c\),

\[
|\langle Q_sa,(b\cdot\nabla)c\rangle|
\le\|\nabla Q_sa\|_\infty\,\|b\|_2\,\|c\|_2.
\]

The derivative lands on the **finite-frequency shell**, so the right side requires only velocity \(L^2\) norms for \(b,c\). It also extends by density to a bounded trilinear observable of solenoidal \(L^2\) fields when the derivative is understood via the integration-by-parts representation.

For arbitrary solenoidal \(e\in L^2\), regardless of its high-mode support, Fourier Cauchy–Schwarz yields

\[
\|\nabla Q_se\|_\infty
\le C_s\|e\|_2,\qquad C_s=
\sqrt{sN^2|\mathcal S_s|}.
\]

For each registered \(K\ge2N\), all modes of the relevant shells lie inside the Galerkin retained cube, and the counts are \(6,6,24\) for \(s=1,4,5\). The same shell constant applies to the difference between the **infinite-dimensional full PDE solution** and the finite rational reference.

## Source-pinned rational reference and finite Galerkin bounds

BSAR-16B defines the exact Gaussian-rational degree-two Galerkin Taylor reference

\[
p(t)=a_0+t a_1+t^2a_2,
\]

whose complete shell transfers are the exact degree-at-most-six rational polynomials

\[
T_s(p(t))=\sum_{j=0}^6 c_{s,j}t^j.
\]

BSAR-16F derives the rational signed lower reference envelope, valid uniformly for every \(0\le t\le\tau\),

\[
M_s^{\mathrm{ref}}(\tau)
=|c_{s,0}|+
\sum_{j=1}^6
\min(0,\operatorname{sgn}(c_{s,0})\,c_{s,j})\tau^j.
\]

Let \(v_K\) be the exact finite Galerkin ODE solution. By BSAR-16B's rational polynomial-defect/Gronwall inequality,

\[
\|v_K(t)-p(t)\|_2\le Y_K(\tau),
\qquad 0\le t\le\tau,
\]

where \(Y_K(\tau)\) is computed with directed rational square-root and fixed-exponential upper bounds.

Separately, under smooth existence of \(u\) on the interval, BSAR-16B supplies the conditional PDE-to-Galerkin comparison

\[
\|u(t)-v_K(t)\|_2
\le \tau R_*(\tau)\,e^{\tau G_*(\tau)}
\le Z_K(\tau),\qquad 0\le t\le\tau.
\]

Here \(R_*\) is the rigorous time-uniform Galerkin high-mode forcing envelope, \(G_*\) bounds the exact finite Galerkin velocity gradient, and the exponential is replaced by a rational upward enclosure. The implementation uses BSAR-16B's **already outward-rounded stored \(Z_K\)** and verifies the source identities, viscosity and exact horizon before use. The triangle inequality gives

\[
\|u(t)-p(t)\|_2\le
E_K(\tau):=Y_K(\tau)+Z_K(\tau),
\qquad 0\le t\le\tau.
\]

This bound can be applied to the infinite-dimensional error since the nonlinear transfer test only uses its \(L^2\) norm after moving derivatives to the finite shell.

## Explicit nonlinear transfer error and strict sign margin

Let \(P(\tau)\ge\sup_{0\le t\le\tau}\|p(t)\|_2\) and \(H_s(\tau)\ge\sup_{t\le\tau}\|\nabla Q_sp(t)\|_\infty\) be the upward rational Fourier coefficient envelopes inherited from BSAR-16F. Write \(u=p+e\), \(\|e\|_2\le E=E_K(\tau)\). Expanding the cubic trilinear functional and bounding all seven nonconstant error terms gives

\[
\left|T_s(u(t))-T_s(p(t))\right|
\le
E\left(C_sP^2+2H_sP\right)
+E^2\left(2C_sP+H_s\right)
+C_sE^3
=:\mathcal E_s^{\rm PDE}(\tau).
\]

All \(P,H_s,C_s,E\) are nonnegative **rational upper bounds**; the three powers of \(E\) explicitly account for one, two and three error insertions. The resulting rigorous conditional sign-separation inequality is

\[
\boxed{
\operatorname{sgn}(c_{s,0})\,T_s(u(t))
\ge M_s^{\rm ref}(\tau)-\mathcal E_s^{\rm PDE}(\tau)
=:\Delta_s^{\rm PDE}(\tau),
\quad 0\le t\le\tau.
}
\]

When the exact-rational lower bound is positive, the full smooth NSE flow retains the initial BSAR-14 shell-transfer sign throughout the certified interval. This is **stronger in PDE scope** than the exact finite Galerkin sign statement, subject to the separately stated smooth-existence premise. It does **not** control pointwise vorticity maxima, normalized direction fields, or half-maximum core membership of the full PDE solution; those functionals require stronger spatial regularity/error control.

## Registered computation, replay and limitations

The twelve exact roots are N=1/2, \(\sigma=\pm1\), grid 16/24/32 with retained K=5/7/10, amplitude 1, viscosity 1/10, and the registered horizon 3/250. Each row reuses the exact BSAR-16B conditional PDE \(L^2\) error receipt and independently reconstructs the BSAR-16F exact rational polynomial and shell-local constants. All three shell signs are tested with rigorous directed-rational rounding of output bounds.

The dedicated CI runs standard-library Python 3.11, checks the original BSAR-14 source Git blob, tests wrong-source/viscosity/horizon exclusions and intentionally inflated PDE error negative controls, then freezes and re-audits the **36 conditionally certified shell records** with SHA-256. If a full-interval margin fails, the checker seeks a shorter dyadic rational interval and recomputes the full PDE error for that interval. A positive lower interval is recorded only after a strict rational sign gate passes.

To reproduce:

    python -m unittest experiments.bsar16.test_conditional_nse_shells -v
    python -m experiments.bsar16.conditional_nse_shells generate --out /tmp/bsar16g
    python -m experiments.bsar16.conditional_nse_shells audit --out /tmp/bsar16g

The **conditional smooth-existence hypothesis** remains visible in every row and in the manifest. This stage cannot prove smooth existence to T=0.012, establish a uniform-in-N lifetime, yield a full-PDE vorticity-core certificate, or resolve BSAR-09's uniform window budget. A separate investigation would be needed to extend the same finite-shell inequalities to suitable Leray–Hopf weak-solution representatives and their relative-energy controls.
