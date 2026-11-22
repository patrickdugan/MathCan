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

## Sealed rational results: 36 conditional signs through T = 0.012

The [first BSAR-16G dedicated CI run](https://github.com/patrickdugan/MathCan/actions/runs/45015615658) passed its four targeted tests, froze twelve source/grid cases and thirty-six conditional full-PDE signed transfer records, and re-audited their exact rational SHA-256 manifest. All five workflows passed, including source parity, BSAR-16B residual controls, the Lean kernel, and repository-wide mathematical checks.

The canonical BSAR-16G row-list SHA-256 is

    6eb0137156069d8fb969134acf313df53ea5938fd6c815c53063eb208ba820bf

The preceding source archives are BSAR-16F exact Galerkin transfer signs (SHA-256 \`daf4ebdd3b3d514beaae20381f6af9fb4c2f448b6edc04c6b8d8f5212e9ed6f3\`) and BSAR-16B rational Galerkin/PDE error envelopes (SHA-256 \`da7772a24fdc392e958c84aa49d4262401d3a94ed26bd492a568d7445f402f67\`).

The table selects the least favorable registered phase and grid for each initial frequency/shell pair. The signed lower bounds are rounded **downward**, and transfer-error upper bounds **upward** for display. Each bound holds simultaneously for **every time** \(t\in[0,3/250]\), under the explicit smooth-full-NSE-existence hypothesis.

| Initial frequency N | Shell \(\lvert k\rvert^2/N^2\) | Rational reference signed lower | Full-PDE transfer perturbation upper | Conditional full-NSE signed lower |
|---:|---:|---:|---:|---:|
| 1 | 1 | 0.243697700622 | 0.004822351793 | **0.238875348830** |
| 1 | 4 | 0.975923482352 | 0.006584986741 | **0.969338495612** |
| 1 | 5 | 0.695676988235 | 0.015127002762 | **0.680549985473** |
| 2 | 1 | 0.462723058816 | 0.181252099521 | **0.281470959296** |
| 2 | 4 | 1.860799667172 | 0.260379421364 | **1.600420245808** |
| 2 | 5 | 1.251598559639 | 0.594722308663 | **0.656876250977** |

The **least** conditional full-PDE signed margin in the registered experiment is \(0.238875348830\), for \(N=1,\sigma=-1,M=32\), shell 1. The full rational audit records **12/12 roots and 36/36 shell signs certified for the entire \(0.012\) window**. For N=2 the largest registered PDE-to-Galerkin \(L^2\) upper bound is \(0.004714812\); the corresponding total PDE-to-rational-reference upper bound is \(0.004789776587\). These upper bounds include the Galerkin spatial residual and continuous-time rational Galerkin reference error, and are distinct from empirical differences between two floating numerical runs.

**The smooth-existence premise is essential.** These numbers certify nonlinear transfer signs of an actual full NSE solution *if* such a solution is smooth on this particular time interval. They give no quantitative proof that every registered smooth source survives through T=0.012, and no lower or upper bound for the true full-PDE pointwise vorticity core. The full-PDE shell functional is controlled from \(L^2\) because the derivative moves to a finite projector; pointwise vorticity and normalized direction require different regularity information.

## Registered computation, replay and limitations

The twelve exact roots are N=1/2, \(\sigma=\pm1\), grid 16/24/32 with retained K=5/7/10, amplitude 1, viscosity 1/10, and the registered horizon 3/250. Each row reuses the exact BSAR-16B conditional PDE \(L^2\) error receipt and independently reconstructs the BSAR-16F exact rational polynomial and shell-local constants. All three shell signs are tested with rigorous directed-rational rounding of output bounds.

The dedicated CI runs standard-library Python 3.11, checks the original BSAR-14 source Git blob, tests wrong-source/viscosity/horizon exclusions and intentionally inflated PDE error negative controls, then freezes and re-audits the **36 conditionally certified shell records** with SHA-256. If a full-interval margin fails, the checker seeks a shorter dyadic rational interval and recomputes the full PDE error for that interval. A positive lower interval is recorded only after a strict rational sign gate passes.

To reproduce:

    python -m unittest experiments.bsar16.test_conditional_nse_shells -v
    python -m experiments.bsar16.conditional_nse_shells generate --out /tmp/bsar16g
    python -m experiments.bsar16.conditional_nse_shells audit --out /tmp/bsar16g

The **conditional smooth-existence hypothesis** remains visible in every row and in the manifest. This stage cannot prove smooth existence to T=0.012, establish a uniform-in-N lifetime, yield a full-PDE vorticity-core certificate, or resolve BSAR-09's uniform window budget. A separate investigation would be needed to extend the same finite-shell inequalities to suitable Leray–Hopf weak-solution representatives and their relative-energy controls.
