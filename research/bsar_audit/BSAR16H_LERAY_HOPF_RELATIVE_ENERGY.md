# BSAR-16H: Leray–Hopf relative energy and almost-everywhere low-shell signs

Parent: [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213), target [BSAR-16H #228](https://github.com/patrickdugan/MathCan/issues/228). Dependencies: merged [BSAR-16B #216](https://github.com/patrickdugan/MathCan/pull/216), [BSAR-16F #223](https://github.com/patrickdugan/MathCan/pull/223) and [BSAR-16G #226](https://github.com/patrickdugan/MathCan/pull/226). Original eight-mode source pinned to BSAR-14 blob aa25ad74be2347acf061d631f55338802eead212.

**Statement and scope.** Let u be any mean-zero Leray–Hopf weak solution of the unforced three-dimensional periodic Navier–Stokes equations with one of the four exact BSAR-14 smooth divergence-free initial data (N=1,2, phase sigma=±1, A=1, viscosity nu=1/10). For each registered retained Galerkin cutoff K=5,7,10, the original three low-shell nonlinear transfers retain their initial signs for **almost every time t in [0,3/250]**. The signed rational lower bounds are those already sealed in BSAR-16G, with minimum 0.238875348830. This conclusion requires no premise that the full NSE solution remains smooth to the specified endpoint, and applies to every Leray–Hopf solution in the stated energy class.

The proof below combines a standard weak-solution relative-energy argument against a smooth *residual-forced approximate solution* with the exact rational calculations already audited in BSAR-16B/G. The Python companion checks finite Fourier algebra and those rational receipts; it is **not a Lean formal proof of infinite-dimensional weak PDE theory**.

## 1. Domain, Fourier normalization and weak solution class

Use the flat torus \(\mathbb T^3=(\mathbb R/2\pi\mathbb Z)^3\), with the spatial-average pairing

\[
\langle a,b\rangle=(2\pi)^{-3}\int_{\mathbb T^3}a(x)\cdot b(x)\,dx,\qquad
\|a\|_2^2=\sum_{k\in\mathbb Z^3}|\widehat a(k)|^2.
\]

Let H be the real mean-zero solenoidal L2 space and V its H1 counterpart. Write \(A=-\mathbb P\Delta\), \(B(a,b)=\mathbb P[(a\cdot\nabla)b]\), and \(b(a,b,c)=\langle(a\cdot\nabla)b,c\rangle\) for smooth divergence-free fields.

The admissible Leray–Hopf solution \(u\) belongs to

\[
L^\infty(0,T;H)\cap L^2(0,T;V)\cap C_{\mathrm{weak}}([0,T];H),
\]

solves \(\partial_t u+\nu Au+B(u,u)=0\) distributionally with strong initial L2 trace \(u(0)=u_0\), and satisfies for almost every terminal time \(t\in[0,T]\)

\[
\frac12\|u(t)\|_2^2+\nu\int_0^t\|\nabla u\|_2^2\,ds
\le\frac12\|u_0\|_2^2.
\]

Existence of global periodic Leray–Hopf solutions from these smooth finite-energy data is a classical theorem. The choice of an a.e.-time conclusion makes the statement invariant under changes on an exceptional null set; it does not depend on weak-solution uniqueness.

## 2. Galerkin field and the residual sign

For the strict retained cube \(\Lambda_K=\{k:\max_i|k_i|\le K\}\), let \(v=v_K\) be the exact finite Galerkin ODE solution from the same source datum:

\[
\partial_t v+\nu Av+P_{\le K}B(v,v)=0,\qquad v(0)=u_0 .
\]

Its exact Galerkin energy identity gives \(\|v(t)\|_2\le\|u_0\|_2=2\), so the finite ODE exists smoothly for all positive time.

The full-PDE residual of v is

\[
r_K:=\partial_t v+\nu Av+B(v,v)=P_{>K}B(v,v).
\]

Thus the residual appears on the **right** of the approximate PDE, \(\partial_t v+\nu Av+B(v,v)=r_K\). For the difference \(w=u-v\), subtraction yields the forcing \(-r_K\) and the formal identity

\[
\partial_t w+\nu Aw+B(u,u)-B(v,v)=-r_K.
\]

The source's nonzero initial residual at N=2, K=5/7 is exactly audited in BSAR-16A. The companion BSAR-16H Gaussian-rational test takes \(w=r_K(0)/11\) for N=2, K=5 and verifies the sign of the residual forcing and the cancellation of transport energy work.

## 3. Derive relative energy using the weak formulation

A Leray–Hopf solution cannot generally be used as a pointwise classical test of its own equation. Instead use the smooth solenoidal v as a time-dependent test function in the weak formulation, justified by time cutoff/mollification and weak traces. For admissible t,

\[
\langle u(t),v(t)\rangle-\langle u_0,v_0\rangle
=\int_0^t
\big(\langle u,\partial_s v\rangle
-\nu\langle\nabla u,\nabla v\rangle
-b(u,u,v)\big)\,ds .
\tag{3.1}
\]

The smooth approximate solution satisfies

\[
\frac12\|v(t)\|_2^2+\nu\int_0^t\|\nabla v\|_2^2\,ds
=\frac12\|v_0\|_2^2+\int_0^t\langle r_K,v\rangle\,ds.
\tag{3.2}
\]

Here \(\langle r_K,v\rangle=0\), because the high-mode residual and the retained field have disjoint Fourier supports. Combine (3.1), (3.2), and the weak energy inequality, using \(u_0=v_0\). Substituting \(\partial_s v=-\nu Av-B(v,v)+r_K\) yields the nonlinear cross term

\[
b(u,u,v)+b(v,v,u)=-b(w,v,w)
\]

by periodic integration by parts and solenoidality. The result for almost every terminal time is

\[
\boxed{
\frac12\|w(t)\|_2^2+
\nu\int_0^t\|\nabla w(s)\|_2^2\,ds
\le-\int_0^t b(w,v,w)\,ds
-\int_0^t\langle r_K,w\rangle\,ds .
}
\tag{RE}
\]

The **coefficient of kinetic energy is 1/2**, the **coefficient of dissipation is nu**, and the omitted high-mode residual has the **minus** sign. These signs are independently checked on nontrivial exact finite Fourier data. The weak statement itself follows from the weak formulation and energy inequality, not from the finite checker.

Since \(|b(w,v,w)|\le\|\nabla v\|_\infty\|w\|_2^2\), setting \(G(s)=\|\nabla v(s)\|_\infty\) and \(R(s)=\|r_K(s)\|_2\) gives

\[
\frac12\|w(t)\|_2^2
\le\int_0^t G(s)\|w(s)\|_2^2+R(s)\|w(s)\|_2\,ds .
\tag{3.3}
\]

## 4. Integral comparison for an energy-class solution

Let \(f(t)=\|w(t)\|_2\) be a nonnegative measurable representative, defined almost everywhere. Write

\[
J(t)=\int_0^t\big(G(s)f(s)^2+R(s)f(s)\big)\,ds .
\]

Because f is essentially bounded, and G,R are continuous and bounded, J is absolutely continuous. By (3.3), \(f(t)^2\le2J(t)\) for almost every t. Hence

\[
J'(t)\le2G(t)J(t)+R(t)\sqrt{2J(t)}
\]

at almost every Lebesgue time. For any epsilon > 0, take \(H_\epsilon(t)=\sqrt{2J(t)+\epsilon^2}\). Direct differentiation gives

\[
H_\epsilon'(t)\le G(t)H_\epsilon(t)+R(t)
\quad\text{for almost every }t.
\]

The scalar integrating-factor argument, followed by epsilon down to zero, proves

\[
\boxed{
\|u(t)-v_K(t)\|_2
\le\int_0^t R(s)\,
\exp\Big(\int_s^t G(\tau)\,d\tau\Big)\,ds
\quad\text{for a.e. }t\in[0,T].
}
\tag{4.1}
\]

The argument uses absolute continuity of J, **not** absolute continuity of the Leray–Hopf velocity norm. The initial difference is zero by the strong initial trace.

The exact finite Galerkin path is already bounded by the BSAR-16B rational certificates, for all times in [0,T]:

\[
R(s)\le R_*(T),\qquad G(s)\le G_*(T).
\]

Consequently, for a.e. t in [0,T],

\[
\|u(t)-v_K(t)\|_2
\le T R_*(T)\exp(TG_*(T))
\le Z_K(T),
\tag{4.2}
\]

where \(Z_K(T)\) is the **same directed-rational upper bound** frozen in BSAR-16B and reused by BSAR-16G. Its numerical values thus apply to every Leray–Hopf solution without an independent smooth-full-NSE lifespan hypothesis.

## 5. The finite-shell observable is continuous in velocity L2

For each original shell \(s\in\{1,4,5\}\) at frequency N, let \(Q_s\) project onto the finite lattice sphere \(\mathcal S_s=\{k\in\mathbb Z^3:|k|^2=sN^2\}\). For any real solenoidal \(a\in H\), define

\[
\boxed{
T_s(a)=\langle a,(a\cdot\nabla)Q_s a\rangle.
}
\tag{5.1}
\]

This is a well-defined integral: \(Q_sa\) is a finite trigonometric polynomial with bounded derivative and \(a\in L^2\). For smooth a, solenoidality and periodic integration by parts give the original BSAR-14 convention

\[
T_s(a)=-\langle Q_sa,(a\cdot\nabla)a\rangle.
\]

The trilinear expression

\[
\tau_s(a,b,c)=\langle Q_sa,(b\cdot\nabla)c\rangle
=-\langle c,(b\cdot\nabla)Q_sa\rangle
\]

extends to divergence-free \(H^3\), because

\[
|\tau_s(a,b,c)|
\le\|\nabla Q_sa\|_\infty\|b\|_2\|c\|_2
\le C_s\|a\|_2\|b\|_2\|c\|_2
\]

with \(C_s=\sqrt{sN^2|\mathcal S_s|}\). The exact shell counts for s=1,4,5 are respectively 6,6,24 and all shell modes are retained by the registered Galerkin cubes. Thus \(T_s\) is locally Lipschitz in the velocity L2 norm.

Let p(t) be the BSAR-16B Gaussian-rational degree-two reference. The exact Galerkin-to-reference bound is \(Y_K(T)\). By (4.2), for a.e. t in [0,T],

\[
\|u(t)-p(t)\|_2\le E_K(T):=Y_K(T)+Z_K(T).
\]

The BSAR-16F/G trilinear expansion includes all terms linear, quadratic and cubic in this error:

\[
|T_s(u(t))-T_s(p(t))|
\le E(C_sP^2+2H_sP)+E^2(2C_sP+H_s)+C_sE^3
=:\mathcal E_s(T),
\tag{5.2}
\]

where P bounds the reference L2 norm and \(H_s\) bounds the gradient of its finite-shell projection. The exact-rational degree-six transfer polynomial supplies the signed reference margin \(M_s^{\rm ref}(T)\). Therefore

\[
\boxed{
\operatorname{sgn}(T_s(u_0))\,T_s(u(t))
\ge M_s^{\rm ref}(T)-\mathcal E_s(T)>0
\quad \text{for a.e. } t\in[0,3/250].
}
\tag{5.3}
\]

Every rational right-hand side was sealed in BSAR-16G. The smallest signed margin across all 36 registered shell/source/grid rows is **0.238875348830**.

This theorem concerns a finite-shell low-frequency observable, defined at almost every time for weak velocities. It does not imply pointwise vorticity control, uniqueness, regularity, or sign persistence for all Fourier shells. A statement at every time would additionally require a theorem relating the weak representative to the L2-continuous cubic observable at exceptional times.

## 6. Certificate custody and reproduction

The companion verifier independently calls the sealed BSAR-16G exact-rational generator, checks its canonical SHA-256 **6eb0137156069d8fb969134acf313df53ea5938fd6c815c53063eb208ba820bf**, and audits all 12 roots and 36 signed shell inequalities. The new rows explicitly label the conclusion **almost every time**, **every Leray–Hopf weak solution** of the source datum, and **no smooth full-NSE lifespan premise**.

A finite Gaussian-rational sign audit constructs a nonzero high-mode perturbation \(w=r_K(0)/11\) at N=2,K=5 and verifies the exact forcing sign, transport cancellation, viscous coefficient, and sign equivalence between derivative-shifted and original shell-transfer definitions. These are algebraic checks; the weak comparison step is established analytically above.

Reproduce from the MathCan repository root, using only Python 3.11 standard library:

    python -m unittest experiments.bsar16.test_weak_shell_signs -v
    python -m experiments.bsar16.weak_shell_signs generate --out /tmp/bsar16h
    python -m experiments.bsar16.weak_shell_signs audit --out /tmp/bsar16h

**Outstanding mathematics:** full-PDE pointwise half-maximum vorticity-core geometry, the 3D global smoothness/uniqueness problem, and the uniform-in-frequency BSAR-09 ratio-window budget all remain open.

## Background references

- [From Jean Leray to the millennium problem: the Navier–Stokes equations](https://link.springer.com/article/10.1007/s00028-020-00645-3), for Leray–Hopf existence and the energy class.
- [Three results on the energy conservation for the 3D Euler equations](https://doi.org/10.1007/s00030-024-00924-9), for the periodic Leray–Hopf definition and energy inequality.
- [Uniqueness for some Leray–Hopf solutions to the Navier–Stokes equations](https://doi.org/10.1016/S0022-0396(02)00108-0), for the relative-energy weak–strong comparison approach. The present argument uses a smooth approximate comparison with an explicitly retained residual.
