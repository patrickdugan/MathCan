# AHR-03: Symplectic mode transport, non-Abelian holonomy, and an exact hypercube face law

**Date:** 2026-11-23. **Status:** A self-contained four-oscillator model with derived noncommuting stable-mode holonomies; separately, a combinatorial proof of the hypercube trace-moment identity. All numerical checks are finite-dimensional and local. The oscillator construction is a **surrogate model** and has not been identified with the reduced Riemann-ellipsoid Hamiltonian.

## 1. The cyclic arithmetic graph and its exact fourth moment

Let \(Q_d\) be the graph on \(\{0,1\}^d\) whose edges flip one prime-exponent bit. Choose any real site energies \(V_x\), any fixed hopping modulus \(J>0\), and phases \(A_{xy}=-A_{yx}\):

\[
H_A=\sum_x V_x|x\rangle\langle x|+J\sum_{\{x,y\}\in E(Q_d)} \big(e^{iA_{xy}}|x\rangle\langle y|+e^{-iA_{xy}}|y\rangle\langle x|\big).
\]

Here the summation over edges uses a fixed orientation; reversing an edge changes the phase sign. Let \(H_0\) retain the same \(V_x,J\) and set all edge phases to zero. Each oriented square face \(f\) has gauge-invariant flux \(F_f=\sum_{(x,y)\in\partial f}A_{xy}\pmod{2\pi}\).

**Theorem (face detection by fourth moment).** For any \(d\ge2\),

\[
\operatorname{Tr}(H_A^k)=\operatorname{Tr}(H_0^k)\quad (k=0,1,2,3),
\qquad
\boxed{\operatorname{Tr}(H_A^4)-\operatorname{Tr}(H_0^4)
=8J^4\sum_{f\subset Q_d}(\cos F_f-1).}
\]

**Proof.** Expand each diagonal matrix element of \(H_A^k\) as a weighted closed walk of length \(k\), with each diagonal factor interpreted as a stay and each off-diagonal factor as an edge traversal. Any closed walk with at most three steps contains no non-backtracking cycle in the bipartite cube, so the directed edge phases cancel. At length four, flux can survive only when all four factors are edge steps forming a simple square. Every face contributes four choices of starting corner in each orientation, each with weight \(J^4e^{\pm iF_f}\). Its contribution to the trace is \(8J^4\cos F_f\), compared with \(8J^4\) at zero flux. All other four-step closed walks consist of stays or backtracking and have equal weight in the two Hamiltonians. Summing face contributions proves the identity. \(\square\)

The cube has \(\binom d2 2^{d-2}\) square faces. With \(Z_A(\beta)=\operatorname{Tr}(e^{-\beta H_A})\), the exact theorem gives

\[
Z_A(\beta)-Z_0(\beta)
=\frac{\beta^4J^4}{3}\sum_f(\cos F_f-1)+O(\beta^5),\qquad \beta\to0.
\]

For a particular vertex \(x\), the first flux-dependent return-probability coefficient is

\[
\left|\langle x|e^{-itH_A}|x\rangle\right|^2-
\left|\langle x|e^{-itH_0}|x\rangle\right|^2
=\frac{J^4t^4}{6}\sum_{f\ni x}(\cos F_f-1)+O(t^6).
\]

The proof does not depend on arithmetic site energies. Establishing a prime-specific computational effect requires separate controlled experiments.

## 2. A stable four-oscillator surrogate with a degenerate three-mode band

Take a real four-component displacement vector \(z\in\mathbb R^4\), momentum \(p\), and configuration parameter \(q=(q_1,q_2,q_3)\) with \(\|q\|<1\). Define

\[
n(q)=(q_1,q_2,q_3,\sqrt{1-\|q\|^2})\in S^3,
\qquad K(q)=\omega^2I_4+\Delta n(q)n(q)^\top,\quad \omega>0,\Delta>0,
\]

\[
\mathcal H(q;z,p)=\tfrac12 p^\top p+\tfrac12 z^\top K(q)z.
\]

The Hessian \(K(q)\) has a stable threefold degenerate eigenvalue \(\omega^2\) on \(n(q)^\perp\), and a stable isolated eigenvalue \(\omega^2+\Delta\) along \(n(q)\). Frequencies are \(\omega,\omega,\omega,\sqrt{\omega^2+\Delta}\). The dynamical phase separation is set by the positive frequency gap.

Select a smooth orthonormal tangent frame \(U(q)\in\mathbb R^{4\times3}\) satisfying \(U^\top U=I_3\) and \(U^\top n=0\). In the northern chart \(h=\sqrt{1-\|q\|^2}\), an explicit choice is

\[
\boxed{U(q)=\begin{pmatrix}I_3-\frac{qq^\top}{1+h}\\-q^\top\end{pmatrix}.}
\]

The phase-space Hamiltonian matrix is \(\Omega\,\operatorname{diag}(K,I_4)\) for \(\Omega=\begin{psmallmatrix}0&I_4\\-I_4&0\end{psmallmatrix}\). If \(u_a\) is the \(a\)-th column of \(U\), its positive-frequency complex normal mode is

\[
\xi_a(q)=\frac1{\sqrt{2\omega}}\binom{u_a(q)}{-i\omega u_a(q)},
\qquad (\Omega\nabla^2\mathcal H)\xi_a=-i\omega\xi_a.
\]

The symplectic Hermitian inner product \(\langle\xi,\eta\rangle_{\Omega}=i\xi^\dagger\Omega\eta\) satisfies \(\langle\xi_a,\xi_b\rangle_\Omega=\delta_{ab}\). The connection induced on this stable positive-frequency band is

\[
\boxed{\mathcal A_{ab}=i\xi_a^\dagger\Omega\,d\xi_b=u_a^\top du_b,
\qquad \mathcal A=U^\top dU\in\mathfrak{so}(3).}
\]

For slow parameter motion, the common dynamical oscillation can be factored from the mode envelopes, whose adiabatic transport obeys \(dc=-\mathcal A(\dot q)c\,dt\). The standard adiabatic gap and smoothness conditions must be checked when simulating full second-order oscillator dynamics.

## 3. Explicit non-Abelian curvature

Let \(P(q)=I_4-n(q)n(q)^\top=U(q)U(q)^\top\). The curvature is

\[
\mathcal F=d\mathcal A+\mathcal A\wedge\mathcal A
=dU^\top (I-P)\wedge dU.
\]

At \(q=0\), \(U=(I_3;0)\), and \(\partial_i U\) has bottom row \(-e_i^\top\). Therefore

\[
\boxed{\mathcal F_{ij}(0)=e_i e_j^\top-e_j e_i^\top.}
\]

In particular, defining \(F_{12}=E_{12}-E_{21}\) and \(F_{23}=E_{23}-E_{32}\),

\[
\boxed{[F_{12},F_{23}]=E_{13}-E_{31}=F_{13}\ne0.}
\]

Small loops in the \((q_1,q_2)\) and \((q_2,q_3)\) planes induce noncommuting mode transformations. The obstruction appears at second order in the enclosed areas: \(W_AW_B-W_BW_A\sim (\text{area}_A)(\text{area}_B)[F_{12},F_{23}]\), with orientation-dependent sign.

For a rectangle of side \(r<1/\sqrt2\) in either coordinate plane, the loop lies on a unit two-sphere inside \(S^3\). Gauss–Bonnet gives the magnitude of its mode rotation angle:

\[
\boxed{\theta(r)=\int_0^r\!\int_0^r\frac{dx\,dy}{\sqrt{1-x^2-y^2}}.}
\]

The first loop rotates the \((1,2)\) modal plane and fixes mode 3. The second rotates the \((2,3)\) plane and fixes mode 1. For initial tangent-mode vector \(c_0=e_1\), the distance between the two path-order outcomes is

\[
\boxed{\|W_AW_Bc_0-W_BW_Ac_0\|_2
=2|\sin\theta\,\sin(\theta/2)|.}
\]

For the representative value \(r=0.55\), exact quadrature and numerical parallel transport agree to approximately \(10^{-12}\): \(\theta=0.3421975269255724\) rad, endpoint-mode difference \(0.11426768544\), and Frobenius norm of \(W_AW_B-W_BW_A\) approximately \(0.16392457024\). The physical vertex returns to its starting point for both loops. This is a finite path-order memory that can be read out through modal amplitudes.

## 4. Interpretation and experimental gates

- **Established within AHR-03:** stable four-oscillator Hamiltonian, triple mode degeneracy, symplectic connection, nonzero noncommuting curvature, analytic loop-angle integral, checked path-order effect, and the combinatorial fourth-moment theorem.
- **Open physical realization:** find a family of stable relative equilibria of a reduced rotating Riemann-ellipsoid system and a *protected or sufficiently isolated* multi-mode eigenspace that supports an analogous symplectic connection. Compute its actual \(\Omega\nabla^2H_{\mathrm{red}}\), project mode vectors in the correct symplectic Krein metric, and compare Wilson loops. Stability/degeneracy cannot be assumed from the toy system.
- **Quantum engineering:** a two-qubit circuit can encode the three-dimensional real modal subspace and implement embedded \(SO(3)\) rotations. Compare loop-order readouts, commuting control loops, and matched ordinary gate controls. Report coherence and gate counts before spending QPU time.
- **Complexity:** the four-oscillator example has a constant-size classical simulation. Neither the holonomy effect nor flux-threaded arithmetic graphs establish a complexity-class advantage or a consciousness test.

## 5. Reproduce

From the directory containing the script:

```sh
python ahr03_verify.py
```

Requires NumPy and SciPy. Writes `ahr03_validation.json` and verifies the exact face law on seeded random hypercubes of dimension 2–5, with arbitrary site energies and edge phases. It separately integrates adiabatic parallel transport in the oscillator surrogate using DOP853 and compares with the analytic spherical-area formula.

**Suggested formalization:** Prove the fourth-moment theorem in Lean as a closed-walk classification on finite bipartite graphs with girth 4, then specialize to the Boolean cube. Treat the oscillator connection in real finite-dimensional matrix algebra first, followed by a carefully chosen symplectic-normal-mode interface.