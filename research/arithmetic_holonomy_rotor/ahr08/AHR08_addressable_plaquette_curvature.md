# AHR-08: addressable plaquette curvature on the intact prime cube

**2026-11-23.** Research note: finite-graph walk identity and numerical checks, with no claim of mathematical priority, RH consequence, quantum speedup, or hardware execution.

## AHR-08A: single-face selection by starting corner

Let Q_d be the d-dimensional hypercube. Its Hermitian Hamiltonian has arbitrary real site potentials V_x, positive edge couplings J_ab, and magnetic U(1) phases A_ab=-A_ba. The prime-logarithm choice V_x=sum_i x_i log p_i is a useful specialization.

Pick edge e=(u,v) in coordinate direction i, oriented from u to v. For any other direction j, the target square f has corners u, v, u xor e_j, v xor e_j. Initialize the walk at x=u xor e_j, the corner away from e. This x belongs to exactly one of the d-1 squares containing e.

Add a calibrated phase delta to e. Let W_f be the product of its four edge magnitudes, and let F_f be the oriented sum of edge phases along x->u->v->(v xor e_j)->x. With

\[
P_x(t,\delta)=|\langle x|e^{-itH_{\delta}}|x\rangle|^2,
\]

the exact short-time expansion gives

\[
\boxed{P_x(t,\delta)=B_x(t)+\frac{W_ft^4}{6}\cos(F_f+\delta)+O(t^6),}
\tag{AHR-08A}
\]

where B_x has no delta dependence through fourth order.

**Proof.** Expand the diagonal return amplitude into weighted closed walks. In a bipartite hypercube, the first gauge-sensitive closed walks contain four hops, and every four-hop loop with nontrivial circulation traverses one square. Only one square contains both the probe edge e and chosen start vertex x. Its two orientations contribute 2W_f cos(F_f+delta) to (H^4)_xx. The amplitude coefficient is 2W_f/4! and its contribution to the modulus-square probability is doubled, giving W_f/6. Hermitian evolution ensures P_x(t)=P_x(-t), so the next term has even order at least t^6. QED.

Four phase offsets delta_k=k*pi/2 form the complex quadrature

\[
Z_{e,x}(t)=\frac12\sum_{k=0}^3P_x(t,\delta_k)e^{-i\delta_k},
\quad\boxed{Z_{e,x}(t)=\frac{W_ft^4}{6}e^{iF_f}+O(t^6).}
\tag{AHR-08B}
\]

The leading phase is a signed Wilson-loop curvature relative to the external phase-control reference. Background flux on the other hypercube edges may be arbitrary; overlapping cycles enter its finite-time remainder.

## AHR-08C: two-time cancellation

Define Q(t)=6Z_{e,x}(t)/(W_ft^4). Smooth finite-dimensional evolution gives Q(t)=e^{iF_f}+c_2t^2+O(t^4), with c_2 generally complex. The two-time Richardson combination

\[
\boxed{Q_R(t)=2Q(t/\sqrt2)-Q(t)=e^{iF_f}+O(t^4)}
\tag{AHR-08C}
\]

reduces the leading systematic bias using eight phase/time settings per face.

**Shot-cost constraint.** If the experiment measures independent return/no-return Bernoulli events at total B shots, the initial return probability obeys 1-kappa*t^2+O(t^4), where kappa=sum of squared incident edge couplings at x. Within the leading-harmonic four-setting model the local Cramer-Rao phase-variance bound is

\[
\boxed{\operatorname{Var}(\hat F_f)\gtrsim72\kappa/(B W_f^2t^6).}
\tag{AHR-08D}
\]

At t/sqrt2 the per-shot variance of normalized Q increases by a factor of eight. The Richardson coefficient two increases its contribution by another factor four. Independent shots should therefore be allocated at ratio B_short/B_long=sqrt(32) for leading-order variance minimization. Richardson's systematic-bias improvement carries a substantial variance cost. This conditional result applies to the stated basis-return measurement family, rather than arbitrary quantum coherent metrology.

## Three-prime cube addressability

The 3-cube has twelve edges and six square faces. Each edge belongs to two faces. At least three phase-controllable edges are needed to cover all faces, and the explicit hitting set

\[
\boxed{\{(0,1),(2,6),(5,7)\}}
\tag{AHR-08E}
\]

attains this minimum. For each selected edge, preparing the two opposite face corners selects its two incident faces separately through AHR-08A. Six face readouts therefore require **24 four-phase circuit combinations** and only three independently controlled edge locations. This is a mathematical control-count result; compiled quantum gates implementing a computational-basis edge may have high physical cost.

The six measured fluxes contain five independent gauge degrees of freedom. With coordinate oriented faces, the Bianchi compatibility equation is

\[
\boxed{\Delta_0F_{12}-\Delta_1F_{02}+\Delta_2F_{01}=0\pmod{2\pi}.}
\tag{AHR-08F}
\]

It supplies a useful consistency check.

## Reproducibility

Run python ahr08_ci.py with NumPy and SciPy. Tests use prime-logarithm vertex energies plus random detunings, random positive couplings, and arbitrary random background fluxes.

The oracle passes across seeded Q_3 and Q_4 cubes, including 24 and 96 edge/face assignments, vertex-gauge invariance, Bianchi, the three-edge minimum face cover, and a wrong-starting-corner negative control. At t=0.4 the normalized complex error drops under Richardson from 0.328332 to 0.025577 (Q_3 seed 20261123), from 0.289240 to 0.020331 (Q_3 seed 20261124), and from 0.320441 to 0.032105 (Q_4 seed 20261125).

The next gates are an explicit operator-norm remainder bound, inverse-gauge uniqueness from local readouts, a Lean kernel proof of four-hop square localization, and matched Qiskit circuit compilation under hardware noise and resource constraints. No QPU experiment was submitted.
