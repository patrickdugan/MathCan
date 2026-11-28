# AHR-02: prime cocycles, Clifford flux, arithmetic loop zeta, and holonomic memory

**Status (23 November 2026).** Project mathematical constructions, derivations, and finite-matrix checks. Existing ingredients include magnetic hypercubes, Clifford systems, twisted group algebras, weighted Ihara zeta functions, and SU(2) holonomy. No claim that the general ingredients are new, or that any construction proves RH, yields a complexity separation, or diagnoses consciousness.

## 1. Prime exponent geometry and its cocycle

Unique prime factorization gives `Q_{>0}^× ~= direct_sum_p Z`. For a finite prime set S, the squarefree register is the cube `{0,1}^d`, with energy `E(x)=sum_i x_i log(p_i)`. Its mixed discrete derivative vanishes on any face: `Delta_i Delta_j E=0`. Therefore any gauge potential constructed as a gradient of this additive arithmetic energy is flat.

For general integer exponent vectors `a,b in Z^d`, choose antisymmetric real matrix Theta and set

`omega(a,b)=exp(i sum_{i<j} Theta_ij a_i b_j)`.

Bilinearity verifies `omega(a,b)omega(a+b,c)=omega(b,c)omega(a,b+c)`. Associative projective generators then obey `U_i U_j = exp(i Theta_ij) U_j U_i` for i<j. The twisting lives in a multiplier (group 2-cocycle); the underlying rational numbers still multiply commutatively. The continuous integer exponent model is a version of a noncommutative torus. Restricting to a finite squarefree hypercube introduces boundaries and makes the directed hopping formulation more concrete.

Take the Landau gauge `A_i(x)=sum_{j<i} Theta_{ji} x_j`. The oriented flux of every i-j square is Theta_ij. The same convention yields a Hermitian finite graph Hamiltonian with `H_{x+e_i,x}=J_i exp(i A_i(x))` and the conjugate reverse edge. A change `H -> G H G†` with G diagonal only changes vertex phases, leaving all site-basis transition probabilities invariant.

### Gauge versus entanglement caution

Arbitrary vertex gauge transformations need not be tensor products of local qubit phase gates. For the zero-flux Hamiltonian `H0=J(X_1+X_2)`, let `G=CZ=diag(1,1,1,-1)`. It has zero plaquette flux after conjugation, and all site probabilities are unchanged; nevertheless the state `G exp(-itH0)|00>` has concurrence exactly `sin^2(2Jt)` even though the original factorized evolution has zero concurrence. Thus concurrence is an encoding- and gauge-convention-sensitive observable under this broad graph gauge group. The earlier AHR-01 short-time concurrence prediction is valid in the fixed prime-qubit Landau gauge. Use return probabilities, spectral moments, and Wilson loops as the primary gauge-invariant diagnostics.

## 2. Uniform pi flux produces a Clifford flat band

Let `Gamma_i=(prod_{j<i} Z_j) X_i` on d qubits. They are Hermitian involutions and anticommute in pairs. They coincide with the hopping terms of a hypercube with pi flux through every square. The kinetic operator `D_d=J sum_i Gamma_i` satisfies exactly `D_d^2=d J^2 I`.

Its spectrum is `+sqrt(d) J` and `-sqrt(d) J`, each `2^(d-1)`-fold degenerate. With initial `|0^d>`, the exact return is `cos^2(sqrt(d) J t)`. The zero-flux kinetic operator `J sum_i X_i` has return `cos^(2d)(Jt)`. Tests for d=2..6 reproduce all identities numerically to floating-point precision. This is a solvable Clifford limit and by itself offers no hard-to-simulate quantum computation.

Arithmetic detuning adds `V=sum_i (log p_i) N_i`. Moving to the interaction picture gives an exact quasiperiodic drive:

`H_I(t) = J sum_i (prod_{j<i} Z_j) [cos(t log p_i) X_i + sin(t log p_i) Y_i]`.

The functions `log p_i` are rationally independent over Q. The nested time-ordered commutators produce Clifford bivectors and higher operators, giving a concrete arena for resonance and persistent-state diagnostics. This is a proposed direction for dynamical modeling, not evidence of computational complexity gains.

## 3. Full exact two-prime spectral theorem

Use two primes with `a=log p`, `b=log q`, equal edge coupling J, and plaquette holonomy phi. Set `c=(a+b)/2` and `s=2J^2+(a^2+b^2)/4`. The characteristic polynomial of the centered operator K=H-cI is

`det(lambda I - K) = lambda^4 - 2s lambda^2 + (a^2-b^2)^2/16 + 4J^4 sin^2(phi/2)`.

Consequently, with `r_phi=sqrt(a^2 b^2/4 + J^2(a^2+b^2)+4J^4 cos^2(phi/2))`, all four eigenvalues are

`E=c +/- sqrt(s +/- r_phi)`,

with the signs independent. The lower positive centered energy should be computed stably by `sqrt(k/(s+r_phi))` with `k=(a^2-b^2)^2/16+4J^4 sin^2(phi/2)` to avoid subtractive cancellation when k≈0. The formula was checked for 20 tuples of a,b,J,phi, maximum absolute error 1.78e-15.

At pi flux, `K` anticommutes with `Y_1 X_2`, giving an explicit chiral symmetry. More generally its even characteristic polynomial exhibits spectral symmetry about c. The flux changes the constant coefficient only.

## 4. Gauge curvature and energetic interaction have different small-time onset

Add energetic interaction `delta N_x N_y`. In the fixed qubit gauge and with initial `|00>`, pure flux gives

`C_{phi,0}(t)=2 J^2 abs(sin(phi/2)) t^2+O(t^3)`.

For phi=0, pure energetic interaction gives

`C_{0,delta}(t)=(2/3)J^2 abs(delta) t^3+O(t^4)`.

For a *family of constant-flux experiments*, each of duration t but with flux chosen as `phi=kappa t`, the signed two-amplitude determinant begins

`det(psi amplitudes)=i J^2 (delta/3-kappa/2)t^3+O(t^4)`.

Therefore the choice `kappa=2 delta/3` suppresses the cubic term. Numerically with `J=.9,delta=.41,a=log 2,b=log 3`, the concurrence suppression ratio grows from 20.8 at t=.12 to 338 at t=.0075. The parameter phi is constant *during* each t-duration experiment: this is not the same as a time-ramped phi(s)=kappa s drive.

## 5. Fourth spectral moment counts gauge-threaded faces

Let H_F be hopping on the d-hypercube with constant edge magnitude J, arbitrary diagonal energies, and oriented flux F_f around each square face. Let H_0 have the same energies and all edge phases gauged to zero. The first three trace moments agree. The first flux-dependent moment is exactly

`Tr H_F^4 - Tr H_0^4 = 8 J^4 sum_{square faces f} (cos F_f-1)`.

Each undirected face contributes eight oriented four-step closed walks (four starting corners times two orientations). Any walk using fewer than four hopping steps either backtracks or has no cycle, and is flux-insensitive. In the d-dimensional cube the number of faces is `choose(d,2)2^(d-2)`. The d=3 instance has six faces and five independent loop fluxes. Their six oriented phases obey one discrete Bianchi constraint.

The high-temperature trace `Z_F(beta)=Tr exp(-beta H_F)` obeys

`Z_F(beta)-Z_0(beta)=(beta^4 J^4/3) sum_f(cos F_f-1) + O(beta^5)`.

The leading difference in the probability of return to the origin is `J^4 t^4/6 sum_{f incident to origin}(cos F_f-1)+O(t^6)`, with the same hopping-energy assumptions. A random-flux 3D example with `(log2, log3, log5)` site energies gave predicted `Delta Tr H^4=-3.752072529002026` and observed `-3.752072529002021`.

## 6. A bridge to Ihara graph zeta and Dirichlet L-pairs

Consider a directed, nonbacktracking 4-cycle with total metric length `L` and loop phase phi. Its two orientations contribute `e^{-s L+i phi}` and `e^{-s L-i phi}`. If B_s is the weighted nonbacktracking transfer matrix, then

`det(I-B_s) = (1-e^{-sL+i phi})(1-e^{-sL-i phi})`.

This is a graph-zeta Euler factor:

`zeta_C(s,phi) = 1/[1-2e^{-sL}cos phi+e^{-2sL}]`.

For a disjoint union of cycles indexed by primes, set each metric loop length `L_p=log p`. Given a Dirichlet character chi and `chi(p)=exp(i phi_p)` for p not dividing its conductor, the product of such factors over a finite prime set S is *exactly*

`prod_{p in S} zeta_C(s,phi_p) = L_S(s,chi) L_S(s,conj(chi))`,

where L_S denotes the truncated Euler product. The reciprocal edges force conjugate phase pairing. Thus an undirected Hermitian loop ensemble naturally encodes an L-function times its conjugate-character partner; orientation-sensitive/chiral dynamics are required to isolate a single factor directly from this construction.

This is an exact engineered identity, not a new representation of analytic continuation or a discovery of zeta zeros. It merely relocates the chosen prime factors into loop lengths and phases. In a numerical test, five disjoint cycles assigned the order-four character mod 5 reproduced their paired Euler product at `s=2.1+0.6i` within 5e-16.

A separate identity for the zero-hopping squarefree arithmetic register is `Tr exp(-s V)=prod_{p in S}(1+p^{-s})`. As S grows over all primes it becomes `zeta(s)/zeta(2s)` in `Re(s)>1`. Keep this fermionic partition function distinct from the graph-zeta construction.

### Critical-line normalization trap and exact finite poles

A single prime-labelled graph-zeta cycle has inverse determinant `(1-p^(-s) exp(i phi))(1-p^(-s) exp(-i phi))`. Its zeros occur when `s=i(±phi+2 pi k)/log p`, with real part zero. The finite graph-zeta product has poles on this imaginary axis and no zeros. Replacing `s` with `s-1/2` mechanically relocates those poles to `Re s=1/2`; that is a choice of normalization, not an RH mechanism. Any genuine arithmetic-spectral program must produce the correct analytic continuation and functional equation and distinguish zeta zeros from encoded local poles.

### Prime-logarithm recurrence and resource scaling

The frequencies `log p_i` are linearly independent over the rationals: `sum_i k_i log p_i=0` with integers k_i implies `prod_i p_i^(k_i)=1`, hence every k_i=0 by unique prime factorization. The diagonal arithmetic unitary `exp(-it V)` is therefore quasiperiodic for a finite prime set.

Dirichlet simultaneous approximation supplies a quantitative (loose) recurrence guarantee. For `Q>=2`, some integer `1<=t<=Q^d` has every fractional part `||t log p_i/(2 pi)||<=1/Q`. Consequently `||exp(-it V)-I||_op <=2 pi d/Q` on the squarefree register. Choosing `Q=ceil(2 pi d/epsilon)` gives a recurrence within epsilon at an integer time at most `Q^d`. The guarantee grows exponentially in the number of prime directions, so recurrent spectral phases alone establish no efficient memory or computation scaling.

## 7. Non-Abelian holonomy becomes an order memory

Abelian loop phases commute, so completing loops A and B in different orders produces the same U(1) phase. A two-dimensional degenerate internal subspace permits SU(2) loop actions.

Let `W_A=exp(i alpha X)` and `W_B=exp(i beta Z)` act on an ancilla qubit that remains attached to the walker as the walker returns to the same graph vertex. The operator commutator is

`W_A W_B-W_B W_A=2i sin(alpha)sin(beta)Y`.

The gauge-invariant trace of the group commutator is

`(1/2)Tr(W_A W_B W_A^† W_B^†)=1-2 sin^2(alpha)sin^2(beta)`.

For ancilla initial `|0>`, two loop orders give pure-state trace distance

`D(|AB0>,|BA0>)=abs(sin(2 alpha)sin beta)`.

Choosing `alpha=pi/4`, `beta=pi/2` gives distance 1: the loop orders yield orthogonal ancilla states, distinguishable perfectly with a Y-basis measurement. This is a specific finite-state order memory, not evidence of subjective consciousness. Non-Abelian Wilczek-Zee holonomies have an established experimental literature, including synthetic SU(2) fields and shape-space holonomic gates.

The connection to Riemann ellipsoid mechanics becomes an actual derivation only after finding an appropriate family of stable normal modes in a rotating-fluid Hamiltonian, computing its (possibly non-Abelian) adiabatic connection, and showing its Wilson loops implement the intended rotations. Until then the fluid analogy remains a mathematical inspiration.

## 8. Research gates

- **AHR-02A, exact mathematics:** Prove the hypercube fourth-moment face law using closed walks or a Lean finite-graph theorem, and prove the even characteristic polynomial for the two-prime arithmetic square. The `ahr02_verify.py` script supplies numeric oracles.
- **AHR-02B, IBM experiment:** Verify flux discrimination on two qubits using return probability and the tree control; add the flux-interaction compensation schedule and three-qubit face counting only if noise budgets permit. Document the gauge issue for any entanglement claim.
- **AHR-03, memory:** Demonstrate noncommuting SU(2) loop order as a separate ancilla protocol, with loop-order reversal, zero-curvature, and matched conventional gate controls. Measure persistence and robustness over delays rather than naming it consciousness.
- **AHR-04, RH/GRH contact:** Use primitive loop zeta and Dirichlet-character phases to inspect trace-formula analogues, with explicit convergence, analyticity, functional-equation, and uniform resource tests. Engineering a finite Euler product alone says nothing about the critical line.

## Verification

Run `python ahr02_verify.py` with NumPy and SciPy. Checks cover cocycle associativity, d=2..6 Clifford spectra, full two-prime spectral formula, 3D fourth-moment face law, gauge-invariant site probabilities, a zero-flux entanglement counterexample, cubic energetic entanglement, its flux compensation, the finite squarefree Euler product, finite Dirichlet L-pair loop zeta, and SU(2) order memory. Full machine-readable receipts: `ahr02_validation.json`.

## Prior literature

- Jia and Verbaarschot, *Chaos on the hypercube* (2020), https://link.springer.com/article/10.1007/JHEP11(2020)154
- Matsuura and Ohta, *Kazakov-Migdal model on the graph and Ihara zeta function* (2022), https://link.springer.com/article/10.1007/JHEP09(2022)178
- Khalkhali, *Basic Noncommutative Geometry*, twisted group algebras, https://www.math.uwo.ca/faculty/khalkhali/files/BNCG_1sted.pdf
- Sugawa et al., *Wilson loop and Wilczek-Zee phase from a non-Abelian gauge field* (2021), https://www.nature.com/articles/s41534-021-00483-2
- *Non-Abelian geometric phases in triangular structures and universal SU(2) control in shape space* (2026), https://journals.aps.org/pra/abstract/10.1103/wk9v-xp4l
- Mokhtari et al., *Bifurcations of Riemann Ellipsoids* (2026), https://epubs.siam.org/doi/10.1137/25M1775300