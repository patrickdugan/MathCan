# AHR-01: Arithmetic Holonomy Rotor

**Status:** Mathematical proposal plus independently reproducible finite-dimensional numerical checks. These are new constructions for this project; no priority claim about the underlying quantum-walk/Peierls-phase mathematics. No quantum hardware has been used.

## 1. Physical and arithmetic starting points

Modern Hamiltonian treatments of Riemann's rotating fluid ellipsoids involve stability of relative equilibria, modes, and bifurcations. This motivates **circulatory coupling** between arithmetic modes, without claiming that an ellipsoid is a quantum computer. An independent 2026 quantum experiment constructed a logarithmic energy spectrum to relate zeta functions to dynamical quantum phase transitions.

For any distinct primes `p,q`, label the four basis states by `n=p^x q^y` with `x,y in {0,1}`. The arithmetic energies are `E_xy = log(n) = x log(p) + y log(q)` and have identically vanishing mixed discrete curvature:

`Delta E = E_11 - E_10 - E_01 + E_00 = 0`.

Let `N_x = (I-Z_x)/2`, `N_y = (I-Z_y)/2`, with `X,Y,Z` Pauli operators. A single magnetic/rotational phase `Phi` around the plaquette defines

`H(Phi) = (log p) N_x + (log q) N_y + J X_x + J[(I-N_x) X_y + N_x(cos Phi X_y + sin Phi Y_y)]`.

Use units `hbar=1`. The `Phi` edge corresponds to the `x=1` vertical bond. The orientation convention is `00 -> 10 -> 11 -> 01 -> 00` with holonomy `exp(i Phi)`.

## 2. Proposition A: factorization and holonomy-generated entanglement

At `Phi=0`, `H(0) = h_p (tensor I) + I (tensor h_q)` with each `h_r = log(r) (I-Z)/2 + JX`. Thus `U(0,t)` is a tensor product. Any product initial state, including `|00>`, remains separable.

For `|psi(Phi,t)> = exp(-itH(Phi)) |00>`, the amplitudes at short time are

```
psi_00 = 1 + O(t^2)
psi_10 = -i J t + O(t^2)
psi_01 = -i J t + O(t^2)
psi_11 = -J^2 t^2 (1 + exp(i Phi))/2 + O(t^3).
```

The determinant of the 2x2 amplitude matrix is

`psi_00 psi_11 - psi_01 psi_10 = (J^2 t^2/2)(1-exp(i Phi)) + O(t^3)`.

Therefore the pure-state concurrence is

**`C(Phi,t) = 2 J^2 t^2 |sin(Phi/2)| + O(t^3)`**.

The coefficient is independent of the prime energies; arithmetic begins to influence the higher-order dynamics. For `Phi=0`, `C(0,t)` is **exactly zero at every time**.

## 3. Proposition B: shortest-cycle return interference

Let `P(Phi,t) = |<00|exp(-itH(Phi))|00>|^2`. The shortest gauge-sensitive closed walks on the square use four hops and come in two orientations, giving `2 J^4 cos(Phi)` in `<00|H(Phi)^4|00>`. All lower-order return moments are flux-independent. Expanding the unitary gives

**`P(Phi,t)-P(0,t) = (J^4/6) [cos(Phi)-1] t^4 + O(t^6)`**.

The probability is even in real evolution time, which removes odd orders from its Taylor expansion. For `Phi=pi`, the coefficient is `-J^4/3`.

### Closed-form zero-flux baseline

For `r in {p,q}`, set `omega_r=sqrt(J^2+(log(r)/2)^2)` and `P_r(t)=1-[J^2/omega_r^2] sin^2(omega_r t)`. Then

**`P(0,t)=P_p(t) P_q(t)`**.

This gives a no-fitting analytic baseline that can be evaluated before any simulator or quantum hardware run.

## 4. Proposition C: exact spectral shift

The only term in the four-state characteristic polynomial that depends on the loop phase is the four-step closed cycle. For all complex `lambda`,

**`det(lambda I - H(Phi)) - det(lambda I - H(0)) = 2 J^4 [1-cos(Phi)]`**.

Equivalently, `Tr H(Phi)^k = Tr H(0)^k` for `k=1,2,3`, whereas

**`Tr H(Phi)^4 - Tr H(0)^4 = 8 J^4 [cos(Phi)-1]`**.

These identities hold for arbitrary on-site energies on the square, not only logarithmic ones, provided all four hopping magnitudes equal `J`.

### Remove one edge: strict null control

Removing, for example, the `01 <-> 11` horizontal hopping leaves a tree. A diagonal unitary can eliminate all edge phases on a tree. Consequently, the probabilities of measurements in the site basis, including `P(Phi,t)`, are exactly independent of `Phi` for every `t`. The local code verifies this to machine precision.

## 5. What makes arithmetic matter?

The square has two independent curvatures:

- `Delta E = E_11 - E_10 - E_01 + E_00`, a discrete **energy curvature**. It vanishes for `log(n)` on a genuine multiplicative square.
- `Phi = sum_oriented_edges arg(J_edge) mod 2pi`, a **gauge holonomy**. It controls quantum interference around that square.

Introduce `delta` at the composite vertex (`E_11 = log(pq)+delta`) and compare the plane `(delta, Phi)`. The baseline `(0,0)` factorizes; `delta` induces an energy interaction, while `Phi` induces a gauge interaction. This separates two mathematically different sources of correlations.

Any pair of independent real frequencies can also satisfy `Delta E=0`. The first four-state experiment establishes *control of gauge flux over an arithmetic-labelled tensor-product spectrum*, not prime-specific computation. Prime-specific phenomena must be demonstrated with nontrivial arithmetic controls and scaling.

### Dirichlet generating function seed

Prepare the product-weighted state

`|psi_beta> = sum_{x,y} (p^x q^y)^(-beta/2) |xy> / sqrt((1+p^(-beta))(1+q^(-beta)))`.

For `J=0`,

`<psi_beta|e^(-it H)|psi_beta> = (1+p^(-beta-it))(1+q^(-beta-it))/[(1+p^(-beta))(1+q^(-beta))]`.

This is a **finite Euler-type product**, not `zeta(beta+it)`. In particular, this 2-qubit system provides no test of RH. Approaching the actual zeta function requires a different regulator and correct treatment of the Dirichlet series or its analytic continuation, along with scaling and precision analyses.

## 6. Exact finite-dimensional benchmarks

`p=2`, `q=3`, `J=1`; state is initially `|00>`. Evaluation: `scipy.linalg.expm`.

| t | P(0,t) | P(pi/2,t) | P(pi,t) | C(pi/2,t) | C(pi,t) |
|---:|---:|---:|---:|---:|---:|
| 0.4 | 0.7226 | 0.7193 | 0.7160 | 0.1937 | 0.2839 |
| 0.8 | 0.2591 | 0.2385 | 0.2196 | 0.5357 | 0.7722 |
| 1.0 | 0.1175 | 0.1037 | 0.0985 | 0.6761 | 0.8744 |
| 1.2 | 0.0487 | 0.0738 | 0.1281 | 0.7661 | 0.8071 |
| 1.6 | 0.0338 | 0.2085 | 0.5432 | 0.6600 | 0.2806 |
| 2.0 | 0.1945 | 0.3486 | 0.9311 | 0.4888 | 0.3141 |

### Product-formula validation

A second-order Suzuki–Trotter formula with 8 steps gives absolute return-probability errors at `t=1.6` of approximately 0.00536 for `Phi=pi/2` and 0.00957 for `Phi=pi`. At `t=0.8`, four steps have errors under 0.001 for both phases. The final QPU transpiler, qubit topology and native gates will determine whether these depths fit the actual hardware budget.

The seven non-identity Pauli terms (with the scalar `(log p + log q)/2 I` omitted as a global phase) are:

```
-(log p/2) Z_x
-(log q/2) Z_y
+J X_x
+J(1+cos Phi)/2 X_y
+J(1-cos Phi)/2 Z_x X_y
+J sin Phi/2 Y_y
-J sin Phi/2 Z_x Y_y
```

For Qiskit little-endian labels with `x=q0, y=q1` these are `IZ, ZI, IX, XI, XZ, YI, YZ` respectively.

## 7. Tail-out research problems

**AHR-02, multiplicative cube:** introduce a third prime and three independent prime-pair plaquettes. Test the discrete lattice-gauge Bianchi identity for face holonomies and characterize compatible patterns of circulations. Study whether controlled flux fields outperform fixed real hopping on *identically specified* tasks.

**AHR-03, resonant memory:** Floquet-modulate `Phi(t)` and examine frequency-selective excitation, retention of phase histories, and perturbation response. Compare with matched two-qubit and recurrent classical controls. This can test persistent state and information integration without asserting subjective experience.

**AHR-04, spectral arithmetic:** replace squarefree prime cubes with a carefully normalized integer-register Hamiltonian. Separate true arithmetic effects from generic quasiperiodic energy spectra, precision requirements, and finite-size artifacts. Examine any relation to the independently checked 2026 Alpöge–Claude Lean proof only after extracting its operative prime-sum inequality and exact constants.

**Computational complexity:** Any suggestion of a polynomial-time advantage requires a uniform algorithm, resource accounting for state preparation and measurement, and comparison against the strongest known classical method. The present experiment is a gauge-interference and entanglement demonstration.

## Reproducibility

Run `python ahr01_exact_validation.py` with NumPy and SciPy installed. It checks all three propositions, Pauli decomposition, the cycle-breaking control, and second-order Trotter errors. It writes `ahr01_ideal_predictions.csv` and `ahr01_validation.json`. No hardware access or paid service is needed.

## References

- Mokhtari, Palacián, and Yanguas, *Bifurcations of Riemann Ellipsoids* (2026), DOI 10.1137/25M1775300, https://epubs.siam.org/doi/10.1137/25M1775300
- Wei et al., *The Riemann Hypothesis manifested in dynamical quantum phase transitions*, Nature Communications 17, 8163 (July 2026), https://doi.org/10.1038/s41467-026-74935-8
- Michael Rubinstein, *Alpöge/Claude proof of the Generalized Riemann Hypothesis* (November 2026), https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/
- IBM Quantum, client-side Sampler release 0.52.0 (November 2026), https://quantum.cloud.ibm.com/docs/en/api/qiskit-ibm-runtime/release-notes