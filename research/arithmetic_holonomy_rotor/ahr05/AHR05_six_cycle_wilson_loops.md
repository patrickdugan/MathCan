# AHR-05: Sixth-cycle Wilson loops and arithmetic cycle energies

**23 November 2026.** A follow-on to AHR-04. Exact finite-graph combinatorics and seeded matrix checks. Uses familiar closed-walk and discrete-gauge constructions; the claims here concern their arithmetic-hypercube specialization.

## 1. Mixed spectral derivatives isolate a simple cycle

Let G be a finite simple graph with arbitrary real site energies V_x, positive edge magnitudes J_e, and oriented U(1) edge phases A_xy=-A_yx. Define the Hermitian magnetic hopping Hamiltonian H as in AHR-04. Fix a simple undirected cycle C with ℓ distinct edges, ordered consistently around its boundary. Let W_C be the product of those ℓ edge magnitudes and Φ_C their oriented phase sum.

For a function of the edge magnitudes, define D_C as the ℓ-fold mixed finite difference toggling each marked edge independently between zero and its specified magnitude. Every unmarked edge and all site energies remain fixed.

**Theorem AHR-05A.** For any simple cycle of length ℓ≥3,

\[
\boxed{D_C\mathrm{Tr}(H^\ell)=2\ell W_C\cos\Phi_C,}\tag{1}
\]

\[
\boxed{D_C\mathrm{Tr}(H^{\ell+1})
=2(\ell+1)W_C\left(\sum_{x\in C}V_x\right)\cos\Phi_C.}\tag{2}
\]

**Proof.** In a length-ℓ closed-walk expansion, a term surviving the ℓ marked edge differences must contain every edge of C. It therefore traverses exactly those ℓ edges once. The possible closed walks are the two orientations of C, with ℓ choices of initial vertex, producing 2ℓW_CcosΦ_C. At length ℓ+1, a surviving closed walk can contain the cycle's ℓ marked hops and one diagonal stay. A single additional off-cycle hop would give two odd-degree endpoints and cannot form a closed walk. For each stay vertex, both orientations and all ℓ+1 cyclic placements contribute, giving 2(ℓ+1) W_C ΣV_x cosΦ_C. QED.

If cosΦ_C is nonzero, the quotient gives a cycle-local energy mean:

\[
\boxed{\frac{D_C\mathrm{Tr}(H^{\ell+1})}{D_C\mathrm{Tr}(H^\ell)}
=(\ell+1)\overline V_C,\qquad
\overline V_C=\frac1\ell\sum_{x\in C}V_x.}\tag{3}
\]

In particular, the fourth/fifth moment face theorem of AHR-04 is the ℓ=4 case. The sixth/seventh moment case isolates a hexagon. Phase probes at offsets 0 and +π/2 recover both cosine and sine by the same method, now using 2^(ℓ+1) on/off configurations for both settings.

## 2. Count of simple six-cycles in the prime hypercube

**Theorem AHR-05B.** The d-dimensional cube has

\[
\boxed{N_6(Q_d)=16\binom d3\,2^{d-3},\qquad d\ge3.}\tag{4}
\]

**Proof.** Every coordinate flips an even number of times in a closed path. A simple six-cycle must flip three distinct directions twice each: two coordinates support only four vertices and cannot form a six-cycle. Hence every six-cycle belongs to a unique induced three-dimensional cube on three chosen directions, with all other bits fixed.

For Q_3, fix a root and count directed rooted simple six-cycles. There are three choices of first direction i and two of second direction j, both different. Let k be the remaining direction. The third step i permits one valid completion, and third step k permits three, giving 3×2×4=24 rooted directed cycles. Count eight possible roots and divide by twelve for six starting vertices and two orientations: 8×24/12=16. Choose the coordinate triple and remaining fixed bits to obtain (4). QED.

For d=3,4,5 the exact counts are 16, 128, 640.

## 3. Two-face and three-face Wilson loops

The Q_3 cube has six square faces. Twelve unordered pairs of adjacent faces each bound a distinct simple six-cycle, accounting for 12 of the 16. The remaining four are skew hexagons dividing the surface of the cube into two patches of three faces.

The discrete Stokes theorem gives

\[
\Phi_C=\sum_{f\in S}\epsilon_f F_f\pmod{2\pi}
\]

for either oriented face patch S bounded by a hexagon. The Bianchi identity makes the two choices consistent.

For a two-face patch, orient its face phases as α and β so that the hexagon phase is α+β. The fourth-order face probes recover cosα and cosβ, while the sixth-order hexagon probe recovers cos(α+β). Thus

\[
\boxed{\cos(\alpha+\beta)-\cos\alpha\cos\beta
=-\sin\alpha\sin\beta.}\tag{5}
\]

The six-edge observable determines a **relative chirality correlation** that the two individual cosine measurements leave ambiguous. As before, global reversal of every phase leaves unprobed real spectral data unchanged.

## 4. A three-prime skew-hexagon invariant

Label the eight cube vertices by n=2^x3^y5^z and set V_{xyz}=x log2+y log3+z log5. Every skew hexagon bounding a three-face patch omits two antipodal cube vertices. Since the total energy over the eight vertices is 4(log2+log3+log5) and the antipodal pair sums to (log2+log3+log5), the sum over the six hexagon vertices is

\[
\sum_{x\in C}V_x=3\log(2\cdot3\cdot5)=3\log30.
\]

Insert this in (3) with ℓ=6:

\[
\boxed{\frac{D_C\mathrm{Tr}(H^7)}{D_C\mathrm{Tr}(H^6)}
=\frac72\log30=11.904190835817545.}\tag{6}
\]

The numerical oracle obtained 11.90419083585665, an error of approximately 3.91×10^−11. For general three primes p,q,r, replace 30 with pqr. The prime-logarithm energies are imposed by design; generic matched site energies can reproduce these observations.

## 5. Verification and next questions

The seeded numerical suite enumerates all simple six-cycles for d=3,4,5; classifies the 12 two-face and four three-face loops in Q_3; verifies oriented Stokes phases for random edge gauge fields; compares sixth-order 64-setting mixed differences against 12 W_C cosΦ_C; uses π/2 phase offsets for signed holonomy; and verifies the three-prime sixth/seventh-moment ratio. All are exact finite-dimensional predictions with floating-point checks. No quantum hardware was used.

Research gates: Lean proof of the marked-cycle lemma and the 16*C(d,3)*2^(d-3) count; isolation of length-six signals without 64 separate edge settings; resource scaling with dimension d; magnetic spectral and arithmetic controls; eventually deriving holonomy from actual rotating-fluid modes instead of a surrogate oscillator. These results do not establish RH, polynomial-time breakthroughs, or machine consciousness.
