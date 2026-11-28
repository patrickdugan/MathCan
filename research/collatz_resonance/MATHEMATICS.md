# COL mathematics: proofs and model assumptions

## The map and finite core

Let d>0, d=1 mod 4. Define S_d(n)=n/2 for even n, 3n+d for n=1 mod 4, and n+d
for n=3 mod 4. For odd n write c(n)=3 or1 respectively, a(n)=v_2(c(n)n+d), and

\[
F_d(n)=\frac{c(n)n+d}{2^{a(n)}}.
\]

Both numerators are divisible by 4. Therefore a(n)>=2 and
`0<F_d(n)<=(3n+d)/4`. Above d this is strictly below n; at or below d it is
at most d. An odd orbit descends to the closed core {1,3,...,d}. A finite
functional graph eventually repeats. Initial even states reach an odd state
through halving. The Lean module proves positivity, oddness, the bound,
closure, descent and eventual entry for the actual F_d, implemented by
recursively removing all factors of two. The pigeonhole step is a written
finite-graph argument here.

Every S_d cycle contains an odd member, so contracting its even stretches
gives an F_d cycle and expansion reverses that construction. If r is its odd
length, u counts branches with c=3, and A=sum a(n), the full period is r+A.
Consequently A>=2r>=2u.

## Gcd conservation and the exact lattice

Assume gcd(d,6)=1. For c in{1,3}, gcd(cn+d,d)=gcd(n,d), and halving preserves
this gcd. Thus g=gcd(n,d) stays constant on an orbit. Composing a cycle gives

\[
2^A n_0=3^u n_0+dB
\]

for a positive integer B. Divide by g and cancel the unit n_0/g modulo d/g:

\[
\boxed{2^A\equiv3^u\pmod{d/g}.}
\]

Canceling n_0 modulo d requires a unit cycle. Every reference row is checked
using its reduced modulus.

For any m>=1 coprime to 6 define

\[
\Lambda_m=\{(u,A)\in\mathbb Z^2:2^A3^{-u}=1\pmod m\}.
\]

Let L=ord_m(2), h be the order of3 in `<2,3>/<2>`, and choose0<=s<L with
3^h=2^s. Then `Lambda_m = Z(h,s)+Z(0,L)`. Indeed every relation has h|u;
writing u=hv leaves L|(A-sv). Substitution proves the converse. The lattice
index is hL=|<2,3>|. For m=1 use h=L=1,s=0. `arithmetic.py` implements this
general group computation and a squarefree CRT version when2 is primitive
at each prime factor.

At d=29*53*269*389, modular powers verify that2 is primitive locally and
log_2(3) equals5,17,109,271. Thus

\[
A\equiv5u\ (28),\quad A\equiv17u\ (52),\quad
A\equiv109u\ (268),\quad A\equiv271u\ (388).
\]

Compatibility forces u even. CRT gives `u=2v` and
`A=885958v mod2365636`. In coordinates (u,A-6u), the vectors
(1522,-1354),(2024,1308) lie in the lattice and have determinant4,731,272,
equal to its index. They therefore form a basis. Their sum is (3546,-46),
the observed dominant branch family. The finite search u<=10000 and
|A-6u|<=100 returns exactly(3546,21230),(7092,42460).

These are necessary arithmetic conditions. A legal closed branch word also
has to realize its affine offset and satisfy the residue rules at every step.

## Absolute signs with k auxiliary primes

Fix distinct seed primes q_1,...,q_k>3. For each i choose p_i=1 mod 24 with
Legendre symbol(q_j/p_i) negative exactly for j=i. Existence follows by
choosing a nonzero square or nonsquare residue for p_i modulo each q_j, then
combining those choices with p_i=1 mod 24 by CRT. The combined class is a unit
class, so Dirichlet's theorem supplies infinitely many primes. Choose them
distinct and different from the seeds. Since p_i=1 mod 4, quadratic
reciprocity transfers(p_i/q_j) to(q_j/p_i).

Both 2 and 3 are quadratic residues at each p_i. For d=product p_i every branch
preserves each individual symbol(n/p_i), including zero. The2^k subset
products of the seed primes have distinct vectors and reach distinct cycles.
CRT realizes every ternary sign vector on positive starts, each of which
eventually reaches a cycle. Hence

\[
C(d)\geq3^k,\qquad C_{\mathrm{unit}}(d)\geq2^k.
\]

The construction changes the manuscript's auxiliary congruence class from
5 mod 24 to1 mod 24 and uses k primes. Their sizes remain a separate problem.
For seeds(5,7,11), the bounded search returns (1873,1321,1009), giving
d=2496501097. The checked signs certify eight prescribed basins and at
least 27 cycles. The complete graph for that larger d has not been enumerated.
This is a written deduction using the classical sources in `SOURCES.md`.

## Periodic observers and sampling measures

Manuscript Theorem4 states that, for d=1 mod 4 and gcd(d,6)=1, every periodic
forward-closed set is the inverse image of a union of<2,3>-orbits modulo d,
allowing every proposed modulus. Sufficiency follows from the residue
multipliers2^(-1),3,1. Its necessity proof removes the power-of-two part of
the label modulus by propagating full odd-modulus fibres, then uses
translation by d and invertible multipliers on gcd(d,m). The supplied paper
owns that proof. Lean checks the downstream invariant and decoder logic;
the entire all-moduli classification has not been formalized here.

The reference has32 unit quotient classes,40 with one zero prime coordinate,
18 with two zeros,4 with three and1 with four. Local base2 logarithms modulo 4,
after subtracting a reference coordinate, compute these counts. The added
generator3 has order1 if the local logs agree mod 4 on the support and order2
otherwise. The 137 cycles fill these 95 classes.

A class count acquires a predictive meaning only after choosing a sampling
measure. For state X, basin target B and observation Q, optimal decoding has

\[
\operatorname{Acc}^{*}(Q)=\sum_q\max_b\Pr(Q=q,B=b).
\]

Under uniform odd core inputs this becomes`sum_q max_b N[q,b] / |X|`. Uniform
sampling of cycles instead gives95/137, or32/55 when restricted to unit
cycles. Companion receipts specify the measure they use. At d=13,2^9=5
mod13 while F_13 has separate cycles[1] and[5,7], so a decoder of the
conserved quotient cannot identify both targets. Lean proves this general
obstruction and checks the concrete arithmetic witnesses.

## Ordered observations encode the seed

For a fixed prefix with multipliers c_j and halving counts a_j, initialize
B_0=A_0=u_0=0 and update

\[
B_{j+1}=c_jB_j+2^{A_j},\quad A_{j+1}=A_j+a_j,\quad
u_{j+1}=u_j+\mathbf1_{c_j=3}.
\]

Composition gives`2^A n_h=3^u n_0+dB`. The endpoint n_h is odd. Reduction
modulo2^(A+1) yields the exact seed decoder

\[
n_0\equiv(2^A-dB)(3^u)^{-1}\pmod{2^{A+1}}.
\]

Two seeds with the same prefix differ by a multiple of2^(A+1). Their absolute
difference on the core is at most d-1, forcing equality whenever
2^(A+1)>d-1. Since A>=2h, it suffices that2^(2h+1)>d-1. Tests replay this
decoder at h=5 for all 44,204 odd core states over the 172 admissible d<=1025.

This theorem measures the information carried by a full prefix. Learning
to decode it with bounded memory or compute is a separate research task.
Finite lookup scores also saturate for shuffled partitions with sufficiently
small cells. The recurrent-model protocol therefore needs fresh parameters,
restricted readouts and controls matched for stored information.

## The model behind slope six

For a fresh uniform odd 2-adic input, each branch has probability 1/2. Within
either branch the affine numerator divided by 4 is uniform on Z_2, so

\[
\Pr(a=k\mid c)=2^{-(k-1)}\ (k\geq2),\quad
\mathbb E a=3,\quad\operatorname{Var}(a)=2.
\]

The triple indicator t is independent of a in this one-input distribution,
with E(t)=1/2 and Var(t)=1/4. Thus E(a-6t)=0 and Var(a-6t)=11. Taking r
independent draws from this law gives variance 11r. Replacing r by 2u
motivates the band `(A-6u)^2<=22u` and the period estimate A+2u.

Selecting a finite positive-integer cycle changes the sampling distribution.
The Haar calculation supplies a model; a concentration theorem for selected
cycles remains open. COL-03 measures whether a fixed short-vector rule
predicts finite cycle populations. This split family supplies the domain of
all current deductions. The current proofs and experiments concern this split family.
