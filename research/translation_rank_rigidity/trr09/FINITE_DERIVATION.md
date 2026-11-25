# Finite formulas for the local coefficients

Let `K` have characteristic different from two and three, let
`E : y² = x³ + A*x + B` be smooth, and let `G` be a finite subgroup of odd
order `N`. Put `S = G \ {O}`. Write `X` for the distinct x-coordinates in
`S`, so `|X| = (N-1)/2`, and set

\[
F(U)=U^3+AU+B,\qquad J(U)=3U^2+A,\qquad
\Phi(U)=\prod_{v\in X}(U-v),\qquad D_v=\Phi'(v).
\]

Every `D_v` is nonzero. Nonidentity subgroup points have nonzero
y-coordinate because the subgroup has odd order.

## The coefficient is a finite slope sum

Let `c(P,Q)` be the actual chord or tangent slope when `P`, `Q` and
`P+Q` are nonidentity. Set its value to zero at identity and inverse
pairs. Fix `P=(a,b)` in `S` and write

\[
\ell=\frac{J(a)}{2b},\quad
S_1=\sum_{v\in X\setminus\{a\}}\frac1{a-v},\quad
S_2=\sum_{\{v,w\}\subset X\setminus\{a\}}
                         \frac1{(a-v)(a-w)}.
\]

For `Q=(v,w)` with `v ≠ a`, the ordinary secant formula gives

\[
c(P,Q)+c(P,-Q)=\frac{2b}{a-v}.
\]

The terms at `O` and `-P` vanish, while the term at `P` is `ℓ`.
Consequently the explicit local coefficient is

\[
\boxed{a_P=-\ell-2bS_1=-\sum_{Q\in G}c(P,Q).}
\tag{1}
\]

This equality uses finite inversion pairing. A version convenient for
formalization first sums over the actual points outside `{O,P,-P}`:

\[
a_P=-\ell-b\sum_{Q\in G\setminus\{O,P,-P\}}
                         \frac1{x(P)-x(Q)}.
\]

The x-coordinate fibres have exactly two points, which recovers (1).

## Averaging the slope cocycle

The chord geometry gives the normalized diagonal slope identity

\[
c(P,P)+c(2P,R)=c(P,R)+c(P,P+R).
\tag{2}
\]

Summing (2) over `R∈G` and translating the final sum by `P` gives

\[
N c(P,P)-a_{2P}=-2a_P.
\]

Thus

\[
\boxed{a_{2P}=2a_P+N\frac{J(x(P))}{2y(P)}.}
\tag{3}
\]

The finite sum argument uses the image of the integer `N` in `K` and
never divides by it, so (3) includes matching characteristic. The Lean
geometry module proves (2) directly on actual curve points. The finite
controls also check the full identity
`c(P,Q)+c(P+Q,R)=c(Q,R)+c(P,Q+R)` on their enumerated instances.

## The residue ratio from finite Lagrange interpolation

Define

\[
\lambda_Q=\frac1{2y(Q)D_{x(Q)}},\qquad
f_0(O)=0,\qquad f_0(Q)=x(Q)\quad(Q\ne O).
\]

For a pair `Q,-Q` whose common x-coordinate is `v ≠ a`, the addition
formula gives

\[
x(P+Q)-x(P-Q)=\frac{-4b\,y(Q)}{(a-v)^2}.
\]

Their contribution to `(M₀λ)_P` is therefore
`-2b/((a-v)²D_v)`. The pair `P,-P` contributes `x(2P)/(2bD_a)`.
Dividing by `λ_P` yields

\[
\frac{(M_0\lambda)_P}{\lambda_P}
=x(2P)-4b^2D_a\sum_{v\ne a}\frac1{(a-v)^2D_v}.
\tag{4}
\]

The Lagrange identity

\[
\frac1{\Phi(U)}=\sum_{v\in X}\frac1{D_v(U-v)}
\]

is a finite rational identity: after multiplication by `Φ`, both sides
are polynomials of degree at most `|X|-1` agreeing at every root.
Expand at `U=a+ε`. The coefficient of `ε` gives

\[
\boxed{D_a\sum_{v\ne a}\frac1{(a-v)^2D_v}=S_2-S_1^2.}
\tag{5}
\]

This coefficient computation can equivalently be performed by twice
differentiating the multiplied polynomial identity. It involves ordinary
one-variable polynomials.

Since `x(2P)=ℓ²-2a`, equations (4) and (5) give the explicit second local
coefficient

\[
\boxed{b_P:=\frac{(M_0\lambda)_P}{\lambda_P}
       =\ell^2-2a+4b^2(S_1^2-S_2).}
\tag{6}
\]

## The square identity from the finite coordinate trace

Set `U_G = ∑_{R∈S} x(R)`. Translation by `P` maps
`G \ {O,-P}` bijectively onto `G \ {O,P}`. For each other pair,
the short Weierstrass equation and the addition formula give

\[
x(P+Q)+x(P-Q)
=2a-\frac{2J(a)}{a-v}+\frac{4F(a)}{(a-v)^2}.
\tag{7}
\]

Sum (7), include `x(2P)`, and use
`∑_{v≠a}1/(a-v)² = S₁²-2S₂`. The result is

\[
U_G=\ell^2+(N-4)a-2J(a)S_1+4F(a)(S_1^2-2S_2).
\tag{8}
\]

Substitution of (1) and (6), using `2bℓ=J(a)` and `b²=F(a)`, gives

\[
\boxed{2b_P-a_P^2+N x(P)=U_G.}
\tag{9}
\]

In particular, the short-model constant called `C₀` in the earlier
logarithmic-derivative derivation is zero. Under `M₀λ=uλ`, equations
(6) and (9) become

\[
a_P^2=Nx(P)+2u-U_G.
\]

When `n=(N:K) ≠ 0`, choose `c=(2u-U_G)/n` to obtain the exact square
hypothesis used by `TRR08Geometry.tame_coefficient_exclusion`.

## Verification boundary

This document supplies the finite mathematical derivation. Its finite
controls reconstruct point addition, slopes, subgroup roots and residue
weights directly over the listed prime fields. The implementation lives
in `check_finite_bridge.py`; `finite_bridge_receipt.json` records every
coverage count and source hash.

The corresponding Lean modules have passed kernel checks with only
`propext`, `Classical.choice` and `Quot.sound` in their axiom reports:

| Source module | Declaration in namespace `TRR08Geometry` |
| --- | --- |
| `LocalCoefficient` | `localCoefficient_eq_slopeCoefficient` |
| `DiagonalSlope` | `normalizedSlope_diagonal` |
| `BarycentricResidue` | `BarycentricResidue.finite_residue_identity` |
| `TraceCoefficient` | `localSecondCoefficient_relation` |
| `ResidueEigenvector` | `residueMatrixRow_eq_localSecondCoefficient` |
| `ResidueEigenvector` | `residue_eigenvector_explicit_square` |
| `TameEigenvector` | `tame_no_cyclicResidue_eigenvector` |

The residue-square theorem takes the concrete row equation as its premise.
Its proof derives the finite residue and trace identities inside Lean. The
final tame theorem composes it with the proved coefficient doubling law and
the earlier nine-point obstruction.

The finite scans calibrate signs and degeneracies. The kernel proofs
supply the universal finite identities under their stated hypotheses.
The implication from a polynomial interpolation decoder to the residue
eigenvector condition remains a separate geometric interpolation step.
