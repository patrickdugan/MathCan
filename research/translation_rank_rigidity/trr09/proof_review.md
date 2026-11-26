# TRR-09 proof review

## Endpoint and scope

`tame_cyclicResidue_eigenvector_exclusion` is a theorem about actual
Mathlib curve points and the original inverse-product residues. It assumes
a smooth short model, finite odd marked order at least nineteen, and
nonzero images of `2`, `3`, and that order in the coefficient field. Its
interpolation premise is the concrete equation `M0*lambda=u*lambda` on all
nonidentity points of the cyclic subgroup.

Every coefficient used by the final contradiction has a definition. The
square and doubling identities are proved from those definitions. The
geometry uses the supplied curve's actual group law, and all finite sums
range over its actual subgroup.

This endpoint holds over arbitrary fields with the stated hypotheses.
Extension-field exceptions in the tame residue eigenvector problem are
therefore excluded by the same theorem. The theorem also allows odd
composite marked order at least nineteen.

## Definitions checked against the original model

`affineX` is zero at the identity and the ordinary coordinate at a finite
point. Consequently `residueMatrixRow` is exactly the row of `M0` used by
the reduction with `f0(O)=0`. `subgroupResidue` is zero at the identity.
The theorem `subgroupResidue_eq_inverse_product` identifies its nonidentity
values with

\[
\left(2y(P)\prod_{v\in X_G\setminus\{x(P)\}}(x(P)-v)\right)^{-1}.
\]

There is no choice of signs for representatives in this definition. Both
`P` and `-P` occur in the subgroup sum, and the proof derives the oddness of
the residue from their coordinates. The two-point x-fibres are established
using Mathlib's equality criterion for points with the same x-coordinate.

The original explicit local coefficient has the sign
`-m(P)-2*y(P)*sum(1/(x(P)-v))`. Pairing the slope sum proves that formula.
The paired residue contribution is negative:

\[
\bigl(x(P+Q)-x(P-Q)\bigr)\lambda(Q)
=\frac{-2y(P)}{(x(P)-x(Q))^2\Phi'(x(Q))}.
\]

These signs give `2*b-a^2+N*x=U`, and the eigenvector premise then gives
`a^2=N*x+2*u-U`. Choosing `c=(2*u-U)/N` matches the previous obstruction
theorem exactly.

## Actual point geometry

The normalized slope is zero at identity and inverse pairs. At the remaining
pairs it is Mathlib's actual secant or tangent slope. The unrestricted
diagonal identity includes zero points and two-torsion. Its proof handles
the coincidences `R=P`, `R=2P`, `R=-P` and `R=-2P` before applying the generic
secant calculation.

The generic calculation comes from the chord incidence equation and the
divided cubic equation. A separate polynomial identity handles the outer
tangent. Lean checks each polynomial combination and every cancellation
uses a proved nonzero denominator.

The final application only needs the diagonal identity. The full cocycle
appears in the independent finite control sweep; the universal Lean theorem
for that stronger identity is outside this update.

## Finite interpolation and trace

`BarycentricResidue` differentiates Mathlib's Lagrange partition of unity.
At a node `a`, let `D=Phi'(a)`, let `w_v=1/Phi'(v)`, and write `S1` and `Q`
for the reciprocal sum and the sum of squared reciprocals over the other
nodes. The checked identity is

\[
2D\sum_{v\ne a}\frac{w_v}{(a-v)^2}=-(S_1^2+Q).
\]

The node map is injective on the finite index set, which proves every
cofactor value used for cancellation is nonzero. This polynomial identity
uses no field-cardinality hypothesis.

`TraceCoefficient` reindexes the actual subgroup by addition and inversion.
It removes the distinguished points `O`, `P`, and `-P`, using `P != O` and
`2P != O` to justify their distinctness. The addition formulas supply the
paired coordinate identity. This yields the coordinate trace and the
relation `2*b-a^2+N*x=U` through finite sums.

These finite identities remain valid when `N=0` in the field. The final
tame obstruction has its own nonvanishing premise, used in the choice of
`c` and the degree-eight argument. The separate matching-characteristic
argument still requires formalization.

## Verification performed

The combined verifier builds the core and the complete geometry aggregate,
then compiles all sixteen audited source modules directly. Its explicit
contract contains the 43 previous principal reports and 70 new reports.
The accepted transitive dependencies are `propext`, `Classical.choice`,
and `Quot.sound`; an earlier helper has an empty dependency list.

Raw sources are checked for admitted goals, declared mathematical axioms and
unchecked native reductions. The report parser rejects missing, additional
or duplicate declarations. The sixteen existing verifier controls pass.

A mathematical mutation changes the factor `2` in the displayed finite
residue identity to `3` while retaining its proof. Ordinary Lean compilation
rejects the altered conclusion at the final polynomial comparison. The
control checks that compilation reached the mathematical proof, and its log
is retained with the verification receipt.

The independent exact control sweep has 942 smooth models and 5,740,416
point triples. For 1,229 distinct odd cyclic subgroups it verifies each
coefficient identity at all 8,860 nonidentity subgroup points. It includes
53 subgroup instances whose order is divisible by the characteristic.

## Remaining path to the complete interpolation statement

The geometric evaluation image must be identified with the residue
hyperplane. The finite decoder reconstruction from TRR-08 can then use that
image theorem, once the coordinate-polynomial basis and its degree bound are
connected to the feature map.

For a generalized Weierstrass model, the change to short form requires a
checked coordinate transformation preserving the specified total degree in
each input pair. The matching-characteristic proof and the small-order
certificate interfaces remain separate obligations. Each is listed in the
machine-readable proof boundary.
