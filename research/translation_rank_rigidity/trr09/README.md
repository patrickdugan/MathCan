# TRR-09: the actual residue eigenvector is excluded in tame characteristic

TRR-09 proves the residue eigenvector exclusion on actual smooth short
Weierstrass curves in Lean. The main theorem starts with the concrete
weights from the interpolation reduction. Every coefficient identity used
by the degree-eight obstruction is derived from the finite subgroup.

The combined local audit passed **113 principal theorem reports**, including
**70 new reports** across ten modules. All transitive dependencies in those
reports belong to the standard set `propext`, `Classical.choice`, and
`Quot.sound`. The verifier also changes a factor of two to three in the
finite residue identity and checks that Lean rejects the resulting proof.

## The checked theorem

Let

\[
E: y^2=x^3+Ax+B
\]

be a smooth short Weierstrass curve over a field `K`. Suppose `T` has finite
odd order `N >= 19`, and the images of `2`, `3`, and `N` are nonzero in `K`.
Write `G = <T>` and `S = G \ {O}`. Let `X_G` be the set of distinct
x-coordinates in `S`, and define

\[
\Phi(X)=\prod_{v\in X_G}(X-v),\qquad
\lambda(P)=\frac{1}{2y(P)\Phi'(x(P))}\quad(P\in S).
\]

Use `lambda(O)=0` and `f_0(O)=0`, with `f_0(P)=x(P)` elsewhere. Then

\[
\boxed{\neg\exists u\in K\quad
  \sum_{Q\in S}f_0(P+Q)\lambda(Q)=u\lambda(P)
  \quad\text{for every }P\in S.}
\]

The endpoint is
`TRR08Geometry.tame_no_cyclicResidue_eigenvector` in
[`TameEigenvector.lean`](../../../experiments/trr08_geometry/TRR08Geometry/TameEigenvector.lean).
Its point type is Mathlib's `WeierstrassCurve.Affine.Point`. Finite sums run
over the actual subgroup `AddSubgroup.zmultiples T`; its cardinal is proved
equal to `addOrderOf T`.

The statement applies over any field satisfying its hypotheses, including
finite extensions. It also covers odd composite marked order at least
nineteen. In prime characteristic, the tame hypothesis means `p` does not
divide `N`.

## How the two coefficient hypotheses are discharged

For nonidentity `P`, put

\[
m(P)=\frac{3x(P)^2+A}{2y(P)},\qquad
a(P)=-m(P)-2y(P)\sum_{v\in X_G\setminus\{x(P)\}}
                           \frac{1}{x(P)-v}.
\]

The normalized slope `c(P,Q)` is the chord or tangent slope, with value zero
at identity and inverse pairs. The actual curve formulas prove

\[
c(P,P)+c(2P,R)=c(P,R)+c(P,P+R)
\]

for every pair of curve points, including all tangent coincidences. Pairing
`Q` with `-Q` identifies the explicit coefficient with the finite sum

\[
a(P)=-\sum_{Q\in G}c(P,Q).
\]

Summing the diagonal identity and translating the finite index gives

\[
a(2P)=2a(P)+N m(P).
\]

The residue calculation uses the actual Lagrange basis at the distinct
x-roots. Differentiating its partition of unity supplies the weighted
reciprocal identity needed to prove

\[
(M_0\lambda)(P)=b(P)\lambda(P),
\]

where `b(P)` is an explicit expression in the same reciprocal sums.
Reindexing the coordinate trace over the finite subgroup gives

\[
2b(P)-a(P)^2+N x(P)=U,
\qquad U=\sum_{Q\in G\setminus\{O\}}x(Q).
\]

Since every nonidentity residue is proved nonzero, the eigenvector premise
forces `b(P)=u`. Thus

\[
a(P)^2=Nx(P)+2u-U.
\]

For `n=(N:K) != 0`, take `c=(2u-U)/n`. The square identity and the proved
doubling law now supply every input to the existing nine-point obstruction.
That obstruction forces the short cubic's discriminant to vanish, contrary
to smoothness.

The complete finite derivation is in
[`FINITE_DERIVATION.md`](FINITE_DERIVATION.md). The proof review records the
remaining interface with the coordinate-polynomial model.

## Modules and audit contract

| New module | Principal contribution | Reports |
|---|---|---:|
| `NormalizedSlope` | Actual chord, tangent, negation and rotation formulas | 14 |
| `DiagonalSlope` | Diagonal slope cocycle with every degenerate case included | 2 |
| `FiniteSlopeAverage` | Finite averaging and cyclic subgroup cardinal | 15 |
| `LocalCoefficient` | Explicit reciprocal-root formula equals the finite slope sum | 6 |
| `BarycentricResidue` | Finite Lagrange identities at a node | 7 |
| `TraceCoefficient` | Translation trace and `2b-a^2+Nx=U` | 7 |
| `ExplicitObstruction` | Doubling for the constructed coefficients | 6 |
| `CyclicCoefficient` | Odd cyclic order supplies the two-point x-fibres | 2 |
| `ResidueEigenvector` | Original residue weights, matrix row and forced square identity | 9 |
| `TameEigenvector` | Actual residue eigenvector exclusion | 2 |
| **New total** | | **70** |
| **Including the TRR-08 contract** | | **113** |

The machine-readable declaration list is explicit in
[`verify_formalization.py`](verify_formalization.py). The verifier checks
the pinned Lean version and installed Mathlib commit before building both
projects. Each source is then compiled directly and its exact report set is
checked. The receipt records SHA-256 hashes for every source and both
verifier scripts.

## Exact finite controls

The independent Python implementation reconstructs every smooth short
model over the prime fields `5, 7, 11, 13, 17, 19`. It enumerates every
rational point triple and each distinct odd cyclic subgroup in those models.

| Checked quantity | Count |
|---|---:|
| Smooth short models | 942 |
| Full slope-cocycle triples | 5,740,416 |
| Distinct odd cyclic subgroups | 1,229 |
| Checks of each coefficient pairing, Lagrange, residue, trace and doubling identity | 8,860 |
| Subgroups whose order is divisible by the characteristic | 53 |

The finite checks cover identity points, inverse pairs, zero total sums and
nonvertical tangents. Their coverage is recorded in
[`finite_bridge_receipt.json`](finite_bridge_receipt.json). Running Python
with assertions disabled is rejected. The universal proof of the diagonal
identity is supplied by Lean; the full three-variable cocycle in this
control sweep remains a finite empirical check.

## Remaining formal obligations

The endpoint already quantifies over the actual residue weights. Connecting
it to the complete degree statement still requires the geometric evaluation
image and the coordinate-polynomial interface. A finite Lagrange route to
the next lemma is given in
[`NEXT_EVALUATION_LEMMA.md`](NEXT_EVALUATION_LEMMA.md).

Passage from a generalized Weierstrass equation to short form must also be
formalized with the degree bound preserved. The argument in characteristic
dividing the marked order still uses written function-field and divisor
steps. Finally, the checked integral certificates for small marked orders
need an explicit Lean connection to the same interpolation statement.

The receipt therefore keeps `full_interpolation_theorem_formalized=false`
and records `actual_residue_eigenvector_exclusion_formalized=true`.
The result concerns the specified affine coordinate polynomial model.

## Reproduce

Use Lean `v4.35.0` and the committed geometry manifest. From the repository
root, after fetching the pinned Mathlib cache:

```sh
python research/translation_rank_rigidity/trr08/test_verifier.py \
  --output /tmp/trr09-legacy-controls.json
python research/translation_rank_rigidity/trr09/check_finite_bridge.py \
  --output /tmp/trr09-finite-controls.json
python research/translation_rank_rigidity/trr09/verify_formalization.py \
  --output /tmp/trr09-formalization.json
```

The shared TRR-08/09 workflow fetches the exact imported Mathlib modules and
runs these checks in public CI. Its `trr09-residue-formalization` artifact
contains the commit identifier, receipts and full direct compiler logs,
including the rejected mathematical mutation.
