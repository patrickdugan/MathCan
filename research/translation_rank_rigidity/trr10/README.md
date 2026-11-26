# TRR-10: exact ordinary interpolation degree in tame odd order

TRR-10 completes the coordinate-polynomial theorem on smooth short
Weierstrass models with tame odd marked order at least nineteen. Lean checks
both the obstruction below the threshold and an explicit polynomial
construction at the threshold.

## The theorem

Let `K` be a field and let

\[
E:y^2=x^3+Ax+B
\]

be smooth. Suppose `T` has finite odd order `N >= 19`, with `2`, `3`, and `N`
nonzero in `K`. Put `G = <T>` and `S = G \ {O}`. For any `u` in `K`, define
`f_u(O)=u` and `f_u(P)=x(P)` for every nonidentity subgroup point.

For every natural number `d`,

\[
\boxed{
\begin{aligned}
&\exists\mathcal D\in K[X_1,Y_1,X_2,Y_2],\qquad
  \deg_{(X_1,Y_1)}\mathcal D\le d,\quad
  \deg_{(X_2,Y_2)}\mathcal D\le d,\\
&\mathcal D(x(P),y(P),x(Q),y(Q))=f_u(P+Q)
  \quad(P,Q\in S)
\end{aligned}
\quad\Longleftrightarrow\quad d\ge\left\lceil\frac N3\right\rceil .
}
\]

Each block degree is the ordinary total degree in that coordinate pair.
The same bound is imposed on the two blocks. The target function uses the
assigned value whenever `P+Q=O`; the inputs themselves range over `S`.

The endpoint is
[`TRR08Geometry.tame_polynomialDecoder_degree_iff`](../../../experiments/trr08_geometry/TRR08Geometry/DecoderDegree.lean).
It quantifies over an actual `MvPolynomial (Fin 4) K` and the actual subgroup
of Mathlib curve points. All residue and interpolation facts are derived
inside the proof. The theorem applies to arbitrary fields under these
hypotheses, including finite extensions, and to odd composite orders.

For example, the minimum degrees for orders `19, 23, 25, 27, 29, 31` are
`7, 8, 9, 9, 10, 11`, respectively, whenever the characteristic conditions
hold. The universal theorem covers every larger eligible order without
further order-specific elimination.

## Why lower degrees fail

Let `m=(N-1)/2` and let `X_G` contain the distinct x-coordinates of `S`.
TRR-10 proves `|X_G|=m` from the two-point fibres `{P,-P}`. Define

\[
\Phi(X)=\prod_{v\in X_G}(X-v),\qquad
\lambda(P)=\frac1{2y(P)\Phi'(x(P))}.
\]

Pairing inverse points cancels the residue sum of every function of `x`.
For the odd part, finite Lagrange interpolation gives

\[
\sum_{P\in S}\lambda(P)\bigl(p(x(P))+y(P)q(x(P))\bigr)
=[X^{m-1}]q(X),\qquad \deg q<m.
\]

The cubic equation reduces `x^a y^b` to this normal form. When
`2a+3b <= N-1`, its residue sum vanishes. An ordinary monomial of degree at
most `d` has `2a+3b <= 3d`, so every row of a block-degree-`d` decoder is
annihilated whenever `3d <= N-1`.

At a fixed nonidentity point `P`, the assigned value contributes

\[
\sum_{Q\in S}\lambda(Q)f_u(P+Q)
=(M_0\lambda)(P)-u\lambda(P).
\]

Consequently such a decoder would force `M0*lambda=u*lambda`. TRR-09's
actual residue theorem excludes this under the stated tame hypotheses.
The resulting lower bound is `d >= ceil(N/3)`.

## A polynomial at the threshold

For `P` in `S`, let `beta_P(X)` be the Lagrange basis polynomial at `x(P)`
on `X_G`. The function

\[
\beta_P(x)\left(\frac12+\frac{y}{2y(P)}\right)
\]

is one at `P` and zero at every other point of `S`. Its direct expression
can have a larger ordinary degree than needed. The proof constructs a
smaller representative using

\[
X^{j\bmod3}(Y^2-AX-B)^{\lfloor j/3\rfloor},
\]

which evaluates to `x^j` on the curve. Its ordinary degree is bounded by
`ceil(2j/3)`. Multiplication by `Y` gives the corresponding representative
for `yx^j` with degree at most `ceil((2j+3)/3)`.

Since `deg beta_P=m-1`, this yields an actual bivariate point-mass polynomial
`L_P` of total degree at most `ceil(N/3)`. The four-variable polynomial

\[
\mathcal D(X_1,Y_1,X_2,Y_2)=
\sum_{P,Q\in S} f_u(P+Q)
                 L_P(X_1,Y_1)L_Q(X_2,Y_2)
\]

has the required block bound and reproduces every table entry. Lean checks
the polynomial support and its evaluation. This upper construction also
applies to other finite odd subgroups under the hypotheses in
`exists_polynomialDecoder_of_card_le`; tame order and `N >= 19` enter through
the lower bound.

## Verification

The combined audit passed **180 principal theorem reports** across 27 source
modules. TRR-10 adds **67 reports** in eleven modules to the frozen TRR-09
contract. Every reported transitive dependency lies in the standard set
`propext`, `Classical.choice`, `Quot.sound`.

| New module | Contribution | Reports |
|---|---|---:|
| `RootCardinality` | Actual x-fibres and their cardinality | 3 |
| `CubicMonomials` | Normal forms of even and odd monomials | 6 |
| `ResidueAnnihilation` | Finite Lagrange coefficient functional | 9 |
| `PolynomialDegree` | Actual bivariate support and evaluation sums | 6 |
| `ResidueMonomials` | Weighted and ordinary monomial annihilation | 6 |
| `BlockPolynomial` | Actual four-variable rows and their residue sums | 3 |
| `TameDecoder` | Decoder implies eigenvector; degree lower bound | 7 |
| `PolynomialLift` | Ordinary-degree representatives using the cubic equation | 12 |
| `PointInterpolation` | Explicit point-mass polynomials | 4 |
| `BlockTensor` | Polynomial construction for any finite target matrix | 8 |
| `DecoderDegree` | Upper bound and exact degree iff | 3 |
| **New total** | | **67** |

The verifier checks Lean `v4.35.0`, the installed Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, source hashes and an explicit list
of declarations. It compiles every audited module directly. Three deliberate
mathematical changes must fail inside the changed theorem: replacing the
residue factor `2` by `3`, allowing monomial weight `N` instead of `N-1`,
and changing the assigned-value contribution from subtraction to addition.

See [`formalization_receipt.json`](formalization_receipt.json) and
[`proof_review.md`](proof_review.md). Public CI retains the direct compiler
logs and source revision in its `trr10-polynomial-interpolation` artifact.

## Exact finite experiments

The independent arithmetic checker enumerates every smooth short model and
every distinct nontrivial odd cyclic subgroup over the prime fields
`5, 7, 11, 13, 17, 19`.

| Quantity | Checked |
|---|---:|
| Smooth models | 942 |
| Distinct nontrivial odd cyclic subgroups | 1,229 |
| Subgroups with order divisible by the characteristic | 53 |
| Ordinary monomial residue moments | 10,091 |
| Evaluation ranks | 4,864 |
| Point-mass polynomials within the ordinary degree bound | 8,860 |
| Point-mass identity matrix entries | 111,336 |
| Explicit four-variable decoders | 106 |
| Decoder target entries evaluated from collected coefficients | 17,432 |

The complete coefficient lists are in
[`decoder_witnesses.json`](decoder_witnesses.json). There is one deterministic
subgroup fixture for each encountered `(p,N)`, with both `u=0` and `u=1`.
The checker evaluates the collected four-variable coefficients directly.
Each witness and the bundle have hashes in
[`interpolation_receipt.json`](interpolation_receipt.json).

The sweep also checks the evaluation rank profile
`rank(0)=1` and
`rank(d)=min(3d,N-1)-1_{3d=N-1}` for `1 <= d <= ceil(N/3)`.
This complete rank formula is an empirical control here. The universal
degree theorem uses the proved annihilation and point-mass construction.

## Remaining formal scope

The coordinate-polynomial connection is complete in the theorem above.
Passage from generalized Weierstrass coordinates still needs a checked
degree-preserving transformation. The lower bound in characteristics
dividing the marked order requires the function-field and divisor argument.
Small marked orders need their integral certificates connected to this same
interpolation statement in Lean.

The receipt records `tame_short_model_interpolation_theorem_formalized=true`.
Its broader legacy flag `full_interpolation_theorem_formalized` stays false
until those additional cases are integrated. The result measures degree in
this affine coordinate polynomial model; general arithmetic circuits,
discrete-logarithm algorithms and signature security require their own
complexity arguments.

## Reproduce

With the pinned Lean toolchain and Mathlib cache installed, run from the
repository root:

```sh
python research/translation_rank_rigidity/trr08/test_verifier.py \
  --output /tmp/trr10-parser-controls.json
python research/translation_rank_rigidity/trr10/check_interpolation.py \
  --output /tmp/trr10-interpolation.json \
  --witness-output /tmp/trr10-decoders.json
python research/translation_rank_rigidity/trr10/verify_formalization.py \
  --output /tmp/trr10-formalization.json
```

The shared workflow repeats the earlier TRR-08 and TRR-09 audits, then runs
the complete TRR-10 contract. Both repository layouts carry the same proof
and verification sources.
