# The next finite evaluation lemma

## Reviewed result and the remaining connection

The compiled TRR-09 theorem excludes the **actual residue eigenvector** on
a smooth short Weierstrass curve with an odd marked subgroup of order
`N >= 19`, provided `2`, `3`, and `N` are nonzero in the coefficient field.
The next connection identifies the evaluations of ordinary bounded-degree
polynomials with the residue hyperplane. A finite Lagrange argument gives
that identification.

The degree cases must be kept explicit. Put `d = floor(N/3)`. For
`N mod 3 = 1` or `2`, the degree-`d` evaluation image is the residue
hyperplane. When `3` divides `N`, the same degree evaluates onto every
function on the nonidentity subgroup points. In that case the relevant
excluded degree is `d-1`.

After the finite evaluation connection is formalized, the resulting exact
degree statement will be

\[
\boxed{\text{least degree in each coordinate block}=\lceil N/3\rceil}
\]

for every assigned value at the identity, under the preceding tame,
smooth, odd-order hypotheses. This document supplies the mathematical
proof of the proposed evaluation connection and its interfaces. The
current Lean sources prove the residue eigenvector exclusion; they have
been left unchanged during this review.

## 1. Independent review of the compiled hypotheses and signs

The reviewed declarations are
`TRR08Geometry.tame_cyclicResidue_eigenvector_exclusion` and
`TRR08Geometry.tame_no_cyclicResidue_eigenvector` in
[TameEigenvector.lean](../../../experiments/trr08_geometry/TRR08Geometry/TameEigenvector.lean),
together with the row and square identities in
[ResidueEigenvector.lean](../../../experiments/trr08_geometry/TRR08Geometry/ResidueEigenvector.lean).

Their concrete objects are as follows.

* `W` is Mathlib's affine short Weierstrass model, with `[W.IsElliptic]`
  in the final exclusion theorem. Its equation is
  `y^2 = x^3 + W.a₄*x + W.a₆`.
* `H = AddSubgroup.zmultiples T` is the actual cyclic subgroup. Its finite
  enumeration comes from `IsOfFinAddOrder T`; its cardinal is proved equal
  to `addOrderOf T`. The theorem asks for odd order at least nineteen.
* `affineX O = 0` and `subgroupResidue H O = 0`. The residue matrix sum
  ranges over `H`, so its extra identity summand is zero. Its restriction
  to nonidentity rows is the matrix from the interpolation question.

Write `S = H \ {O}`, `X = x(S)`, and

\[
\Phi(Z)=\prod_{a\in X}(Z-a).
\]

The theorem `subgroupResidue_eq_inverse_product` identifies the weights as

\[
\lambda_P=\frac1{2y(P)\Phi'(x(P))}\qquad(P\in S).
\]

Odd subgroup order excludes nonzero two-torsion. Therefore `y(P)` and
every difference between distinct elements of `X` are nonzero. The proof
establishes that each displayed residue is nonzero and that
`lambda(-P) = -lambda(P)` before cancelling residues.

The row equation used by the final theorem is exactly

\[
\sum_{Q\in S}f_0(P+Q)\lambda_Q=u\lambda_P,
\quad f_0(O)=0,\quad f_0(R)=x(R)\ (R\ne O).
\tag{1}
\]

The sign of `u` agrees with assigning `f_u(O)=u`. If `J` is the negation
permutation matrix on `S`, then

\[
M_u=M_0+uJ,\qquad J\lambda=-\lambda,
\qquad M_u\lambda=0\iff M_0\lambda=u\lambda.
\tag{2}
\]

In particular, the convention in (1) introduces no minus sign into the
eigenvalue.

The paired addition formula in `paired_add_x_difference` has sign

\[
x(P+Q)-x(P-Q)
=-\frac{4y(P)y(Q)}{(x(P)-x(Q))^2}.
\]

Multiplication by the positive representative's residue gives the paired
row contribution
`-2*y(P)/(Phi'(x(Q))*(x(P)-x(Q))^2)`. At `Q=P`, the contribution is
`x(2P)*lambda(P)`, while `Q=-P` contributes zero. These agree with
`residueMatrixRow_by_roots`.

The finite trace relation in
[TraceCoefficient.lean](../../../experiments/trr08_geometry/TRR08Geometry/TraceCoefficient.lean)
then gives

\[
a_P^2=Nx(P)+2u-U_H,
\qquad
a_P=-\sum_{Q\in H}c(P,Q),
\qquad
U_H=\sum_{Q\in H}x(Q).
\tag{3}
\]

Here `c(P,Q)` is the actual normalized chord or tangent slope. The proved
diagonal identity and finite translation of the sum imply

\[
a_{2P}=2a_P+N\frac{3x(P)^2+A}{2y(P)}.
\tag{4}
\]

The final theorem sets the scalar
`c = (2*u-U_H)/(N:K)`, as required to turn (3) into
`a_P^2 = N*(x(P)+c)`. Division by `N` occurs at this step, so the explicit
hypothesis `(N:K) != 0` is necessary for this proof. All four signs in
(1)–(4) agree with the definitions and with the scalar obstruction.

The resulting theorem quantifies over arbitrary fields satisfying these
hypotheses. Prime subgroup order and finiteness of the ambient field are
unneeded. The theorem includes characteristic zero and finite extension
fields whenever the marked curve satisfies its assumptions. Matching
characteristic, even subgroup order, and characteristics two and three
remain outside this final exclusion theorem. Its current conclusion is
about (1); the polynomial evaluation step below supplies the remaining
connection to the stated decoder model.

## 2. Finite paired interpolation

Let `N=2m+1` with `m>=2`, and suppose `2 != 0` in `K`. Choose one
representative from each inverse pair:

\[
P_i=(a_i,b_i),\quad -P_i=(a_i,-b_i),\quad 1\le i\le m.
\]

Assume that the `a_i` are pairwise distinct and every `b_i` is nonzero.
These are the only geometric properties used in this section. For an
actual odd cyclic subgroup, one can take `P_i=iT` for `1<=i<=m`.

For arbitrary prescribed values `f:S -> K`, define

\[
e_i=\frac{f(P_i)+f(-P_i)}2,
\qquad
o_i=\frac{f(P_i)-f(-P_i)}{2b_i}.
\tag{5}
\]

Replacing `P_i` with `-P_i` leaves both quantities unchanged. In
particular, they can also be defined as functions on the distinct
x-coordinate set, independently of a representative choice.

Let

\[
\ell_i(Z)=\frac{\prod_{j\ne i}(Z-a_j)}{\prod_{j\ne i}(a_i-a_j)},
\qquad
p_f(Z)=\sum_i e_i\ell_i(Z),
\qquad
q_f(Z)=\sum_i o_i\ell_i(Z).
\tag{6}
\]

Finite Lagrange interpolation proves

\[
\deg p_f<m,\quad \deg q_f<m,
\quad f(P)=p_f(x(P))+y(P)q_f(x(P))\quad(P\in S).
\tag{7}
\]

The pair `(p_f,q_f)` is unique subject to these degree bounds. Subtracting
the values at `P_i` and `-P_i` shows that any difference of two such odd
polynomials vanishes at all `m` nodes. Their sum gives the same conclusion
for the even polynomials. The ordinary polynomial root bound completes
the argument.

Zero polynomials have degree `-infinity` throughout this document. This
convention makes all the displayed degree bounds include the zero case.

## 3. The residue functional is one coefficient

Since `Phi` is monic of degree `m`, the coefficient of `Z^(m-1)` in
`ell_i` is `1/Phi'(a_i)`. Consequently

\[
[Z^{m-1}]q_f
=\sum_i\frac{o_i}{\Phi'(a_i)}
=\sum_{P\in S}\lambda_P f(P).
\tag{8}
\]

The normalization in (8) is exact: the denominator `2*b_i` in (5)
matches the denominator in the original residue. No additional factor
of two remains.

Define the residue functional and a space of normal forms by

\[
\Lambda(f)=\sum_{P\in S}\lambda_P f(P),
\qquad
\mathcal V_m=
\{p(X)+Yq(X):\deg p\le m-1,\ \deg q\le m-2\}.
\]

Equations (7) and (8) give the precise next evaluation theorem:

\[
\boxed{
\operatorname{im}(\operatorname{ev}_S|_{\mathcal V_m})
=\ker\Lambda=\lambda^\perp.
}
\tag{9}
\]

For the reverse inclusion, take `p_f` from (6). The condition
`Lambda(f)=0` sets the sole possible `Z^(m-1)` coefficient of `q_f` to
zero, giving `deg q_f <= m-2`. For the forward inclusion, apply the
Lagrange leading-coefficient identity to `q`, whose leading slot is
already zero. The even part cancels in every inverse pair.

Evaluation on `V_m` is injective, by the uniqueness argument after (7).
Thus its dimension is `m+(m-1)=N-2`, and the image is a hyperplane in the
`N-1` dimensional space of all values on `S`.

The coefficient identity can be stated first for arbitrary distinct
nodes, without any curve:

\[
\deg q<m\ \Longrightarrow\
[Z^{m-1}]q=\sum_i\frac{q(a_i)}{\prod_{j\ne i}(a_i-a_j)}.
\tag{10}
\]

Mathlib's existing `Lagrange.basis`, `Lagrange.nodalWeight`, evaluation,
and interpolation declarations supply the objects for this interface.
TRR-09 already uses the same nodal weights in
[BarycentricResidue.lean](../../../experiments/trr08_geometry/TRR08Geometry/BarycentricResidue.lean).

## 4. Ordinary total degree and normal forms

The decoder model bounds ordinary total degree in each coordinate pair.
Let `P_d` be the bivariate polynomials whose monomials `X^a*Y^b` satisfy
`a+b<=d`. Work modulo the short equation

\[
Y^2-X^3-AX-B=0.
\]

For `d>=1`, the image of `P_d` in normal form consists exactly of

\[
\boxed{
p(X)+Yq(X),\qquad
\deg p\le\left\lfloor\frac{3d}{2}\right\rfloor,
\quad
\deg q\le\left\lfloor\frac{3d-3}{2}\right\rfloor.
}
\tag{11}
\]

One inclusion follows by reducing each even power of `Y` with
`Y^2=X^3+AX+B`. The weights `wt(X)=2` and `wt(Y)=3` give an upper bound
`3d` for every original monomial. Reduction preserves this upper bound.
Its even component has weight `2*deg p`; its odd component has weight
`2*deg q+3`.

The opposite inclusion has explicit representatives. If `j=3a+b` with
`0<=b<=2`, put

\[
L_j(X,Y)=X^b(Y^2-AX-B)^a.
\]

On the curve, `L_j=x^j`, while its ordinary total degree is at most
`2a+b=ceil(2j/3)`. The polynomial `Y*L_j` represents `y*x^j` with degree
at most `ceil((2j+3)/3)`. These bounds put every monomial allowed by (11)
inside `P_d`; linear combinations preserve the bound.

This proof can be implemented entirely through polynomial evaluation.
The usual divisor notation calls the normal-form space in (11)
`L(3d O)`. The finite interpolation proof needs the explicit degree
interface (11), together with the displayed representatives.

The unique normal form refers to the quotient by the Weierstrass
equation. Evaluation on a finite point set has an additional kernel.
These two quotients should be kept distinct in the formal definitions.

## 5. The three cases for `floor(N/3)`

With `N=2m+1` and `d=floor(N/3)`, equation (11) specializes as follows.

| `N mod 3` | `3d` | Normal-form degrees | Kernel of evaluation within the normal-form space | Evaluation image |
| --- | --- | --- | --- | --- |
| `1` | `N-1=2m` | `deg p<=m`, `deg q<=m-2` | `K*Phi(X)` | `lambda^perp` |
| `2` | `N-2=2m-1` | `deg p<=m-1`, `deg q<=m-2` | Zero | `lambda^perp` |
| `0` | `N=2m+1` | `deg p<=m`, `deg q<=m-1` | `K*Phi(X)` | All functions on `S` |

For `N mod 3 = 1`, subtract the leading coefficient of `p` times `Phi`
to obtain a representative with `deg p<=m-1`. Since `Phi(x(P))=0` on
`S`, this changes no value. The odd part already has the bound in (9).
If a normal form in this space vanishes on `S`, pair its values to see
that `q=0` and that `p` is a scalar multiple of `Phi`.

The `N mod 3 = 2` row is exactly (9). In the last row, the canonical
interpolants from (7) are both allowed, so every function on `S` occurs.

The kernel statement `K*Phi` applies after passage to normal form. As an
ordinary polynomial, `Phi(X)` has degree `m`, which can exceed `d`.
Its class has a representative of total degree at most `d` using the
polynomials `L_j` above. The kernel in the original bivariate polynomial
space also contains the allowable multiples of the cubic equation.

In the middle and first rows the finite decoder criterion therefore
matches the actual residue eigenvector criterion. The last row permits
every matrix on `S x S` at degree `d`; applying the residue exclusion to
that degree would use the wrong evaluation image.

## 6. The block polynomial interface

A four-variable polynomial has block degree at most `d` when every
monomial

\[
X_1^aY_1^bX_2^cY_2^e
\]

with nonzero coefficient satisfies both `a+b<=d` and `c+e<=d`. This is
the meaning of degree at most `d` in each coordinate pair separately.

If `F_1,...,F_s` are bivariate representatives of degree at most `d`,
then

\[
\mathcal D(X_1,Y_1,X_2,Y_2)
=\sum_{i,j}C_{ij}F_i(X_1,Y_1)F_j(X_2,Y_2)
\tag{12}
\]

has the required block bound. A general polynomial with that bound is
a linear combination of such products, using the monomial features.
This supplies both directions of the link between polynomial decoders
and the finite tensor interface.

The existing
[TranslationInterpolationEvaluation.lean](../../../MathCan/TranslationInterpolationEvaluation.lean)
already proves `evaluation_hyperplane_decoder_iff` and
`evaluation_pole_decoder_iff` from an equality of the evaluation image
with `lambda^perp`. Applying (9) and (11) will discharge that equality
for the first two rows of the table.

The finite indexing in that module uses `Option (Fin n)` to designate
a pivot and the other evaluation points. Its `none` index is a chosen
point of `S`. The group identity `O` has already been removed. Here
`n=N-2`; reindexing the actual nonidentity subgroup points must preserve
this convention.

The matrix `M_u(P,Q)=f_u(P+Q)` is symmetric. The existing tensor proof
constructs its decoder when its rows lie in the evaluation hyperplane.
Equation (2) converts that row condition into the same eigenvector
premise used by `tame_cyclicResidue_eigenvector_exclusion`.

## 7. A shorter first formal target

To obtain the exclusion implication, it suffices to formalize

\[
3d\le N-1\quad\Longrightarrow\quad
\sum_{P\in S}\lambda_P F(x(P),y(P))=0
\quad\text{for every }F\in P_d.
\tag{13}
\]

Indeed, (11) gives `deg q<=m-2` whenever `3d<=2m`. The pair cancellation
and identity (10) then prove (13). Fixing either coordinate block of a
decoder yields such a polynomial in the other block, so (13) and (2)
immediately produce the forbidden residue eigenvector. This first target
requires the annihilation direction alone.

For existence at degree `D=ceil(N/3)`, the canonical normal forms in
(7) have weight at most `2m+1=N`. The explicit representatives `L_j`
therefore give degree at most `D` interpolants for every function on
`S`. Interpolate the point masses and substitute them into (12) to
construct every matrix on `S x S`, including `M_u` for any `u`.

These statements give the precise future corollary. On a smooth short
model, if `N>=19` is odd and `2*3*N` is nonzero in `K`, every degree
`d<ceil(N/3)` satisfies `3d<=N-1` and is excluded by the compiled
eigenvector theorem plus (13). Degree `ceil(N/3)` always suffices by the
finite construction. This conclusion is about the specified coordinate
interpolation model.

## 8. Remaining formal obligations

The next implementation can proceed through explicit finite lemmas:

1. Prove (10) from the leading coefficient of the Lagrange interpolation
   polynomial, with degree conventions covering the zero polynomial.
2. On the actual subgroup, prove the inverse-pair decomposition and
   establish (8). The current root and residue definitions use the
   distinct x-coordinate `Finset`, so the result should identify these
   weights directly with `subgroupResidue`.
3. Give the degree normalization and degree-bounded representatives in
   (11), using ordinary bivariate total degree. This step supplies the
   requested polynomial interface without a divisor-space assumption.
4. Formalize (13) and the fixed-block evaluation of an actual
   four-variable polynomial. Compose the resulting matrix equation
   with the existing tame eigenvector exclusion.
5. Complete (9), including constructive representatives for every
   annihilated vector, and connect it to the existing finite tensor
   equivalence. The full-surjectivity construction at `ceil(N/3)` then
   supplies the matching upper bound.

The mathematical degree cases above are determined. The remaining
uncertainty concerns the Lean representation of degree-bounded
bivariate and block polynomials, and the amount of reindexing needed to
reuse the existing finite tensor API. No new geometric identity,
unlisted characteristic exception, or residue theorem is required by
this finite route.
