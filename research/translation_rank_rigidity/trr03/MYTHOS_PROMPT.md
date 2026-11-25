# Strategy V: resolve the order-eleven decoder locus

I am developing Strategy V of a mathematical audit connected to ECDSA security. This task concerns polynomial representations of a translated coordinate function. Its conclusions will be stated as degree bounds, with algorithmic security implications assessed separately.

## Exact question

Let `K=F_q` have characteristic `p>3`, with `p!=11`. Let `E/K` be a nonsingular elliptic curve and let `G=<T>` have order eleven. Put `S=G\{O}`. For `u in K`, define `f_u(O)=u` and `f_u(P)=x(P)` otherwise.

Determine whether there exists a polynomial

\[
\mathcal D(X_1,Y_1,X_2,Y_2)
\]

of total degree at most three in each coordinate pair separately such that

\[
\mathcal D(x(P),y(P),x(Q),y(Q))=f_u(P+Q)
\quad\text{for every }P,Q\in S.
\]

The least possible degree in this model is already proved to be either three or four. Degree four always suffices. Resolve existence of degree three, including solutions that occur only over extension fields.

## Established reduction

For a generalized Weierstrass equation

\[
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,
\]

define

\[
\Phi(X)=\prod_{i=1}^{5}(X-x(iT)),\qquad
\lambda_i=
\frac1{(2y(iT)+a_1x(iT)+a_3)\Phi'(x(iT))}.
\]

Extend `lambda_(11-i)=-lambda_i` for `1<=i<=5`, and set `lambda_0=0`. Let `M_0(i,j)=f_0((i+j)T)` for `1<=i,j<=10`.

The degree-three decoder exists exactly when

\[
M_0\lambda=u\lambda.
\tag{A}
\]

Here is the reason. Degree-three polynomials in `x,y` restrict to `L(9O)`. Their evaluation on the ten points of `S` has dimension nine. The residue theorem identifies this image with `lambda^perp`. Symmetry of the target matrix turns membership of every column in that hyperplane into a polynomial decoder in both blocks. Assigning the value `u` adds the negation permutation matrix, which sends `lambda` to `-lambda`.

The case `<q,-1>=(Z/11Z)^*` is already settled: oddness and Frobenius force `lambda` to have every nontrivial Fourier character in its support, and (A) would make `f_u` constant. Thus the remaining tame field sizes satisfy `q=1` or `-1 mod 11`.

## Concrete algebraic system

Use Tate normal form with the marked point at `(0,0)`:

\[
E_{b,c}:y^2+(1-c)xy-by=x^3-bx^2,
\qquad T=(0,0).
\]

Put

\[
d=b-c^2-c,\qquad e=b^2-bc-c^3.
\]

On the smooth locus with the required denominators nonzero, the order-eleven equation is

\[
g(b,c)=(b-c)^3e+bc\,d^3=0.
\tag{B}
\]

The first five multiples are

\[
(x_1,y_1)=(0,0),\qquad
(x_2,y_2)=(b,bc),\qquad
(x_3,y_3)=(c,b-c),
\]

\[
(x_4,y_4)=
\left(\frac{b(b-c)}{c^2},-\frac{b^2d}{c^3}\right),
\qquad
(x_5,y_5)=
\left(-\frac{bc\,d}{(b-c)^2},\frac{bc^2e}{(b-c)^3}\right).
\]

Also `x(6T)=(b-c)e/d^2`; equation (B) says that this equals `x(5T)`.

The discriminant is

\[
\Delta=b^3\left(16b^2-8bc^2-20bc+b+c^4-3c^3+3c^2-c\right).
\]

Set `x_0=0`, `x_(11-i)=x_i`, and compute

\[
v_i=2y_i+(1-c)x_i-b,\qquad
\lambda_i=\left(v_i\prod_{j\ne i}(x_i-x_j)\right)^{-1}
\quad(1\le i\le5).
\]

The five equations to solve alongside (B) are

\[
\sum_{j=1}^{10}x_{(i+j)\bmod11}\lambda_j-u\lambda_i=0,
\qquad i=1,\ldots,5.
\tag{C}
\]

Use the open locus where

\[
\Delta\,b\,c\,(b-c)\,d\,e
\left(\prod_{i=1}^{5}v_i\right)
\left(\prod_{1\le i<j\le5}(x_i-x_j)\right)\ne0.
\]

When clearing denominators, retain this locus by saturation, including every denominator introduced in the calculation. The target is the smooth solution locus of (B)-(C) over algebraic closures of characteristic `p>3`, `p!=11`.

## Calibration cases and evidence

Order five has genuine exceptions. In the form

\[
y^2+(1-t)xy-ty=x^3-tx^2,
\]

the degree drops to one precisely when `t^2-t-1=0`, with assigned value `f(O)=t^2`. The discriminant becomes `-10t^6`, and the exceptional invariant is `j=-25/2`. Over `F_11`, the short model `y^2=x^3+2x+9` with `T=(4,2)` has the full-group decoder

\[
f(P+Q)=5a_x(P)a_x(Q)+4a_y(P)a_y(Q),
\]

using `a(O)=(9,0)` and `f(O)=9`.

Order seven has been excluded by an exact certificate. For its Tate parameter `t`, equality of the residue ratios requires

\[
F=3t^4-4t^3+2t^2-2t-1=0,
\quad H=2t^4+2t^3-8t^2+8t-3=0.
\]

These satisfy

\[
(-4t^3-4t^2+16t-18)F
+(6t^3-8t^2+4t-1)H=21.
\]

In characteristic seven their common root is `t=-2`, where the curve is singular. This settles the characteristic-greater-than-three order-seven case.

A useful order-eleven fixture is `K=F_23`, `b=1`, `c=5`. It has `Delta=14`,

\[
(x_1,\ldots,x_5)=(0,1,5,21,22),\quad
(y_1,\ldots,y_5)=(0,5,19,19,22),
\]

\[
(\lambda_1,\ldots,\lambda_5)=(16,9,15,6,21).
\]

The five ratios `(M_0 lambda)_i/lambda_i` are `(13,8,0,19,2)`, so this instance has degree four.

An exact scan examined all 74,828 nonsingular short Weierstrass models over primes `5<=p<=101` and all 70,652 prime-order subgroup instances of order at least five in those models. It found 290 degree drops, all at order five. This evidence covers prime fields in that range; the target question includes arbitrary finite extensions.

## Requested result

Resolve the order-eleven system. A positive answer should give an explicit finite field, a nonsingular curve with a point of exact order eleven, the assigned value `u`, and exact verification of (A). Constructing the degree-three decoder from a basis of `L(9O)|_S` would complete the witness.

For an exclusion result, give an algebraic proof or a checkable saturation/elimination certificate, and account for every exceptional characteristic. An elimination over `Q` should be accompanied by the integer denominator or ideal certificate that identifies the remaining finite characteristics, followed by their analysis.

Supply reproducible SageMath or Magma code for any symbolic computation. State precisely which parts have proofs, which were checked computationally, and any remaining unsolved locus. Keep the result attached to this interpolation problem and its hypotheses.
