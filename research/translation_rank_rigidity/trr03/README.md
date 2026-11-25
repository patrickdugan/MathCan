# TRR-03: polynomial decoders for translated observables

This develops Strategy V: translation rank as a constraint on algebraic representations. The motivating application is the assessment of proposed compression arguments in ECDSA security research. The theorems measure polynomial degree and the pole divisors of features. General circuit size and discrete-logarithm complexity require further arguments.

The general monomial bound is sharp on cyclic groups. For affine coordinates on an elliptic curve, the least degree of a decoder on the finite points of a prime subgroup has just two possible values. An explicit residue vector decides which value occurs. We classify the order-five exception and exclude exceptions at order seven. The next unresolved case in this work is order eleven.

**Evidence:** the general statements below have written proofs. Python verifies exact finite examples and polynomial certificates. `MathCan/TranslationPolynomialDecoder.lean` checks the explicit five-point counterexample, including its addition table, with Lean 4.35.0. Its six theorem reports contain only `propext` or no axioms. The general geometry and residue arguments remain written proofs.

## 1. Polynomial features and matrix rank

Let `K` be a field, `G` a finite abelian group, and

\[
M_f(P,Q)=f(P+Q).
\]

Suppose that maps `a:G -> K^r` and `b:G -> K^s` and a polynomial `P(U,V)` satisfy

\[
f(X+Y)=P(a(X),b(Y)).
\]

If the degree in the first block is at most `D`, expansion in its monomials gives

\[
P(U,V)=\sum_{|\alpha|\le D}U^\alpha P_\alpha(V),
\qquad
\operatorname{rank}M_f\le {r+D\choose D}.
\tag{1}
\]

Each summand evaluates to an outer product. The feature maps can be arbitrary; their computational cost is absent from this representation statement.

For `K=F_Q`, reduction by `U_i^Q=U_i` gives the sharper count

\[
B_Q(r,D)=\#\{\alpha\in\{0,\ldots,Q-1\}^r:|\alpha|\le D\},
\qquad \operatorname{rank}M_f\le B_Q(r,D).
\tag{2}
\]

Reduction never increases total degree. Bounds from both blocks and the matrix dimensions may be combined by taking their minimum.

### Equality on cyclic groups

Let `G=C_n`, assume `K` contains a primitive `n`th root `zeta`, and choose `r,D>=1` such that

\[
n>D(D+1)^{r-1}.
\]

Put `w_i=(D+1)^(i-1)` and define

\[
a_i(x)=\zeta^{w_i x},\qquad
f(x)=\sum_{|\alpha|\le D}\zeta^{(\alpha\cdot w)x},\qquad
P(U,V)=\sum_{|\alpha|\le D}U^\alpha V^\alpha.
\]

Distinct base-`D+1` digits give distinct exponents below `n`. Every displayed Fourier coefficient is one, so Fourier diagonalization gives rank exactly `binom(r+D,D)`. The degree is `D` in each block and `2D` in all variables together. Moreover,

\[
a(x+y)=\operatorname{diag}(\zeta^{w_1y},\ldots,\zeta^{w_ry})a(x).
\]

Thus translation symmetry, including this linear equivariance, permits equality in (1). This construction allows the splitting field to vary with the parameters. On an encoded group, evaluating these character features may itself involve the unknown group parameter.

### Total degree

If the total degree in both blocks is at most `D`, set `B_Q(r,d)=0` for `d<0`. Splitting monomials according to `|alpha|<k` gives

\[
\operatorname{rank}M_f\le
\min_{0\le k\le D+1}
\bigl(B_Q(r,k-1)+B_Q(s,D-k)\bigr).
\tag{3}
\]

For the first part, group terms by their first-block monomial. In the second part, the second-block degree is at most `D-k`, so group by that block instead. This is the monomial splitting argument underlying the Croot-Lev-Pach rank lemma [1].

When `r=s` and `D<Q`, balancing the two degree cutoffs yields

\[
{r+\lfloor D/2\rfloor\choose r}
+{r+\lceil D/2\rceil-1\choose r}.
\]

The receipt contains examples attaining (3). Small characteristic can impose further restrictions. For instance, every Boolean polynomial of degree below four on `F_2^4` has even weight. Its group-algebra element squares to zero, so its multiplication matrix has image contained in its kernel and rank at most eight. A cubic monomial attains eight, while (3) gives ten.

## 2. Charging the algebraic degree of the features

Let `A` be a smooth one-dimensional commutative algebraic group over a finite field, let `G<=A(K)` have size `N`, and let `h` have degree `d` on its smooth projective completion. Assume `h` has a geometric pole inside `A`.

Suppose the first features are rational functions `a_1,...,a_r`, with common polar divisor

\[
B=\max_i\operatorname{div}_\infty(a_i),\quad
e=\deg B,\quad s=|G\cap\operatorname{supp}B|.
\]

Let `t` be the number of poles of `h` in `G`. Assign any values at poles for evaluation. If a polynomial decoder of degree at most `D` in these features agrees with `h(X+Y)` except at at most `k` positions of `X` for each fixed `Y`, then

\[
D e\ge N-s-t-k-d.
\tag{4}
\]

**Proof.** For a fixed `Y`, the rational function

\[
w_Y(X)=h(X+Y)-P(a(X),b(Y))
\]

has pole degree at most `d+De`. It vanishes at at least `N-s-t-k` regular evaluation points. If one `w_Y` is nonzero, comparison of its zero and pole degrees proves (4).

If every `w_Y` vanishes identically, the common divisor `D B` must contain the poles of every translate of `h`. The orbit of one geometric pole inside `A` has `N` distinct points. This forces `e>=N` and `D>=1`, which also proves (4). Translation acts freely on the group, giving the orbit assertion. The hypothesis about an interior pole excludes poles fixed at the boundary of an affine group. QED.

For the ordinary affine features `(x,y)` on a short Weierstrass elliptic curve, `B=3[O]`. Applying (4) to `h=x` gives `3D>=N-4-k`. The next section improves the exact, zero-error case and determines the possible integer degrees.

## 3. An exact two-value theorem for affine-coordinate decoders

Let

\[
E/K:y^2=x^3+Ax+B,\qquad \operatorname{char}K>3,
\]

be nonsingular. Let `G<=E(K)` have prime order `n>=5`, and put `S=G\{O}`. Fix `u in K` and define `f_u(O)=u`, `f_u(T)=x(T)` for `T!=O`.

Define `d_*(E,G,u)` as the least integer `D` for which a polynomial in four affine variables satisfies

\[
f_u(P+Q)=\mathcal P(x(P),y(P),x(Q),y(Q))
\quad(P,Q\in S),
\tag{5}
\]

with total degree at most `D` in each pair of variables separately. The evaluation domain in (5) omits `O` in both inputs; the assigned value `u` is used when `P+Q=O`.

**Theorem.**

\[
d_*(E,G,u)\in
\left\{\left\lfloor\frac n3\right\rfloor,
\left\lceil\frac n3\right\rceil\right\}.
\tag{6}
\]

### Lower bound by divisors

Fix `Q!=O`. Substituting its coordinates into the decoder gives a function `g in L(3D[O])`. The difference `w(T)=x(T+Q)-g(T)` is nonzero: it has a double pole at `-Q`, where `g` is regular. It has at least `n-2` zeros on `G\{O,-Q}` and pole degree at most `3D+2`. Thus `3D>=n-4`.

More precisely, let `m` be the actual pole order of `g` at `O`. If `m=n-4`, every zero and pole is forced, giving

\[
\operatorname{div}(w)=
\sum_{T\in G\setminus\{O,-Q\}}[T]-2[-Q]-(n-4)[O].
\]

The sum of the points of the odd-order group `G` is `O`. The displayed divisor has group sum `3Q`, which is nonzero for a point of prime order at least five. The criterion for a principal divisor on an elliptic curve [2] rules this out. Consequently `m>=n-3`, hence

\[
3D\ge n-3,
\qquad D\ge\lfloor n/3\rfloor.
\]

### Upper bound by interpolation

For `D>=1`, plane polynomials of total degree at most `D` restrict to exactly `L(3D[O])`. Each nongap `0,2,3,...,3D` is realized as a pole order `2i+3j` with `i+j<=D`; the resulting functions have distinct leading pole orders. Riemann-Roch gives dimension `3D`, proving equality of the spaces.

Write `Z=sum_{T in S}[T]`. It has degree `n-1`. If `m>=n`, Riemann-Roch gives

\[
\ell(m[O])-\ell(m[O]-Z)=m-(m-n+1)=n-1,
\]

so evaluation onto `K^S` is surjective. Taking `m=3 ceil(n/3)` supplies degree-`ceil(n/3)` interpolation functions for every point of `S`. Products of one interpolation function in each input block represent any matrix on `S x S`, including (5). This proves (6).

The theorem concerns the affine input set. For a full-group decoder, an assigned feature vector at `O` must be specified. For `D>=3`, any off-curve vector can be separated from `S` using the cubic curve equation, allowing independent interpolation at `O` without increasing `D`. The five-point example below gives its own full-group assignment at degree one.

## 4. A residue vector decides the lower value

Let

\[
F(X)=\prod_{\{T,-T\}\subset S}(X-x(T)),\qquad
\lambda_T=\frac{1}{2y(T)F'(x(T))}\quad(T\in S).
\tag{7}
\]

All denominators are nonzero: the group has odd order, its finite points have nonzero `y`, and different pairs have different `x` coordinates. Also `lambda_{-T}=-lambda_T`.

Let `M_u` be the matrix in (5), and `M_0` its value at `u=0`. Then

\[
d_* =\lfloor n/3\rfloor
\quad\Longleftrightarrow\quad
M_0\lambda=u\lambda.
\tag{8}
\]

**Proof.** The divisor of `F(x)` is `Z-(n-1)[O]`. With the invariant differential `omega=dx/(2y)`, the residues of `omega/F(x)` at `T in S` are `lambda_T`. For `g in L((n-2)[O])`, the differential `g omega/F(x)` is regular at `O` and has no other poles besides `S`. The residue theorem gives

\[
\sum_{T\in S}\lambda_Tg(T)=0.
\]

The evaluation map on `L((n-2)[O])` is injective and its image has dimension `n-2`. Thus its image is exactly `lambda^perp` in `K^S`. Evaluation from `L((n-1)[O])` has the same image, since its one-dimensional kernel is spanned by `F(x)`.

At `D=floor(n/3)`, the pole bound `3D` is either `n-2` or `n-1`. Hence the degree-`D` feature space is exactly `lambda^perp`. A symmetric matrix has a decoder in this feature space precisely when all its columns lie in that space. Indeed, if `V` is a full-column-rank feature evaluation matrix and `L V=I`, the containment gives `M=V(L M L^T)V^T`. Therefore the decoder exists precisely when `M_u lambda=0`.

Finally, `M_u=M_0+u J_-`, where `J_-` permutes a point with its negative. Since `J_- lambda=-lambda`, the last equation is (8). QED.

In particular, any degree drop permits only one assigned pole value `u`. The ratio test in the verifier compares `(M_0 lambda)_T/lambda_T` for all `T` and thus covers every pole assignment at once.

### A sufficient condition for the upper value

If `K=F_q`, `n` is prime to `q`, and

\[
\langle q,-1\rangle=(\mathbb Z/n\mathbb Z)^*,
\tag{9}
\]

then `d_*=ceil(n/3)` for every `u`.

To prove this, extend `lambda` by `lambda_O=0`. Its sum is zero and it is nonzero. Its Fourier support is stable under multiplication by `q` and under negation. Under (9) it therefore contains every nontrivial character. Equation (8) would extend to all of `G`: the row at `O` also annihilates `lambda`, since `x in L((n-2)[O])`.

For the sum-translation matrix, Fourier transformation gives

\[
\widehat{M_{f_u}\lambda}(\chi)
=\widehat f_u(\chi)\widehat\lambda(\chi^{-1}).
\]

Thus (8) would force every nontrivial Fourier coefficient of `f_u` to vanish, making `f_u` constant. The `x` coordinate takes `(n-1)/2>=2` distinct values on `S`, giving a contradiction. This proves the condition. The argument uses field size `q` for Frobenius, including extension fields.

## 5. The order-five exception and its classification

Over `F_11`, take

\[
E:y^2=x^3+2x+9,\qquad T=(4,2).
\]

The subgroup generated by `T` has the following coordinates and assigned value at infinity:

| Index | Geometric point | Decoder vector | `f` |
|---:|---|---|---:|
| 0 | `O` | `(9,0)` | 9 |
| 1 | `(4,2)` | `(4,2)` | 4 |
| 2 | `(8,3)` | `(8,3)` | 8 |
| 3 | `(8,8)` | `(8,8)` | 8 |
| 4 | `(4,9)` | `(4,9)` | 4 |

For all 25 pairs, including infinity,

\[
f(P+Q)=5a_x(P)a_x(Q)+4a_y(P)a_y(Q)\pmod{11}.
\tag{10}
\]

This is degree one in each block. The full translation matrix has rank two: (10) gives the upper bound, and its minor with rows and columns `0,1` has determinant `9*8-4*4=1 mod 11`. Lean checks the finite identities, point equations, addition table, inverse residues, and this minor. The passage from factorization and minor to rank is the usual written linear-algebra argument.

The exception admits an exact classification in Tate normal form. For a marked point of order five, write

\[
E_t:y^2+(1-t)xy-ty=x^3-tx^2,\qquad T=(0,0).
\]

The four nonzero multiples have coordinates

\[
(0,0),\ (t,t^2),\ (t,0),\ (0,t).
\]

Using `dx/(2y+(1-t)x-t)` in (7), the residue vector is

\[
(t^{-2},t^{-3},-t^{-3},-t^{-2}).
\]

The two distinct ratios in (8), computed at `T` and `2T`, are `t+1` and `t^2`. Thus the degree drops to one exactly when

\[
t^2-t-1=0,\qquad f(O)=t^2
\tag{11}
\]

in these Tate coordinates. The discriminant `t^5(t^2-11t-1)` then becomes `-10t^6`. For characteristic greater than three, the exceptional curves are nonsingular exactly when the characteristic differs from five. Their invariant is `j=-25/2`.

Changing between Tate and short Weierstrass coordinates is affine linear in the coordinates, so it preserves each block's polynomial degree. The assigned value of `x(O)` undergoes the same affine change as the ordinary `x` values. Condition (11) classifies marked order-five groups; the `j` value alone does not specify a marked subgroup.

## 6. Order seven has no degree drop

For a marked point of order seven, Tate normal form has

\[
b=t^2(t-1),\quad c=t(t-1),\qquad
y^2+(1-c)xy-by=x^3-bx^2.
\]

Here `t` and `t-1` are nonzero. Multiplying the residue vector by a common nonzero factor gives

\[
(A,B,C,-C,-B,-A),\quad
A=-t(t-1)^3,\ B=t-1,\ C=t^3.
\]

The three ratios in (8) are

\[
R_1=t^3+t+1,\quad
R_2=t(3t^3-3t^2+2t-1),\quad
R_3=(t-1)^2(t^2-3t+3).
\]

Set

\[
F=R_2-R_1=3t^4-4t^3+2t^2-2t-1,
\]
\[
H=R_2-R_3=2t^4+2t^3-8t^2+8t-3.
\]

The following integral identity is an exact certificate:

\[
(-4t^3-4t^2+16t-18)F
+(6t^3-8t^2+4t-1)H=21.
\tag{12}
\]

In characteristic greater than three, a common root would therefore require characteristic seven. Modulo seven,

\[
F=3(t+2)^4,\qquad H=2(t+2)^4.
\]

At their only common root, the discriminant vanishes: its factors modulo seven include `(t+2)^3`. Hence no nonsingular curve qualifies. The integer polynomial coefficient identities and discriminant factor are independently checked by the standard-library verifier. Consequently `d_*=3` for every marked order-seven subgroup in characteristic greater than three, including characteristic seven.

## 7. The current limit: order eleven

For an order-eleven subgroup, (6) leaves `d_*=3` or `4`. We have no proof or counterexample for a degree-three decoder in the remaining cases. Condition (9) already gives degree four when `<q,-1>` acts transitively. In the tame case for order eleven, the remaining finite-field sizes satisfy `q=1` or `-1 mod 11`.

The exact next problem is the locus where the residue vector in (7) is an eigenvector in (8), on the modular curve of a marked point of order eleven. A concrete system is supplied in [the Mythos prompt](MYTHOS_PROMPT.md) and [order11_system.json](order11_system.json). The prompt asks for an algebraic certificate valid in the specified characteristics or a fully checked counterexample.

In Tate coordinates, put

\[
d=b-c^2-c,\qquad e=b^2-bc-c^3.
\]

The first five `x` coordinates of the marked point are

\[
0,\ b,\ c,\ \frac{b(b-c)}{c^2},\
-\frac{bc\,d}{(b-c)^2},
\]

and the sixth is `(b-c)e/d^2`. On the smooth locus where the displayed denominators are nonzero, exact order eleven is given by

\[
g(b,c)=(b-c)^3e+bc\,d^3=0.
\tag{13}
\]

This equation makes `x(6T)=x(5T)`; equality of the points would imply `T=O`, so `6T=-5T`. The order is eleven since eleven is prime. The saturation conditions in the prompt retain distinct finite points and a nonzero differential denominator. The finite search covers prime fields through 101; extension fields remain outside that empirical coverage.

## 8. Computational and formal evidence

From the repository root, run:

```bash
python research/translation_rank_rigidity/trr03/verify_decoder_sharpness.py
python research/translation_rank_rigidity/trr03/elliptic_decoder_probe.py
python research/translation_rank_rigidity/trr03/elliptic_ratio_exhaust.py --maxp 101
python research/translation_rank_rigidity/trr03/verify_tate_certificates.py --check
lake env lean MathCan/TranslationPolynomialDecoder.lean
```

The first three commands regenerate their adjacent receipts. The fourth compares the exact Tate computation with its committed receipt; `--write-receipt` regenerates it. The workflow regenerates all receipts and checks for a diff. SHA-256 values bind each receipt to its verifier and relevant input certificates.

`verify_decoder_sharpness.py` checks eight cyclic equality examples on every one of their 56,600 input pairs, nine additive examples attaining the total-degree bound, and all 34,944 Boolean polynomials in the specified small-degree spaces. It also checks full-rank Cauchy examples with one-dimensional rational features.

`elliptic_decoder_probe.py` computes exact affine evaluation spaces for 54 selected full prime-order curves over 19 prime fields, with group orders from 7 to 97. Every `u=0` case has degree `ceil(n/3)`. Twelve examples have group order equal to the field characteristic.

`elliptic_ratio_exhaust.py --maxp 101` enumerates all 74,828 nonsingular short Weierstrass models over primes from 5 through 101. It checks all 70,652 distinct prime-order subgroup instances with order at least five within those models. This counts different Weierstrass models separately. Among the instances are 8,720 full prime-order groups, 61,932 proper subgroups, and 1,800 subgroups whose order equals the characteristic.

There are 290 degree drops, all at subgroup order five. Every one is checked by independent affine-polynomial containment. All 18,133 order-five subgroup instances agree with (11). The verifier also tests every pole value on one negative subgroup per field using direct curve addition and matrix containment. No degree drop at order at least seven appears in this finite range.

`verify_tate_certificates.py` checks 77 polynomial and rational identities, including (11), (12), and the formulas used to present (13). Its order-eleven fixture over F23 adds 139 finite assertions, including all 121 group additions. Exact coefficient arithmetic supplies the symbolic certificates; finite evaluations serve as additional consistency checks.

The new Lean file proves six statements about the explicit order-five witness. The earlier TRR-01 module has sixteen supporting theorems, checked both locally and in [its successful CI run](https://github.com/patrickdugan/MathCan/actions/runs/45600455877). The two modules have distinct scopes, as recorded in their source headers.

## 9. Security scope and model limits

The rational formula for a Cauchy kernel shows why polynomial hypotheses matter. On a multiplicative subgroup `G<=K^*` and for a nonzero `a` outside `G`,

\[
F(xy)=\frac1{xy-a}
\]

uses one scalar feature for each input and a denominator of total degree two, while its matrix is a nonsingular Cauchy matrix of rank `|G|`. The ordinary rational group-law formulas give another way to see the distinction [3].

Polynomial degree also differs from circuit size. Repeated squaring computes degree `2^k` with `k` multiplication steps; over a finite field, inversion on nonzero inputs can be represented by exponentiation. Large degree can therefore coexist with short arithmetic computations. Strategy V's present conclusions constrain specified polynomial representations. A cryptographic lower bound must additionally connect those representations to the algorithms and costs under study.

This work extends Strategy V. The separate question of structured generic-group reductions remains Strategy VI. Novelty relative to the research literature has not been established; the residue criterion and small-order classifications are results derived and checked within this project.

## References

1. Zeev Dvir and Benjamin L. Edelman, *Matrix Rigidity and the Croot-Lev-Pach Lemma*, Theory of Computing 15(8), 2019. https://theoryofcomputing.org/articles/v015a008/v015a008.pdf
2. Andrew V. Sutherland, *Divisors and the Weil Pairing*, MIT 18.783 Lecture 23, 2025. The notes give the pole orders of `x,y` and the principal-divisor criterion used above. https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec23.pdf
3. Ben Lynn, *Elliptic Curves: Explicit Addition Formulae*. https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
4. Zachary Scherr, *Rational Polynomial Pell Equations*, dissertation. The Tate normal forms and their discriminants appear in Chapter II. https://deepblue.lib.umich.edu/bitstream/handle/2027.42/100026/zscherr_1.pdf
5. Tanja Lange and Arne Winterhof, *Polynomial Interpolation of the Elliptic Curve and XTR Discrete Logarithm*, COCOON 2002, pp. 137-143. This is related work on interpolation of logarithm functions, with a different target function from (5). https://research.tue.nl/en/publications/polynomial-interpolation-of-the-elliptic-curve-and-xtr-discrete-l/
