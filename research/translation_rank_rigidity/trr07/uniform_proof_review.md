# Uniform interpolation obstruction: independent proof review

This review establishes the algebraic and geometric implications behind the degree-eight obstruction. Its conclusion concerns the affine-coordinate polynomial interpolation model already specified in TRR-03. The general geometry remains a written argument. The coefficient classification is additionally checked by Lean 4.35.

## Statement and hypotheses

Let `E` be a smooth elliptic curve over a field of characteristic zero or characteristic `p>3`, with a point `T` of prime order `N>=19`. Work in short Weierstrass coordinates

```
y^2 = x^3+A*x+B,
G=<T>,  S=G\{O},
Phi(X)=product over S/{+/-} of (X-x(Q)),
w=1/Phi(x).
```

Use the invariant differential `omega=dx/(2y)` and its dual derivation `partial`. Around each `Q` in `S`, use the parameter obtained by translating `z=-x/y` at the identity, and write

```
w(Q+z)=lambda_Q/z*(1+a_Q*z+b_Q*z^2+O(z^3)).
```

The established residue identity says that a lower-degree decoder would make `a_Q^2-N*x(Q)` constant on `S`. The integer `N` in scalar expressions means its image in the field. The parameter `c` below denotes this constant divided by `N`; it has no connection to the Tate normal form coefficient named `c` elsewhere.

It suffices to work over an algebraic closure. A decoder over the original field remains one after scalar extension. The group points retain their exact order and distinct coordinates.

## Derivation of the slope cocycle

Put `f=partial(w)/w`. The divisor of `w` is `(N-1)[O]-sum(S)`. In the translated parameter its expansions are

```
f(Z)=(N-1)/z+O(z)                  at O,
f(Q+Z)=-1/z+a_Q+O(z)              at Q in S.
```

The absence of a constant term at the identity follows from evenness of `w` and oddness of the invariant logarithmic derivative. Explicitly, `x(z)` is even, and the factor converting `d/dz` to `partial` is `1+O(z^4)`, so it changes neither the simple-pole coefficient nor the constant term shown above.

Fix `Q` in `S`. Translation by `Q` permutes `G`. Therefore

```
g_Q(Z)=f(Z+Q)-f(Z)
```

has possible poles only at `-Q` and `O`. Their principal parts are respectively `N/z` and `-N/z`. At every other group point, both terms have the same simple-pole coefficient `-1`; their poles cancel because the translated parameter is exactly the same parameter in the two expansions.

The rational chord-slope function

```
s(Z,Q)=(y(Z)-y(Q))/(x(Z)-x(Q))
```

has principal part `1/z` at `-Q` and `-1/z` at `O`. At `Q` its apparent singularity is removable. Indeed, `y(Q)!=0` because a nonidentity point of odd order is not a point of order two, and its limiting value is

```
s(Q,Q)=(3*x(Q)^2+A)/(2*y(Q)).
```

The expansion of `s(Z,Q)` at `O` has constant term zero. Consequently `g_Q-N*s(Z,Q)` has no pole anywhere and equals the constant `a_Q`, found by taking its constant term at `O`.

Now take `P` in `S` with `P+Q` in `S`. At `Z=P`, use the local parametrization `Z=P+Z(z)`. The two occurrences of `f` again have the same pole `-1/z`. Taking the finite value after cancellation proves

```
a_(P+Q)=a_P+a_Q+N*s(P,Q).
```

This includes `P=Q`, since the slope has the removable tangent value and `2P` is nonzero. Thus

```
a_(2P)=2*a_P+N*m_P,
m_P=(3*x(P)^2+A)/(2*y(P)).
```

The proof used equality of rational functions and their principal parts. It assumed no Fourier support, no finite-field splitting condition and no choice of a value for `f` at a pole.

## A polynomial of degree at most eight

First suppose `n=N` is nonzero in the field. Constancy of the obstruction gives a scalar `c` such that

```
a_P^2=n*(x(P)+c)       for every P in S.
```

Write `X=x(P)`, `Y=y(P)` and `a=a_P`. The tangent formula gives `x(2P)=m_P^2-2X`. Squaring the doubled cocycle value and using the two relations for `a_P^2` and `a_(2P)^2` yields

```
6X+3c+4*a*m_P+(n-1)*m_P^2=0.
```

Multiplying by `4Y^2` is valid because `Y!=0`, and the equation becomes

```
R(X)=-8*a*Y*(3X^2+A),
R(X)=4*(6X+3c)*(X^3+A*X+B)+(n-1)*(3X^2+A)^2.
```

Squaring this necessary identity gives `K(X)=0`, where

```
K(X)=R(X)^2-64*n*(X+c)*(3X^2+A)^2*(X^3+A*X+B).
```

Its degree is at most eight. The points in `S` give exactly `(N-1)/2` distinct `x`-coordinates: equal coordinates identify a point with itself or its negative. For `N>=19`, there are at least nine such roots. Hence `K` is the zero polynomial over the field. This root argument works in positive characteristic and over every extension field.

## Classification of the polynomial identity

The leading coefficients of `K`, from degree eight through degree five, are

```
k8 = 9*(n-1)*(9*n-25),
k7 = -360*c*(n-1),
k6 = 108*A*n^2-456*A*n+540*A+144*c^2,
k5 = -600*A*c*n+792*A*c-144*B*n+720*B.
```

They all vanish. Since characteristic three is excluded, the first equation gives `n=1` or `9n=25`.

For `n=1`, the next informative coefficients give

```
48*(4A+3c^2)=0,
192*(A*c+3B)=0.
```

Their scalar factors have only primes two and three. Thus `4A=-3c^2` and `4B=c^3`, which imply `4A^3+27B^2=0`. The curve is singular.

For `9n=25`, characteristic five would force `n=0`, contradicting this case's hypothesis. After substituting `n=25/9`, the coefficient at degree seven is `-640c`. Therefore `c=0`. The degree-six coefficient becomes `(320/3)A`, so `A=0`; degree five then gives `320B=0`, so `B=0`. These cancellations require only primes two, three and five, all accounted for in this branch. This curve is also singular.

`MathCan/TranslationInterpolationUniform.lean` proves the complete implication from these four coefficient equations to `4A^3+27B^2=0` over an arbitrary field satisfying `n!=0`, `2!=0` and `3!=0`. Its proof derives the exclusion of characteristic five where needed. It does not assume that `n` is an integer or that the field has characteristic zero. The six theorem declarations, including supporting cancellation lemmas, compile with the standard transitive axioms listed in `proof_uniform_receipt.json`.

## Matching characteristic and the complete range

If `N=0` in the field, primality of `N` implies characteristic `p=N`. TRR-06 supplies the remaining argument: `w(Z+Q)/w(Z)` has divisor `p([-Q]-[O])`, so its logarithmic derivative is constant. It is nonzero for `Q!=O`, since otherwise a pth root would have the impossible principal divisor `[-Q]-[O]`. The multiplicative cocycle makes these constants additive, and the local expansion identifies them with `a_Q`. Thus `a_(2Q)=2a_Q`, while the structural identity gives `2(u_(2Q)-u_Q)=3a_Q^2!=0`.

Every characteristic in the stated scope is therefore covered. For primes `N>=19`, the lower-degree decoder contradicts smoothness through the degree-eight argument or the matching-characteristic argument. The existing exact certificates cover primes `7,11,13,17`. Combining these with the TRR-03 two-value degree theorem yields the upper value `ceil(N/3)` for every prime `N>=7` in this interpolation model. Order five retains its already classified exceptional family.

The general divisor, residue and evaluation-space steps remain written geometry. The preceding `proof_review.md` records their mathematical sources and formal obligations. The new Lean module checks the coefficient classification; the local finite-field experiments and order-by-order certificates provide independent controls.
