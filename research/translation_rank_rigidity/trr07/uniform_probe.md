# Uniform exclusion from the doubling law

## Statement and scope

Let $K$ have characteristic zero or characteristic $p>3$. Let

$$
E:y^2=x^3+Ax+B,\qquad 4A^3+27B^2\ne0,
$$

and let $G=\langle T\rangle$ have prime order $N\ge19$. Write

$$
\Phi(X)=\prod_{\{P,-P\}\subset G\setminus\{O\}}(X-x(P)),
\quad w=1/\Phi(x),
\quad \lambda_P=\frac1{2y(P)\Phi'(x(P))}.
$$

There is no scalar $u$ for which $M_0\lambda=u\lambda$. This holds over the algebraic closure in every characteristic under consideration. With the evaluation-space reduction and degree bounds from TRR-03, it excludes the smaller affine-block interpolation degree at every prime order at least nineteen.

The checked integral certificates at orders $7,11,13,17$ complete the prime orders below this threshold. Combining those certificates with this argument gives

$$
\boxed{D_{\min}(N)=\lceil N/3\rceil\quad\text{for every prime }N\ge7.}
$$

The model is a polynomial in the two coordinate pairs, with the degree bound imposed separately on each pair, evaluated on $(G\setminus\{O\})^2$, with a freely chosen value at the identity. Generalized Weierstrass equations in characteristic greater than three pass to the short equation through affine changes of the coordinates. These preserve the degree bound and change the target coordinate and assigned identity value affinely.

This document gives a written algebraic proof. `uniform_probe.py` checks the integer polynomial identities and finite-field calibrations. The divisor and residue arguments below have not been formalized in Lean. No literature novelty claim is made.

## Local coefficients and the obstruction

Use the invariant differential $\omega=dx/(2y)$, its dual derivation $\partial$, and the parameter $z=-x/y$ at the identity. Its expansions are

$$
x=z^{-2}+O(z^2),\qquad \omega=(1+O(z^4))\,dz.
$$

At a nonidentity subgroup point, translation identifies a local parameter with $z$. Define $a_P,b_P$ by

$$
w(P+Z)=\frac{\lambda_P}{z(Z)}
\left(1+a_Pz(Z)+b_Pz(Z)^2+O(z(Z)^3)\right).
$$

Every nonidentity point has $y(P)\ne0$, since $G$ has odd order. Its distinct pairs $\{P,-P\}$ have distinct $x$-coordinates. Thus every displayed residue denominator is nonzero.

The function $w$ is even, so

$$
\lambda_{-P}=-\lambda_P,\qquad a_{-P}=-a_P,\qquad b_{-P}=b_P.
$$

For fixed $P\ne O$, apply the residue theorem to
$x(P+Z)w(Z)\omega(Z)$. At points $Q\in G\setminus\{O,-P\}$, the residue is $\lambda_Q x(P+Q)$. The residue at $-P$ is $-\lambda_Pb_P$. There is no pole at $O$. It follows that

$$
\frac{(M_0\lambda)_P}{\lambda_P}=b_P. \tag{1}
$$

Set $L=\partial w/w$. At $P\ne O$,

$$
L(P+Z)=-z^{-1}+a_P+(2b_P-a_P^2)z+O(z^2).
$$

The divisor of $w$ is

$$
\operatorname{div}(w)=N[O]-\sum_{R\in G}[R]. \tag{2}
$$

The poles and principal parts of $\partial L$ imply

$$
\partial L(Z)=\sum_{R\in G\setminus\{O\}}x(Z-R)-(N-1)x(Z)+C_0
$$

for a constant $C_0$. Compare constant terms at $P\ne O$. Translation permutes $G$, giving

$$
2b_P-a_P^2+Nx(P)
=C_0+\sum_{R\in G\setminus\{O\}}x(R). \tag{3}
$$

Equations (1) and (3) show that the obstruction vanishes exactly when

$$
a_P^2-Nx(P)=C\quad\text{for every }P\in G\setminus\{O\}. \tag{4}
$$

## A rational addition identity

For $P\in G\setminus\{O\}$, consider

$$
R_P(Z)=\frac{w(Z+P)}{w(Z)}.
$$

Equation (2), together with translation invariance of the subgroup divisor, gives

$$
\operatorname{div}(R_P)=N([-P]-[O]).
$$

The rational function

$$
q_P(Z)=\frac{y(Z)-y(P)}{x(Z)-x(P)}
$$

has simple poles at $-P$ and $O$, with principal parts $z^{-1}$ and $-z^{-1}$, respectively. Its apparent singularity at $P$ is removable. Hence

$$
L(Z+P)-L(Z)-Nq_P(Z)
$$

has no poles and is constant. At $O$, the constant term is $a_P$: the evenness of $w$ makes the constant term of $L(Z)$ zero, and the constant term of $q_P(Z)$ is zero. Therefore

$$
L(Z+P)-L(Z)=a_P+Nq_P(Z). \tag{5}
$$

Take constant terms at $Z=P$. The removable value of $q_P$ is the tangent slope, giving

$$
\boxed{a_{2P}=2a_P+N\frac{3x(P)^2+A}{2y(P)}.} \tag{6}
$$

This derivation also applies when the characteristic divides $N$; the scalar $N$ then vanishes in (5).

## Elimination when the characteristic does not divide $N$

Write $n$ for the image of the integer $N$ in $K$, assume $n\ne0$, and put $c=C/n$. Under (4),

$$
a_P^2=n(x(P)+c).
$$

For $x=x(P)$, $y=y(P)$, and $m=(3x^2+A)/(2y)$, the usual doubling formula is $x(2P)=m^2-2x$. Substitute (6) into (4) at $2P$, then subtract the equation at $P$. After division by $n$, this yields

$$
4a_Pm+6x+3c+(n-1)m^2=0.
$$

Squaring eliminates $a_P$. Put

$$
F(X)=X^3+AX+B,\qquad R(X)=3X^2+A.
$$

Multiplication by $16y^4$ gives

$$
K(x(P))=0,
$$

where the following polynomial has integral coefficients and degree at most eight:

$$
K(X)=\left[4(6X+3c)F(X)+(n-1)R(X)^2\right]^2
-64n(X+c)R(X)^2F(X). \tag{7}
$$

No division by the tangent slope occurs. All nonidentity subgroup points are covered, including those where the tangent slope vanishes.

There are $(N-1)/2\ge9$ distinct subgroup $x$-coordinates. Therefore (7) must vanish identically. If $C_i=[X^i]K$, its leading coefficient is

$$
C_8=9(n-1)(9n-25).
$$

Since the characteristic exceeds three, the two possibilities are $n=1$ and $9n=25$.

### The branch $n=1$

An exact integer factorization is

$$
K\big|_{n=1}=16FQ,
\qquad Q=(6X+3c)^2F-4(X+c)R^2.
$$

The polynomial $F$ is monic, so $K=0$ implies $Q=0$. Set

$$
Q_3=[X^3]Q=12A+9c^2,\qquad Q_2=[X^2]Q=12Ac+36B.
$$

The following identity lies in $\mathbb Z[A,B,c]$:

$$
\boxed{48(4A^3+27B^2)=16A^2Q_3+(Q_2-24Ac)Q_2.} \tag{8}
$$

Its coefficient 48 is invertible in every characteristic under consideration. Hence the discriminant vanishes.

### The branch $9n=25$

Three further integral identities suffice:

$$
\begin{aligned}
C_7&=-40c(9n-25)-640c,\\
3C_6&=4A(9n-25)(9n-13)+320A+432c^2,\\
C_5&=-24Ac(25n-33)-16B(9n-25)+320B.
\end{aligned} \tag{9}
$$

In characteristic five, $9n=25$ implies $n=0$, contrary to the present assumption. For every other characteristic greater than three, 640 and 320 are invertible. Equations (9) successively give $c=0$, $A=0$, and $B=0$. Again the cubic is singular.

Thus no smooth solution exists when $n\ne0$. Equations (8) and (9) identify every characteristic involved in the argument: two and three lie outside the stated model, while five is handled explicitly by the branch condition. No further exceptional prime arises.

## Matching characteristic $p=N$

Suppose $N=p>3$. Equation (4) says $a_P^2=C$, while (6) says $a_{2P}=2a_P$. Comparing their squares gives $3a_P^2=0$, hence $a_P=0$.

Pass to the algebraic closure, which preserves a putative solution. Equation (5) now gives $\partial R_P=0$. The kernel of this nonzero derivation on the function field of a smooth curve over a perfect field is its subfield of $p$-th powers. In the present short model this can also be seen from

$$
[K(E):K(E)^p]=p:
$$

the extension $K(E)/K(x)$ has degree two, as does $K(E)^p/K(x^p)$, whereas $[K(x):K(x^p)]=p$. The derivation kills $K(E)^p$ and has $\partial x=2y\ne0$, so its kernel is exactly $K(E)^p$.

Consequently $R_P=v^p$ for a rational function $v$. Its divisor must be

$$
\operatorname{div}(v)=[-P]-[O].
$$

A smooth genus-one curve has $L(O)=K$, so this degree-one pole divisor cannot support a nonconstant rational function. This contradicts $P\ne O$.

The matching-characteristic argument works at every prime order greater than three, independently of the degree-eight root count.

## Mechanical checks and remaining formalization

Run

```bash
python3 uniform_probe.py --output receipts/uniform_probe.json
```

The script checks ten exact polynomial identities, including (7)'s elimination numerator, (8), and all three identities in (9). Seventeen finite fixtures cover tame and matching characteristic at orders $7,11,13,17,19,23,29,31$, together with the known order-five exception. They verify 288 instances of the doubling law and compare independently expanded local coefficients with the residue ratios.

For those finite checks, the coefficients of $w$ are computed directly from the roots of $\Phi$. If

$$
S_1=\sum_{v\ne x(P)}\frac1{x(P)-v},\qquad
S_2=\sum_{v<w}\frac1{(x(P)-v)(x(P)-w)},
$$

where the sums run over the other distinct roots, then

$$
\begin{aligned}
a_P&=-\frac{3x(P)^2+A}{2y(P)}-2y(P)S_1,\\
b_P&=a_P^2-2x(P)-2(3x(P)^2+A)S_1-4y(P)^2S_2.
\end{aligned}
$$

The theorem uses the written divisor, principal-part and residue arguments above. Their full machine formalization remains open. The finite calibrations provide independent implementation checks; the uniform conclusion follows from the algebraic proof and the displayed integer identities.
