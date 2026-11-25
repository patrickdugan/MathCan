# TRR-05/06: certified interpolation rigidity through order 17

Date: 2026-11-25. Strategy V, restricted representation model.

## Theorem and scope

For a nonsingular elliptic curve in characteristic zero or p>3, with a rational marked point T of prime order N in {7,11,13,17}, let S=<T> minus O and f_u(O)=u, f_u(P)=x(P) otherwise. The least degree in each affine-coordinate input pair of a polynomial representing f_u(P+Q) on S x S is ceil(N/3), for every u. This follows from the TRR-03 two-value theorem and the following exact exclusion. The proof covers arbitrary finite extensions, not merely prime-field scans. All results concern a specified interpolation model; no general arithmetic circuit lower bound, ECDLP speedup, or general security theorem is claimed.

The certificate and its search/verifier code were supplied by the user from an independent Mythos run. We reproduced the dependency-free Node checker (Node 22.16.0): all 83 checks passed. Original source files are retained. PARI search code is supplied for provenance; we did not rerun its search. The general geometric steps are written mathematics, not Lean-checked.

## Exact certificate (TRR-05)

Use the residue reduction of TRR-03: A_i=(2y_i+(1-c)x_i-b) prod_{j != i}(x_i-x_j), lambda_i=1/A_i, H_ij=x_{i+j}-x_{i-j}, x_0=0 and x_{N-i}=x_i. The lower degree exists iff H lambda=u lambda. Work with b=rt(r-1), c=t(r-1), and t(t-1) invertible. The monic marked-order equation f_N defines R=Z[t][r]/(f_N). The verifier constructs the coordinates and all inverses in R[1/(t(t-1))] by checked integral identities. Consequently specialization to every field on this chart is valid.

Let u_i=(H lambda)_i/lambda_i. For each i>1 the verified equality u_i-u_1=g_i/(t^a_i (t-1)^b_i) gives compressed equations. Their norms have the form t^e_i(t-1)^s_i P_i(t). The verified integral relation sum W_i P_i=n_0 forces p|n_0 if the equations have a common root on the open locus. The certificate independently checks norm-adjugate identities, the resulting ideal membership in R, the complete irreducible factorization of the common-root polynomial in each candidate characteristic, the fibre gcd over every residue field, and the vanishing discriminant at every common zero.

| N | rank R | degree P_i | n_0 | candidate characteristics >3 |
|---:|---:|---:|---:|---|
| 7 | 1 | 4 | 21 | 7 |
| 11 | 2 | 10 | 605 | 5,11 |
| 13 | 3 | 14 | 1014 | 13 |
| 17 | 5 | 24 | 78608 | 17 |

At N=17 the compressed equations have r-degree <=4, t-degree <=12. Their norms have t-1 exponent 45 and t exponent 5 only for i=7. The adjugate identity is sum W_i t^(5-e_i) adj(M_i) M_i=78608 t^5(t-1)^45 I_5. In characteristic 17 the common univariate gcd is (t-11)^24 and the fibre gcd is (r-12)^3; b=7,c=2 and Delta=c4=0. Thus the candidate is cuspidal. The checker also resolves characteristics 2 and 3 as algebraic systems, but we do not extend the geometric theorem to them.

## Chart coverage audit

For any marked point of order N>=7, translate the point to (0,0) and its nonvertical tangent to y=0. In the resulting Weierstrass equation a4=a6=0; a3 is nonzero by smoothness and a2 is nonzero because the point is not a flex (not of order 3). Rescale x,y so a2=a3=-b; write a1=1-c. Thus b is nonzero. In this normal form x(2T)=b, x(3T)=c. The equalities c=0 or b=c would force order <=5. Hence r=b/c and t=c/(r-1) exist. For N>=11, x(5T)=rt(t-1) implies t-1 nonzero. For N=7, x(3T)=x(4T) implies r=t, and b nonzero then implies t-1 nonzero. The subsequent denominators r-t,h,j when used are nonzero: x(6T), x(7T), x(8T), respectively, would otherwise be zero, and these multiples are not +/-T at the orders requiring the next recurrence step. The statements are also direct consequences of the recurrence's division by x(iT), which is nonzero for 2<=i<=(N-1)/2. Specifically, generic rational simplification gives

    x3=t(r-1)
    x4=r(r-1)
    x5=rt(t-1)
    x6=t(r-1)(r-t)/(t-1)^2
    x7=rt(r-1)(t-1)h/(r-t)^2
    x8=r(r-1)(r-t)j/h^2
    x9=t(r-1)hk/j^2

with h=rt-2r+1, j=r-t^2+t-1, k=rt^2-3rt+r+t^2. For N=2n+1, the following identities were independently recomputed by SymPy from the generic addition recurrence, in Q(r,t), with integral cleared denominators:

    (x3-x4)/f7 = 1-r
    (x5-x6)/f11 = -t/(t-1)^2
    (x6-x7)/f13 = t(r-1)/((r-t)^2(t-1)^2)
    (x8-x9)/f17 = (r-1)/(h^2 j^2)

where f_N are exactly the four defining polynomials in the checker. Equality x(nT)=x((n+1)T) holds for every marked N-torsion point. The denominators and remaining cofactors are nonzero there, proving chart coverage in all claimed characteristics. Invertible affine changes of Weierstrass coordinates preserve the degree in each feature pair and the existential pole assignment.

## TRR-06: geometric structural identity

Work in short Weierstrass coordinates in characteristic 0 or p>3. Let N>=5 be odd, G=<T>, S=G minus O, and Phi(X)=prod_{Q in S/{+/-}}(X-x(Q)). Set w=1/Phi(x). Then div(w)=N[O]-sum_{Q in G}[Q]. Write z=-x/y near O, translated to each point; x(z)=z^-2+O(z^2) and omega=(1+O(z^4)) dz. Around Q in S,

    w(Q+z)=lambda_Q/z * (1+a_Q z+b_Q z^2+O(z^3)).

The oddness of the residue vector and evenness of w imply lambda_-Q=-lambda_Q, a_-Q=-a_Q and b_-Q=b_Q. Apply the residue theorem to x(Q+Z)w(Z) omega. The only higher-order pole is at -Q, with residue -lambda_Q b_Q; all other residues give (H lambda)_Q. Thus u_Q=b_Q.

Let partial be the derivation dual to omega. The meromorphic function B=partial(partial(w)/w) has double-pole principal parts +1/z^2 at S and -(N-1)/z^2 at O, with no simple poles. Consequently B(Z)=sum_{R in S} x(Z-R)-(N-1)x(Z)+C. Comparing constant terms at Q gives 2b_Q-a_Q^2=C'-N x(Q), where C' is independent of Q. Hence

    2(u_Q-u_T)=a_Q^2-a_T^2-N(x(Q)-x(T)).

This is the structural identity independently computed by the supplied checker. It converts the obstruction into constancy of a_Q^2-N x(Q) on S.

## Uniform exclusion in characteristic N (written proof)

Let N=p>3 be prime. For Q in G, R_Q(Z)=w(Z+Q)/w(Z) has divisor p([-Q]-[O]). Its logarithmic derivative has no poles in characteristic p and is a constant kappa_Q. For nonzero Q, kappa_Q cannot vanish: over an algebraic closure the kernel of the derivation on the function field consists of pth powers. A pth root of R_Q would have divisor [-Q]-[O], contradicting the degree-one principal divisor criterion on a smooth genus-one curve. The multiplicative cocycle of R_Q and translation invariance of omega imply kappa_(Q+R)=kappa_Q+kappa_R. At O, w has an even expansion with order p-1; the ratio R_Q has expansion const*z^-p*(1+a_Q z+...), so kappa_Q=a_Q. In particular a_(2Q)=2a_Q. The structural identity yields 2(u_(2Q)-u_Q)=3a_Q^2, which is nonzero for p>3. Therefore the lower interpolation degree is impossible in the matching characteristic for every prime N=p>3. This proof uses the standard function-field derivation and genus-one principal-divisor facts; no formal kernel proof is yet supplied.

## Reproduce

Run node verify.mjs certificate.json from this directory. Expect ALL CHECKS PASSED, 83 [ok] checks, and no smooth common zeros. The checked integer n_0 values are sufficient certificates, not claimed to be minimal generators of the integer elimination ideals. The brute force scan is a sanity check and is not the proof over algebraic closures.

See PROSPECTUS.md for registered follow-up gates.
