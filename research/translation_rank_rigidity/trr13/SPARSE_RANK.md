# TRR-13B: sparse-edit inverse-label rank

Theorem (written proof, exact synthetic controls). Let N>=3 be
prime, char(K) not dividing N, and g(j)=j*1_K+e(j) for j in C_N
with at most k nonzero edits. Rank is over K, unchanged by scalar
extension. Over a splitting field, for z!=1 with z^N=1,

    sum_j j*z^j = N/(z-1).
    H(z) = N + (z-1) sum_i e(i) z^i.

The first identity follows by differentiating the geometric sum
or multiplying by z-1 and telescoping. The missing nontrivial
Fourier modes are precisely roots of H on mu_N. Since H(1)=N,
H is nonzero, even after reduction modulo X^N-1. If m is the
number of these roots, rank(g)=N-1-m plus one if sum_j g(j)!=0.

## One edit, any cyclic order

For e=c*delta_i with c nonzero, the missing modes form a fibre
of z^i(z-1) on mu_N. If distinct z,w are in that fibre, set
t=z/w !=1. Then

    (t^(i+1)-1)*w=t^i-1.

If the coefficient on the left is zero, the right is nonzero
because simultaneous t^i=t^(i+1)=1 would imply t=1. Otherwise
w and z=t*w are uniquely determined by t. Therefore the m(m-1)
ordered distinct pairs have different ratios, all nonidentity,
so m(m-1)<=N-1. Consequently rank(g)>=N-1-floor((1+sqrt(4N-3))/2).
This argument is valid for composite N as well, in tame
characteristic. Edits at i=0 and i=N-1 give m<=1 directly.

## k edits, prime order

Choose an integer B>=1 with B^(k+1)<N; let L=ceil(N/B)-1.
For the actual support indices i_1,...,i_k, consider the N
vectors

    (j,j*i_1,...,j*i_k) mod N, 0<=j<N.

Partition each residue interval into at most B consecutive
blocks, each of size at most ceil(N/B). There are fewer than N
boxes. Two distinct vectors have the same box. Subtract them
coordinatewise as integers: obtain a,b_1,...,b_k in [-L,L],
with a congruent to a nonzero multiplier mu modulo N and
b_i congruent to mu*i_i. Primality makes mu a unit modulo N.
Thus z->z^mu permutes mu_N, and H(z^mu) agrees there with

    J(z)=N+sum_i e(i) z^b_i (z^a-1).

The exponents of J, including zero, lie in
[-L+min(0,a), L+max(0,a)], so the span is at most 3L.
Multiplying by an appropriate power of z produces a polynomial
of degree at most 3L. It is nonzero because J(1)=N. Therefore

    m <= 3*(ceil(N/B)-1)
    rank(g) >= N-1-3*(ceil(N/B)-1).

The bound combines with TRR-13's elementary support-rank
bound by taking the larger lower bound. For fixed k>=1,
take B=floor(N^(1/(k+1))) (N prime is not a perfect power);
rank(g)>=N-O(N^(k/(k+1))) uniformly across tame fields.
If the actual number of edits is smaller, use that number.
The exact k=0 rank was already established in TRR-13.

## Controls and limits

verify_sparse.mjs checks the number of missing nontrivial modes
over algebraic closures by polynomial gcd with X^N-1, squarefree
in the tested tame characteristics. It checks the rank relation
independently by gcd with the word polynomial. It exhaustively
checks single edits for p in {2,3,5,7,11}, 3<=N<=31 with p not
dividing N; direct splitting-field controls check uniqueness of
ratios over eleven small prime fields. Seeded support sets at
prime orders up to 257 reconstruct the dilation, compare the
two polynomials modulo X^N-1 and check their gcd degrees and
exponent spans. The finite tests do not prove a general theorem
and are not key-recovery experiments.

The sharper open question is to determine extremal fibre size
for one edit and whether the exponents O(sqrt(N)) and
O(N^(k/(k+1))) are optimal in arbitrary tame characteristic.
A proof of N-O(k) rank or an exact counterexample would be
particularly useful. These results still bound fixed linear
translation representations, not unrestricted shared circuits
or bit-RAM computation. No general security theorem follows.
