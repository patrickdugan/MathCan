# Mythos review: sparse-edit inverse-label rank

Context: Strategy V of a defensive ECDSA security assessment.
We seek precise restricted-model lower bounds and counterexamples
to unsupported security claims. Work on synthetic cyclic functions
and the stated mathematics. Do not develop or optimize scalar-recovery
or signature-forgery algorithms.

Let N be prime and K a field of characteristic not dividing N.
Let ell(j)=j*1_K for j=0,...,N-1, with cyclic indexing.
For g=ell+e, support(e)<=k, define rank(g) as the rank of the
N by N sum-translation matrix g(i+j). Over a splitting field,
for nontrivial z^N=1 the missing Fourier modes are precisely
the roots of

    H(z)=N+(z-1)sum_i e(i)z^i.

The proof of the exact rank is rank(ell)=N-1 or N according
to whether sum ell is zero. Rank is invariant under extension.
TRR-13 gives the bound ceil(N/(2k+1))-1 via the nonzero
difference support and the translate-basis cover.

TRR-13B gives two sharper written results:
1. For one edit at i, each fibre of z^i(z-1) on mu_N has
m(m-1)<=N-1: two distinct roots with ratio t determine
w=(t^i-1)/(t^(i+1)-1) uniquely; the zero-denominator
case cannot occur. This even holds for composite N.
2. For k edits and prime N, any B with B^(k+1)<N yields
m<=3*(ceil(N/B)-1). Pigeonhole the residue vectors
(j,j*i_1,...,j*i_k), using B equal-width blocks per coordinate;
two in the same box give a nonzero invertible multiplier,
and a Laurent polynomial N+sum e(i)z^b_i(z^a-1) with
exponent span <=3*(ceil(N/B)-1) and value N at z=1.
Thus fixed k implies rank(g)>=N-O(N^(k/(k+1))) uniformly
over all tame characteristics.

Review both proofs, especially the fibre with zero denominator,
dilation with signed exponents, changes of fields, the trivial
frequency, and the actual support size. The specific open
problem is:

Determine the maximum possible size of a fibre of z^i(z-1)
on mu_N in arbitrary tame finite characteristic, with N prime.
Does it remain bounded independently of N? If not, prove a
growth lower bound by explicit finite-field examples or obtain
a stronger uniform upper bound. For k=2, study the analogous
root set of N+(z-1)(c*z^i+d*z^j). Can the special difference
structure imply N-O(k) translation rank, or is the power-law
loss unavoidable? A rigorous restricted-field result is useful.
Any proposed counterexample should include exact field, N,
coefficients and the gcd with X^N-1, so extension-field roots
are counted. Compare with characteristic zero without
assuming the complex Fourier-minor theorem in finite fields.

Separately audit the inverse-label rational pole bound
2H(R)>=N-1-2k, the formula leaf bound 4Lx+6Ly>=N-1-2k,
and the generic rational equality-path bound with binary
outputs in TRR-13/README.md. The latter must charge raw
division guards; X/X reduces to a constant yet is undefined
as an expression at X=0.

The computational limitation is explicit: rank and pole
height can be very large for small shared circuits. For
example a point mass has full translation rank; the
quadratic-residue predicate on F_p* has optimal rational
height (p-1)/2 and O(log p) arithmetic evaluation cost.
TRR-12's forward decoder is a further control. No direct
resource-preserving conversion to general bit-RAM or
shared circuit cost has been established. If proposing
any strengthened restricted complexity result, state
all assumptions, including sharing, preprocessing,
guards and the success model. Do not infer a general
ECDLP or ECDSA result from the rank theorem alone.

Return an independent proof, a sharp counterexample or
the precise remaining mathematical obstruction.
