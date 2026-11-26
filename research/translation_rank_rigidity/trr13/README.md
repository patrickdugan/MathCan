# TRR-13: inverse-label pole, rank and rational-formula obstructions

Date 2026-11-26. Strategy V, restricted-model security analysis. New written
proofs with finite controls; not a Lean audit, general ECDLP lower bound,
or evidence of a polynomial-time ECDSA compromise. The TRR-11 theorem and
TRR-12 small forward circuit retain their original scope.

## 1. Scalar labels

Let E/K be a smooth geometrically integral elliptic curve, G=<T> a
rational cyclic subgroup of order N>=3, and N nonzero in K. For 0<=j<N,
let ell(jT)=j*1_K. This is a field-valued residue label; if the
characteristic is smaller than N it need not uniquely encode j.
A full scalar recovery algorithm must return an injective encoding.

For a rational function R in K(E), let H(R) be the degree of its polar
divisor over an algebraic closure; constants have height zero. Suppose
R agrees with ell on all but k elements of G, counting poles or
undefined evaluations as failures. Then

    2 H(R) >= N-1-2k.

Proof: F(P)=R(P+T)-R(P)-1 is a rational function. It is not identically
zero since telescoping N translated copies would give 0=N. Its pole
degree is at most 2H(R), by translation invariance of degree and the
pole inequality for sums. Each of the N-1 non-wrap edges with two
correct endpoints contributes a distinct regular zero. At most 2k
such edges are removed. A nonzero rational function on a smooth
projective curve has at most its pole degree many distinct geometric
zeros. This gives the inequality. If only S=G\{O} is evaluated, the
same argument gives 2H(R)>=N-2-2k. No claim is made for N=0 in K.

More generally the exact rational shift difference has trace
sum_{j=0}^{N-1} F(P+jT)=-N as a function-field identity, and on the
group takes value -N at -T and zero elsewhere.

## 2. Translation rank, including errors

Write tau g(P)=g(P+T) and V_g=span_K{tau^i g: 0<=i<N}.
Its dimension is the rank of the full sum-translation matrix.
For ell, (tau-I)ell=1-N delta_{-T}. The point mass has rank N and
belongs to V_ell+K*1. Thus rank(ell)>=N-1. Precisely it is N
if sum ell !=0, since 1 then belongs to V_ell; otherwise it is N-1
since V_ell lies in the sum-zero hyperplane. This elementary proof
does not require a splitting field.

If g differs from ell at k positions, set h=(tau-I)g-1.
Then h is supported on at most 2k+1 positions and its sum is -N !=0.
For any nonzero function h with support size s, choose a basis of its
translates. The union of their supports must cover G, because the
union of all translated supports does. Hence s*rank(h)>=N.
As V_h is contained in V_g+K*1, this proves

    rank(g) >= ceil(N/(2k+1))-1.

In particular exact fixed linear translation features need dimension
at least N-1. This bounds a representation, not the cost of a
nonlinear decoder or of constructing features. Arbitrary Hamming
error on the table is a distinct metric.

A further restricted exact result: if the only change is at the
identity, g=ell+c delta_O, then rank(g)>=N-2. Over a splitting
field containing an Nth root of unity, the nontrivial Fourier values
of ell are N/(z-1) or the same expression with z inverted, according
to the transform convention. They are distinct for distinct z!=1.
Adding c shifts each by the same constant, so at most one nontrivial
frequency is lost. This proof uses N nonzero in K.

## 3. Formula lower bound

For nonzero rational denominators,
H(f+g), H(f-g), H(f*g), H(f/g) <= H(f)+H(g);
the division case uses H(1/g)=H(g). The same inequalities hold
when a numerator vanishes identically (height zero).
On a short Weierstrass curve, H(x)=2 and H(y)=3.
Induction on a rational arithmetic formula using +,-,*,/ and fixed
field constants gives H(R)<=2Lx+3Ly where Lx,Ly count coordinate
leaves with multiplicity. Thus

    4Lx+6Ly >= N-1-2k

for the full-label task, or N-2-2k on S. Fixed field constants,
including curve-specific nonuniform advice as constants, are
permitted. The model counts repeated occurrences, and is a tree
without shared intermediate computations. Raw divisions at points
where they are undefined count as failures, even if cancellation
makes the rational function regular.

This is a linear-in-N formula leaf lower bound for fixed success
fraction greater than one half in this field-valued inverse-label
model. A binary-encoded scalar output has a separate, stronger
bound valid even when the characteristic is smaller than N.

## 4. Generic-path bound for injective finite-alphabet outputs

Let U be a finite set of rational points of a smooth projective
geometrically integral curve, with an injective label map
L:U -> A^m, A a fixed subset of K of size a>=2.
Consider a finite decision tree with rational zero tests, having a
distinct exceptional outcome for poles or explicitly guarded failures.
Fix all constants, random coins and the curve. For each rational test
h, the generic outcome is zero if h is identically zero, otherwise
nonzero. Following these outcomes selects a single generic path.
Write H_i for heights of tests along it, and B for an upper bound on
additional undefined-input exceptions (e.g. raw intermediate divisions).
The union of exceptional inputs has cardinality at most

    B + 2 sum_i H_i.

Indeed a nonconstant rational function has at most H_i zeros and
H_i poles. Constant tests have no exceptions. Include any additional
raw domain tests in the guard ledger: a reduced rational function
alone does not account for removable singularities such as X/X.

Suppose the generic leaf outputs m rational functions r_j, of maximum
height D. If all are constant, injectivity allows at most one correct
input. Otherwise choose a nonconstant r_j. For every correct regular
evaluation, r_j lies in A, so it has at most a*H(r_j)<=aD such
inputs by applying the zero bound to r_j-c for each c in A.
No restriction on the outputs on the exceptional paths is needed.

Thus the total number of successes satisfies

    successes <= B + 2 sum_i H_i + max(1,aD).

For uniformly distributed inputs and randomized trees the same
inequality holds after taking expectations, with the right-hand
side evaluated on each fixed random tape. This includes arbitrary
rational tests with fixed coefficients; it does not include arbitrary
bit-level tests or uncharged preprocessing or lookup. For binary
labels a=2, success at constant positive rate requires linear
total height budget. If tests/guards/outputs are formulas and
coordinate leaf occurrences are charged, the same height
inequality gives a linear leaf bound. An uncharged guard budget
can invalidate that implication.

## 5. Why this is not a circuit lower bound

The height of a rational function can double at every shared
arithmetic gate, so depth/gate counting by this argument yields
only logarithmic lower bounds. Over F_p, p odd, the nonconstant
predicate (1-X^((p-1)/2))/2 maps F_p* to {0,1}, with equal
fibres. Every rational representative on that domain has height
at least (p-1)/2, and the displayed formula has exactly that
height. Binary powering computes it in O(log p) gates. This
saturates the alphabet-fibre bound with a small shared circuit.

An explicit field-bit predicate also invalidates a free bit-RAM
conversion: on the canonical integer encoding of F_p, parity is
a single bit read; every rational representative valid everywhere
has height at least (p+1)/2 by fibre counting. In addition, an
equality indicator of a specified nonidentity point has full
translation rank, and can be evaluated by finite-field zero
selectors in O(log q) operations. High rank alone is not a
circuit-size measure.

TRR-12's inexpensive forward group-law circuit is another
required scope control. A genuine polynomial-time breakthrough
in scalar inversion, if one exists, would need analysis outside
the present formula/height bounds. No recovery algorithm or
practical forgery is presented. The unrestricted classical
complexity of the deployed scalar inversion problem is open.

## 6. What remains

The precise research gap is the cost of a shared computation
under simultaneous shift-difference, finite alphabet and
translation-rank constraints. We cannot prove a superlogarithmic
general DAG lower bound from these invariants. Study restricted
resource measures with an explicit sharing and guard ledger,
and retain the sharp predicate controls.

A second precise question is the sharp approximate translation
rank for prime N in tame finite characteristic. The elementary
bound is multiplicative in support and rank. A stronger
N-O(k) bound would need a finite-characteristic replacement for
the characteristic-zero Fourier-minor argument, or a proof
using the special form h=(tau-I)e-N delta_{-T}. This is unresolved.
No claim is made that arbitrary prime-order finite-field Fourier
matrices have all minors nonzero.

The 2026 structured generic-group model of Corrigan-Gibbs,
Henzinger and Wu studies lower bounds when a precisely specified
structured fraction of group elements can be accessed. Its
published bound is Omega(min(sqrt(N),1/delta)) within that model.
Our generic-path exceptional sets depend on the fixed rational
tests and random tape; identifying them with that paper's
structured oracle requires a simulation theorem, not merely an
exceptional-set count. Reference: https://eprint.iacr.org/2026/384
(author abstract: https://people.eecs.berkeley.edu/~henrycg/pubs/structured-generic-groups/).
No such simulation has been proved here.

## 7. Exact controls

Run node verify.mjs and compare the output with receipt.json.
The checks enumerate synthetic cyclic words in 15 cohorts and
all error masks through order 17 (both full and punctured).
They verify the sharp predicate on 24 prime fields and two
generic-path leaf types for each selected pair of test functions.
On six previously documented small smooth curves, evaluate
256 fixed affine-linear quotient expressions per curve, count
regular adjacent differences, count raw denominator exceptions,
and test the binary alphabet fibre bound. The quotient has
height <=3 since numerator and denominator belong to L(3O);
the nonconstant affine-linear quotient is recognized by
nonproportional coefficient vectors. These are predetermined
controls, not an inversion search or performance benchmark.

All mathematical statements here are written proofs, pending
independent review and Lean formalization. The exact checks
are limited to the recorded finite cohorts; they do not certify
a general arithmetic-circuit or ECDSA security theorem.
