# CLN-06 / CLN-07 staging: probability, explicit schedule, remaining proof bridges

Base PR #274 head 5067378b6c240142f5f3d9e5701a29b8a3b32e5a.
Run 45379618480 was still queued on inspection. This branch is separate
so the upstream kernel run is not canceled. No Mathlib proof on this
branch has a kernel receipt yet.

## Probability source map

CLN06A proves independent prefix/tail product integration, a uniform
conditional bound under the product law, a finite mixture identity
and almost-sure convergence from a summable majorant.

CLN06B targets independent product coordinates, independence after
measurable maps of disjoint coordinate sets, and exact fair-cylinder
mass. Mathlib v4.35.0 source interfaces were inspected:
- Mathlib/Probability/Independence/InfinitePi.lean: iIndepFun_infinitePi
- Mathlib/Probability/Independence/Basic.lean: iIndepFun.indepFun_set,
  IndepFun.comp, iIndepFun.measure_inter_preimage_eq_mul,
  indepFun_iff_map_prod_eq_prod_map_map
- Mathlib/MeasureTheory/Measure/Prod.lean: lintegral_prod_symm'
- Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean: lintegral_fintype
- Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean: lintegral_map

To instantiate the digit model choose the fair measure on Bool,
take the countable independent product, and map each bit to one of
two distinct digits at each free index. Forced positions ignore the
bit. Prove that the finite base-Q integer prefix has unique digit
encoding; a nonempty fiber fixes exactly the free bits in that
prefix, hence mass 2^(-s(k)). A nonexistent prefix has mass zero.
Use measurable finite sums and limits of uniformly converging tail
sums to obtain the two maps for CLN06B. Verify that the prefix law
has the corresponding atom masses; this is still an open Lean gate.

For the general conditional theorem use a finite-index probability
kernel for the prefix given the tail, or a finite joint-law
disintegration. The independent case is a specialization, not a
proof of the dependent case. CLN06A's finite mixture target alone
does not establish that conditional kernel. Derive the exact
conditional weighted integral via the law of total expectation.

## Grid proof, finite to infinite

For M=Q^k and integer J>0 choose j=floor(J(N-M)/M) for M<=N<QM,
so 0<=j<(Q-1)J and N0=M+floor(j*M/J) <=N.
The division inequalities give
N-N0 < M/J+1 in real arithmetic.
For a sequence with |u_n|<=1, let W_N=(sum_{n<N} u_n)/N.
Then |W_N| <= |W_N0|+(N-N0)/N <= |W_N0|+1/J+1/M.
For every fixed J and grid index j, the expected squared energy is
bounded by the same summable sequence (1+K)alpha_k. CLN06A yields
almost-sure convergence for each grid. Intersect over integer J,
the finitely many j for each J, h>0, and coprime b. For each J
the finite grid maximum tends to zero. Since M tends to infinity,
limsup_N |W_N| <= 1/J for every J; hence it is zero. Conjugation
of the Weyl sum handles negative h. For the Weyl criterion either
locate a verified Mathlib theorem or prove it using the density of
trigonometric polynomials in continuous functions on the circle
and continuous upper/lower approximations to interval indicators.
Do not substitute convergence of the Fourier coefficients for
the word-frequency conclusion without proving this last bridge.

## A simpler Liouville schedule

Set d_j=2^(j+2), m_j=2^d_j for j>=0. Free positions are integers
in (m_j,2m_j], all other digits zero. Then m_0=16 and
m_(j+1)=m_j^2. The blocks are disjoint. For 2m_j <= k < 2m_(j+1)
we have s(k)>=m_j. Because d_j>=j+2 and 2^d_j>=3*d_j,
m_j>=2*d_j+j+2. Therefore the contribution of that entire k block is

  sum 2^(-s(k)) <= 2*m_(j+1)*2^(-m_j)
                 = 2^(1+2*d_j-m_j) <= 2^(-j-1).

The initial finite prefix contributes a finite amount, proving
summability. This square recurrence replaces the earlier much
faster schedule only to simplify the formal proof.

For any realization with infinitely many nonzero digits, the
truncation denominator is Q^(2m_j) and the error is positive and
at most Q^(-m_(j+1)). Since m_(j+1)/(2m_j)=m_j/2 tends to infinity,
the error beats every fixed power of the denominator. The usual
rational separation argument proves irrationality. Infinitely
many nonzero digits holds with probability one: the event of all
future free bits being zero has measure at most 2^(-r) for every r;
the event of finitely many nonzero bits is a countable union of
such null events.

For bases containing all prime factors of Q, choose t_j=O(m_j)
so Q^(2m_j) divides b^t_j, and U_j=floor(m_(j+1) log Q/(2 log b)).
For t_j<=n<=U_j the truncated rational contribution is integral
and the remainder is at most Q^(-m_(j+1)/2)<1/b eventually. Thus
zero digits have limiting subsequence frequency 1. In prime-power
source bases this gives the full normal/non-normal classification
across integer bases. For composite sources with partial common
prime factors the exclusion claim remains deliberately narrower.

This argument is a written mathematical derivation, not a compiled
Lean theorem. The schedule, digit series, Liouville definition and
word-frequency definitions must appear in the final formal target.

## Receipts and next action

CLN01: 12 Lean targets + 4 regression tests verified at 45377255846.
CLN05 fixed composite constant: 2112 exact finite checks independently
rerun in the sandbox this turn. CLN02–05: queued, no compiler output.
No local Lean executable and GitHub release download unavailable in
the sandbox. CLN06A/B: 7 staged source targets, not yet compiled.

Resume by fetching run 45379618480 for its original commit; fix
compiler errors in order. Once the upstream gate is green, integrate
these staged files and audit changes into the PR; reconcile the
ledger at that time. Keep the final theorem dependency audit and the
distinction between general conditional laws and independent digits.
