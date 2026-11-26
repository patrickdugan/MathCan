# Independent mathematical review: inverse-label rigidity

Context: this is Strategy V of a defensive ECDSA security assessment.
The objective is restricted-model lower bounds and explicit
counterexamples to overbroad complexity claims. Do not design or optimize
a key-recovery or signature-forgery method. No deployed keys, real-system
targets or production-curve experiments.

Let E/K be a smooth elliptic curve, G=<T> of odd prime order N, N nonzero
in K. Write ell(jT)=j*1_K for 0<=j<N. Distinguish this residue-valued
label from an injective bit encoding of the scalar.

Established written arguments in TRR-13:
(1) If a rational R agrees with ell except k failures, then
2 H(R)>=N-1-2k, H the geometric pole degree. Indeed
F=R(P+T)-R(P)-1 is nonzero by telescoping N shifts and has at least
N-1-2k distinct regular zeros. On G minus O replace N-1 by N-2.
(2) For g=ell+e with |supp e|<=k,
h=(tau-I)g-1=(tau-I)e-N delta_{-T} has nonzero sum -N and support <=2k+1.
Rank(h)*|supp h|>=N by the translated-basis cover argument;
rank(g)>=ceil(N/(2k+1))-1. Exact rank is N-1 or N according to
whether the sum of ell vanishes. One edit at O loses at most one
nontrivial Fourier frequency.
(3) In a rational formula, H(R)<=2Lx+3Ly. For arbitrary shared
DAGs, height can grow exponentially per number of gates.
(4) A rational equality decision tree, on its generic path, has
at most B+2 sum H(test_i) exceptional inputs, including raw
division guards B. An injective binary output has at most
max(1,2 max_j H(output_j)) successes on that path.

Please audit these proofs, including extension fields, finite
characteristic, arbitrary fixed constants, pole cancellation and
raw guards. Preserve the distinction between a rational function
and the expression computing it.

The specific unresolved algebra problem is:

For prime N and tame characteristic, determine useful sharp
lower bounds on the rank of the cyclic translation matrix of
ell+e for k=1,2 and general small k. Investigate whether the
special structure h=(tau-I)e-N delta_{-T}, with sum h=-N,
forces stronger rank bounds than ceil(N/(2k+1))-1 uniformly
over finite fields, or produce exact synthetic counterexamples.
The characteristic-zero additive uncertainty bound cannot be
imported into positive characteristic without proof. Record
which field hypotheses are indispensable. A proof for a restricted
class of error supports or field sizes is useful; do not claim
a general result without checking all cases.

Then assess whether any *proved* stronger rank statement gives
a resource-preserving lower bound in a precisely specified linear
feature or formula model. A generic shared circuit lower bound
remains open here. Required controls:
- A point-mass function has full translation rank but easy finite
  field zero selectors.
- On F_p*, (1-X^((p-1)/2))/2 has optimal rational height
  (p-1)/2 and O(log p) shared evaluation cost.
- TRR-12's forward group-law decoder has a small circuit despite
  the exact high interpolation degree.

If a stronger lower-bound model is proposed, write its exact
assumptions and account for sharing, evaluation domains, guard
costs, randomization and any precomputed data. Prove a concrete
lemma or give a counterexample; distinguish mathematical evidence
from a security reduction. Do not infer a general scalar recovery
complexity theorem from these controls.

Return a proof review with the strongest supported statement,
an exact finite verification plan for synthetic functions, and
a specific remaining proof obligation.
