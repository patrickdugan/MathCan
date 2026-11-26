# Exact sequential product cost potential (ALG-DESCENT-03)

Independent elementary lemma for a toy certificate verifier. Let d_i>0 for i=1..k, d=sum_i d_i, S_i=sum_{j<i}d_j. A sequential schoolbook product initialized at polynomial 1 charges c=sum_i (S_i+1)(d_i+1) coefficient multiply-adds, since the accumulator and child have degrees S_i and d_i. Expanding and using sum_i S_i*d_i=sum_{j<i}d_j*d_i=(d^2-sum_i d_i^2)/2 gives

    2c = d^2 - sum_i d_i^2 + 2(d+k+sum_i S_i).

For any finite rooted tree of positive degrees where children sum to the parent degree, sum this identity at all internal vertices. Every nonroot internal degree square cancels. Therefore, for root degree n and leaf degrees l_i,

    2W = n^2 - sum_i l_i^2 + 2 sum_internal(d+k+sum_i S_i).

For linear leaves sum_i l_i^2=n. This is an equality for successful, uncached verification using the stated multiplication meter. Extra rejected attempts add their actual cost; shared cache hits change the tree accounting. Other multiplication algorithms or initializing from the first child use different overheads. Child order matters through the prefix sum.

The v3 heuristic c+sum_i d_i^2/2 equals d^2/2+d+k+sum_i S_i; the root-state quadratic term is constant across candidates. A Bellman recursion can subtract the invariant (d^2-d)/2 for all successful uncached subtree costs. For each valid action the remaining immediate cost is O=d+k+sum_i S_i plus child overheads. A failed attempt leaves the same subproblem, adding its charged work. Keep risk separate. This gives a scale-structured target, not a claim that its learned estimator generalizes.

Audit (DataGoblin companion): 32,132 local identities and 1,000 generated complete trees checked using integer arithmetic. Paper proof above independent of samples; Lean formalization remains outstanding. Proposed Lean proof avoids division by two: establish cross-term identity by induction on degree list and telescope with tree recursion.

See [DataGoblin PR #89](https://github.com/MoralityLabAI/DataGoblin/pull/89) for source and development receipt.
