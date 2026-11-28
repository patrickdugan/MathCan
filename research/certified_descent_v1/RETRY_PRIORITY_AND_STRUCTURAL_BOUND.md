# Independent priority theorem and exact relaxed overhead (ALG-DESCENT-04)

Motivated by the public-witness algebraic routing gym; no claim about the underlying Cogentic finite-field theorem or elliptic-curve hardness.

## Fixed-order retry priority (paper proof)

Suppose there are finitely many candidate attempts i. Attempting i costs C_i >=0 and independently succeeds with fixed probability p_i in (0,1]. On success pay a fixed expected continuation V_i>=0 and stop. Otherwise proceed to the next candidate. All-fail fallback has fixed expected cost F. For a given suffix expected cost T, trying i then j costs
    C_i+p_i V_i+(1-p_i)(C_j+p_j V_j+(1-p_j)T).
Swap i,j. Subtract swapped cost from original:
    p_j C_i-p_i C_j+p_i p_j(V_i-V_j)
  = p_i p_j[(C_i/p_i+V_i)-(C_j/p_j+V_j)].
The probability of reaching this pair is nonnegative. Thus swapping an inverted adjacent pair cannot increase total expected cost; a sorted fixed order minimizes it. Under these assumptions observed failures convey no information about remaining success probabilities or continuation costs; conditional histories cannot improve the order. If attempts are correlated, posterior probabilities or V_i depend on history, or a budget changes after each attempt, the exchange argument does not establish an optimal adaptive order. Zero-probability attempts need separate handling (can be discarded if optional, placed last if forced).

## Structural potential

Let M(d)=d(d-1)/2. For ordered positive child degrees d_i summing to d, c = M(d)-sum_i M(d_i)+O(d_1,...,d_k), O=d+k+sum_i (k-i)d_i (i starts at 1). See SEQUENTIAL_PRODUCT_COST.md. Define L(1)=0 and
    L(d)=min_{k in {2,3,4,8}, k<=d; d_i>=1; sum d_i=d}
          (O(d_1,...,d_k)+sum_i L(d_i)).
By strong induction this is the minimum structural overhead over unrestricted ordered degree trees with linear leaves and these arities. It is a lower bound for any fixed algebraic certificate bank, since the relaxation includes every allowed degree partition and may admit unrealizable partitions. For a chosen candidate, O+sum_i L(d_i) is its lower bound on successful overhead. The minimization for fixed k can be implemented via a prefix dynamic program (prefix sum, number of children), with additive costs L(x)+(k-i)x. Strict positivity and k>=2 ensure every L(x) referenced has x<d. With fixed arity set and integer degrees, O(d^3) time computes all L(1)..L(d) using this elementary DP, and O(d) rolling DP working memory plus the table of prior L values.

For a candidate whose successful downstream cost is V_i=sum M(child degrees)+estimated downstream overhead, subtracting M(d) from C_i/p_i+V_i leaves O+estimated downstream overhead+C_i(1/p_i-1). This suggests separate supervision of overhead and rejection probability. It is a heuristic on correlated synthetic banks; do not assume its calibrated success probability transfers to other families.

## Audit

Independent code enumerated 4,459 ordered compositions for degrees 2..14 and matched L exactly, using direct schoolbook work expansion. On 300 exact rational probability instances with 2..5 candidates it checked all 11,594 permutations against the priority order, with a fixed all-fail fallback. The algebraic paper proofs above do not depend on the finite checks. See DataGoblin PR #89. Lean formalization outstanding.
