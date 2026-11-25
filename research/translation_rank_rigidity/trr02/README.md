# TRR-02: exact minimum translation rank at a prescribed cyclic period

**Evidence:** written algebraic proof and independent finite verification. The Lean realization of the finite-field polynomial theory is open. This is a theorem about finite linear recurrent representations, not a lower bound for arbitrary circuits.

## Statement

Let K=F_Q, Q=p^s with p prime, and M=p^a m, gcd(p,m)=1. Define R_Q(M) to be the minimum translation rank among nonzero K-valued functions on C_M having exact period M. R_Q(1)=1. Write m as the product of its distinct maximal prime powers t_i. For a subset B of these indices define w(B)=ord_{prod_{i in B} t_i}(Q), equivalently lcm_{i in B} ord_{t_i}(Q), and w(empty)=1.

If a=0 and M>1, then R_Q(M) is the minimum of sum_{B in P} w(B) over set partitions P of the indices. If a>0, choose a distinguished subset B_* (possibly empty) and a partition P of its complement into nonempty blocks. Then

    R_Q(M) = min [(p^(a-1)+1) w(B_*) + sum_{B in P} w(B)].

In particular, for a>0, R_Q(p^a)=p^(a-1)+1. The zero function is excluded, including at M=1.

## Proof

Identify the function vector with an element F of K[X]/(X^M-1), so the shift acts as multiplication by X or X^{-1}, depending on the sign convention. Its cyclic translate module is isomorphic to K[X]/(g), where g=(X^M-1)/gcd(F,X^M-1) is monic. Its dimension is deg(g). The period is the order of X in the unit group of K[X]/(g). Conversely, every nonconstant monic g dividing X^M-1 is realized by the nonzero vector F=(X^M-1)/g: the annihilator of F is exactly (g), by cancellation in K[X].

Factor X^M-1=(X^m-1)^(p^a). The polynomial X^m-1 is square-free. Write g=prod_j P_j^b_j with distinct monic irreducible P_j dividing X^m-1 and 1<=b_j<=p^a. Let n_j be the multiplicative order of a root of P_j; then n_j|m and deg P_j=ord_{n_j}(Q), with ord_1(Q)=1. This follows from the Frobenius orbit length of a primitive n_j-th root. Conversely an irreducible of exactly that degree exists for each n_j|m.

The order of X modulo P_j^b_j is n_j p^c_j, where c_j is the least c>=0 such that p^c>=b_j. To see this, X^n_j-1 contains P_j exactly once (n_j is prime to p). For any positive integer L, P_j divides X^L-1 iff n_j|L. Writing L=n_j p^c u with p not dividing u, the identity X^L-1=(X^(n_j u)-1)^(p^c) shows that its P_j multiplicity is exactly p^c. The least admissible L is therefore n_j p^c_j. Chinese remaindering gives exact overall period lcm_j(n_j p^c_j), and rank sum_j b_j ord_{n_j}(Q).

For a=0, a feasible list of factors must cover each maximal prime power t_i in at least one n_j. Assign each t_i to one such factor. Replacing each n_j by the product of its assigned prime powers can only decrease its order degree, since multiplicative order on a divisor divides the original order. Drop factors with empty assignments. The resulting partition cost is at most the original rank. Conversely take one irreducible factor of the corresponding order for each nonempty block. The orders are distinct, since the blocks are nonempty and disjoint; the resulting irreducibles are distinct, their product divides X^M-1, and its period is M. This proves equality.

For a>0, some factor has c_j=a and hence b_j>=p^(a-1)+1. Mark one such factor before assigning the maximal tame prime powers. Unmarked factors can be reduced to exponent one; retain the marked factor at exponent p^(a-1)+1 even if its assignment is empty. A marked empty block uses P=X-1. The same divisor-degree monotonicity proves the lower bound by the marked partition cost. Conversely construct the distinct irreducibles for the chosen blocks with the indicated multiplicities. Each multiplicity is <=p^a. Their orders have lcm M and the rank is the formula's cost. This proves the wild-characteristic statement.

## A three-way interaction in rank allocation

Over F_2 take the three prime-power orders 9,11,151; their Frobenius degrees are 6,10,15. Every pair has lcm 30, greater than its separate cost (16,21,25). The triple also has lcm 30, which is less than the separate total 31. Thus R_2(14949)=30: checking only beneficial pair merges misses the optimal grouping. This is a finite representation-allocation example, not a complexity assertion about the partition search.

A subset DP computes the theorem's minimum: for nonempty S fix one distinguished element i and minimize w(B)+F(S\B) over B containing i. F(empty)=0. The wild formula minimizes (p^(a-1)+1)w(B)+F(full\B) over all B including empty. The subset recurrence enumerates O(3^t) candidate transitions, with O(2^t) storage, after the prime-power factors and their orders are known. Factorization and order-computation costs are excluded; no efficient integer factoring claim is made.

## Verification

Run `python verify_min_rank.py` (standard library). It independently compares the marked-partition formula with a shortest-path DP over possible divisors and local factor orders for 1,600 (Q,M) cases (10 field sizes, M=1..160). It also directly enumerates every word for binary periods 1..15, ternary periods 1..9 and quinary periods 1..6, computes aperiodicity by checking shifts of prime order, and computes translation rank by polynomial gcd. All 114,587 words were enumerated; 113,909 were nonzero and aperiodic. Every minimum matches the formula. The three-way example was independently checked by the divisor DP. `receipt.json` records the exact minima and source hash. These finite checks supplement the proof.

The earlier TRR-01 kernel check remains separate. No new Lean kernel verification is claimed here. The natural next formalization is the square-free factorization and root-order/multiplicity identity in a Mathlib project, followed by the marked-partition reduction. The current MathCan root package uses Init only.
