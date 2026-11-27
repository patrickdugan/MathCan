# Exact live-cone continuation quotient for monotone Horn proofs

ALG-DESCENT-19 companion, 2026-11-27. Written proof, no Lean check. Fix a finite acyclic weighted Horn rule graph with one head per rule, earlier premises, positive costs, immutable rule IDs and fixed goal G. Known facts S are persistent; legal new-head actions add exactly one fact. A(S) is the smallest set formed by starting at unknown G, and for every h in A(S) including every unknown premise of every rule deriving h. Stop at facts in S. A(S)=empty when G is known.

## Restriction and monotonicity

Backward extraction from a concrete successful derivation retains the rule deriving G and recursively the rules deriving its unknown premises, stopping at S. Every retained head lies in A(S), and their original order is executable. Omitted positive-cost rules only increase cost. In an optimal proof no first action has head outside A(S); otherwise extraction removes that action and gives a strictly cheaper proof. Repeating at each suffix proves that restricting live actions preserves the optimal continuation value J(S). A(S union T) is contained in A(S) because any path of unknown dependencies that remains after adding facts was already such a path before.

## Exact quotient theorem

Suppose A(S)=A(T)=A. For each rule r whose head is in A, every premise p is either in A or known in S by closure of the cone; similarly for T. Thus for such a rule, p is unknown in S iff p is in A, iff p is unknown in T. Its head is unknown in both. The live rule is legal in S iff legal in T, equivalently prem(r) is disjoint from A. Rule IDs and costs agree under the immutable graph scope.

For a legal live action deriving h, the new cone is the closure from G using unknown-fact mask A minus {h}: start at G if still unknown and recursively include only premises in this mask. Indeed monotonicity prohibits new members outside A, and each surviving dependency path inside A minus {h} has exactly the same unknown/known status as in S union {h}. Therefore A(S union {h})=A(T union {h}), deterministically computed from A and h alone. It is a strict subset of A. A=empty is precisely the goal-satisfied terminal class. This gives a cost-labelled transition-preserving quotient of the live-restricted graph, without identifying arbitrary non-live transitions. Induction on |A| establishes identical optimal continuation values and identical legal rule-ID suffix choices for all states in one class.

A quotient Bellman recurrence is
    V(empty)=0
    V(A)=min over r with head in A and prem(r) intersect A empty of
       [c(r)+V(next(A,head(r)))].
For reachable A, V(A)=J(S). Treating all facts outside A as known is valid for this recurrence only on live heads; it is not a claim that those outside facts have actually been derived. hmax and additive/FF continuation calculations depend only on A, by induction on deriving-rule prerequisites. Their proof suffix can be replayed on any representative S of A.

## Certified search and witness accounting

Under the same rule/goal scope, retain the least prefix cost g per class and a concrete executable prefix witness. Every legal live suffix for a discarded representative is legal on the cheaper representative by the quotient theorem. Hence dominated larger/equal g prefixes can be discarded for minimum additive proof cost, with cheaper reopen as needed. Do not invent proofs for all outside facts or use a stale path after dominance changes. Store an immutable concrete witness, or update and verify it under exact representative semantics. Verified incumbent proof plus admissible frontier minimum remains sound if all improving quotient continuations are covered. Do not infer permission, proof trace identity, or equality of arbitrary state predicates from cone equality. Registry, goal, initial facts and authorization context must be fixed. The theorem does not cover destructive rules, costs dependent on hidden history, side conditions outside public premises, negative costs, arbitrary cyclic rule graphs, or general Lean proof states.

## Development checks (spent cohort)

V19 independent audit: all 48,617 full-reachable states agree with static and live restricted optimum. 180,896 monotonicity checks. Retrospective grouping compares exact cost and complete live rule-ID/cost/successor-cone signatures in every class; 235,222 strict live transition checks. OOD 47,307 full-reachable states and 10,294 root-local cone classes (78.24% aggregate reduction; 71.78% mean root reduction). This is a state-space diagnostic, not a measured quotient-search speed or allocated memory claim. Native V19 uses full keys, and static support is faster than dynamic filtering. See DataGoblin PR #89; future native quotient benchmark requires fresh roots and independent concrete proof replay. No Lean, native BPD/MMS or cryptographic claim.