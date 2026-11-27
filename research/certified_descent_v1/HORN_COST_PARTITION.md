# Goal-threshold cost partitions for acyclic Horn proof planning

ALG-DESCENT-13 companion. Independent elementary paper proofs in the synthetic planning domain; no novelty claim, no Lean check. Let R be a finite acyclic positive-cost Horn rule table with one head per rule and earlier premises, current known facts S, goal G, and a finite successful continuation P (only new heads need be added). Let J_c(S) be minimum continuation weight for nonnegative rule costs c. Rule identity and statement scope are fixed.

## Mandatory facts

For each fact h, M_S(h)=empty if h is known; otherwise
    M_S(h)={h} union intersection_{r:head=h} (union_{q in premises(r)} M_S(q)).
Every proof of h contains these unknown facts by induction on the topological order. Conversely, for any fact x outside M_S(h), there is a proof of h avoiding x: choose a rule whose premises' mandatory sets all exclude x, recursively choose proofs avoiding x for each premise, and execute their union in topological order, sharing already derived facts. Thus M_S(G) is exactly the set of unknown facts present in every proof of G under these assumptions. Since each new head needs a rule, and distinct heads have disjoint deriving-rule sets, sum_{h in M_S(G)} min_{r:head=h} c_r <= J_c(S). The argument also holds for residual nonnegative costs.

## Unavoidable cuts

For residual costs a>=0, let d(h)=0 for h in S, otherwise
    d(h)=min_{r:head=h} (a_r+max_{q in premises(r)} d(q)).
By the usual hmax induction, d(G)<=J_a(S). Let H=d(G)>0 and take Z={h in the full backward ancestor closure of G : d(h)>=H}. G belongs to Z; S is disjoint from Z. Define C={r:head(r) in Z, premises(r) disjoint from Z}. Any successful proof must enter Z for the first time, using a rule in C. Hence removing all rules in C makes G unreachable. Every r in C has strictly positive residual cost: the recurrence gives d(head)<=a_r+max d(premises), all its premises are ancestors with distances below H, and the head distance is at least H. If a_r were zero this would contradict the threshold. Therefore delta=min_{r in C} a_r>0.

Set a'_r=a_r-delta for r in C, unchanged elsewhere. For every successful P,
    cost_a(P)-cost_{a'}(P)=delta * number of rule occurrences of P in C >=delta.
Consequently J_a(S)>=delta+J_{a'}(S). Starting from a^(0)=c, a sequence of cuts gives J_c(S)>=sum_{j<=k} delta_j+J_{a^(k)}(S) for every prefix k. Each iteration makes at least one positive residual cost zero and never increases a residual cost, so there are at most |R| iterations. Stop when residual d(G)=0. The admissible combined bound is
    B(S)=max_k [sum_{j<=k}delta_j + max(d_{a^(k)}(G), mandatory_cost_{a^(k)}(S))].
This includes prefix zero, so it dominates the original hmax and mandatory bounds. A cut certificate can be checked independently by deleting each cut, verifying unreachability, checking residual charges and then checking a residual lower bound; no reliance on the generator's particular threshold heuristic is necessary for soundness. The algorithm here uses the specified threshold to find such cuts, and the audit checks it too.

## Lazy refinement for an anytime certificate

Let b_0(s)<=b_1(s)<=J(s) be valid lower bounds, possibly unequal computational costs. Maintain each unresolved state with its presently certified value b(s) in {b_0,b_1}. A refinement only raises the key for that state, or permits pruning if g+b_1>=U. OPEN coverage is unchanged otherwise. Thus L=min(U,min_OPEN(g+b))<=J(initial)<=U at every interruption. If the next chosen lowest key is coarse, refine and reinsert or prune before expansion; if it is already refined, expand. With finite states and one refinement per state, exact duplicate handling and eventual completion under sufficient budget, the same optimality certificate remains sound. More general refinement stages require individually admissible bounds and retention of all unresolved states. No claim of identical expansion order or wall-clock superiority. A learned policy may decide when to request a stronger bound, while only certified bounds govern pruning. Charge refinement work and memory; finite-cap certificates must retain lower-bound coverage.

## Development evidence

V13 fresh 36 roots, four arms, 864 snapshots. All 6,199 evaluated lower bounds checked against exact Bellman values; 13,018 unavoidable cuts verified by independent reachability deletion. OOD combined bound capped mean expansions 13.0417 vs hmax 19.6667, 20 wins/4 ties/0 losses, 24/24 vs 23/24 certified by 128. On jointly certified roots 9.3478 vs 14.9565 expansions. Measured runtime higher (5.353 vs 1.355 ms). Pure cut bound 13.1667 expansions and 4.477 ms. These are synthetic search results, not general proof-complexity or cryptographic results. DataGoblin PR #89.