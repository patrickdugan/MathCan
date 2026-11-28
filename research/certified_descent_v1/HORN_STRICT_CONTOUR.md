# Strict admissible contours and certification work

ALG-DESCENT-12 companion (2026-11-27). Paper argument; no Lean verification.

Let S be the initial proved set. Transitions apply a public positive-cost Horn rule to add one new fact. Stop upon reaching the goal. For reachable state s, d(s) is minimum prefix cost from S in this terminal-goal state graph. Let C* be the optimum proof cost.

## Consistency of hmax

For each state s, define v_s(p)=0 for known p; otherwise minimize c(r)+max_{q in prem(r)} v_s(q) over rules deriving p (empty max is zero). Rules are acyclic and fact indices topological. A legal action of cost c adds fact a to produce t. Then v_s(p)<=c+v_t(p) for every fact p. For already-known facts the claim is trivial. For a, the applied rule is an available proof with cost c. For every remaining unknown p, choose a rule minimizing v_t(p); its premise values satisfy the inequality by topological induction, hence its cost plus the max of premise values is bounded by c+v_t(p). Nonnegative c handles an empty premise set. Thus hmax(s)<=c+hmax(t). Along any path g+hmax is nondecreasing.

## Strict-contour lower bound

Consider the frontier-based algorithm of V12: enumerate every applicable successor (minimum-cost same-head transition suffices); keep exact state identity and best prefix cost; reopen when cheaper; prune only by g+h>=U for verified incumbent U, or exact best-g dominance. Final certification requires U=C* and no frontier entry below U. Assume h is consistent and admissible. Every nonterminal reachable state s with d(s)+h(s)<C* must have been expanded at its optimal prefix cost d(s).

Proof: follow a shortest prefix path to s. Every path prefix is itself shortest, and consistency gives all prefix f values <= d(s)+h(s)<C*. Initial state cannot be pruned. Induct along the path. An expanded prefix at optimal g generates the next prefix at optimal g; no admissible incumbent pruning is possible since U>=C*. Exact dominance can discard that arrival only if an equal-cost arrival already exists. If it is not expanded at optimal cost, it must remain unresolved in OPEN at certification, a contradiction. Hence each strict-contour state is expanded. This lower bound applies to the specified full-successor, exact-dominance and scalar-bound architecture; stronger valid pruning, abstraction, improved bounds, or other proof certificates can escape it.

If an optimal incumbent is already available, consistent min-f ordering with correct dominance expands exactly the strict contour before certifying. With a worse initial incumbent, equality-contour work or other extra expansions can occur. Model ranking alone cannot avoid mandatory strict-contour work while preserving this certificate.

Retrospective audit on V12 public development roots: 181,562 deduplicated successor edges consistent, 360/360 certified traces covered all forced states at optimal g. OOD strict count mean 17.6667 vs A* 17.75; A* hits strict count on 22/24, no expansions with f>C*. This is an explanation of the failed ranking gate on this finite problem family.

## Stronger admissible bounds

For each unknown fact p, define mandatory-fact set M_s(p) = {p} union the intersection across rules r deriving p of the union of M_s(q) over its premises q. Known facts have empty sets. In this acyclic system, induction shows every successful proof of p from s derives all facts in M_s(p): select the rule first deriving p, then each premise must have a proof from s within the prefix. Taking intersection makes the result independent of selected rule. Let m(p) be the minimum cost among rules with head p. Distinct mandatory facts require distinct head-adding rule applications. Therefore sum_{p in M_s(goal)} m(p) is admissible, and its max with hmax is admissible. Consistency is not assumed until proven or verified; use reopen-safe search. More general cost partitions and landmark cuts may further tighten the bound. Compare bound strength, construction time, frontier size and strict contours on fresh roots before spending more on rank learning.

No factoring, discrete-log or cryptographic claim.