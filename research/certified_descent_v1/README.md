# Certified variable-arity descent: tree bounds and potential

2026-11-26. Independent abstraction motivated by [Cogentic's discrete logarithm theorem statement](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/discrete_logarithm/README.md). This note does not reproduce or verify the paper's algebraic lemmas or its announced Lean formalization.

## Uniform depth/arity bound (proved here)

Fix a root-size parameter N >= 2. A finite rooted computation tree has integer size d(v) >= 1 at each node, d(root) <= N. Terminal size is 1; allow earlier terminal nodes. Every internal node has at most A(N) children, each of size <= d(v)/B(N), where B(N)>1; every node has local cost <= C(N) including verification and leaf work. The same bound holds for expected costs if the cost conditional on reaching any node (and its history) is <= C(N), and the tree constraints hold almost surely.

At depth j, size is <= N/B^j, so positive integer size implies j <= floor(log_B N). Induction on levels gives at most A^j nodes at depth j. Therefore total work is <= C sum_{j=0}^H A^j, H=floor(log_B N). For the expected-cost version, label the nodes by child-index sequences, assign zero to absent nodes, and sum their expectations over the finite full A-ary tree.

If A and C are polynomially bounded in N and B(N) tends to infinity with 2 <= B(N) <= N eventually, log(work) <= O(log N)(1+log N/log B) + O(log log N) = o((log N)^2). Hence work is N^{o(log N)}. This is an abstract conditional implication. Establishing a growing B, polynomially bounded A,C, and a valid representation is the domain-specific burden. Expected retry cost must be included: conditional success probability at least q>0 for each attempt and conditional expected cost <= c imply expected search cost <= c/q by a geometric tail argument. A marginal success probability alone does not imply that bound.

## Nonuniform branching (proved here)

For s>=0, suppose every internal node satisfies sum_i d(child_i)^s <= d(parent)^s. Let Phi_j be the sum of d(v)^s over nodes at depth j. Induction gives Phi_j <= N^s. Since d(v)>=1, the number of nodes at that depth is <= N^s. A tree of height H and local costs <= C thus costs <= C(H+1)N^s.

A more useful amortized condition for variable local work c(v)>=0 and any nonnegative potential P(v) is
    c(v) + sum_i P(child_i) <= P(v)
at all nodes, including leaves. Sum over the tree; all nonroot potentials cancel, giving total work <= P(root). This can be applied to arbitrary finite trees even with unequal branching. For positive integer sizes and strict shrinkage, finiteness follows if each node has finitely many children. Do not apply a tree sum to a DAG without accounting for whether shared nodes are charged once or per visit.

## Bellman target for a learned router

Let F(s) be a public admissible certificate bank at state s. For deterministic finite acyclic subproblems, independent additive costs and all children required, define
    J(s) = min_a [c(s,a) + sum_{u in children(s,a)} J(u)]
with explicit terminal costs. The recursion is proved by induction on height. This is an AND-OR search objective; one successful child is insufficient. A per-step log degree-reduction reward alone can favor a policy that increases total work. With uncertain proposals, charge failed attempts, memory and construction separately; avoid comparing policies with unequal proposal budgets.

## Formalization plan

Lean targets: (1) level population bound by induction over lists of sizes; (2) power potential conservation for natural exponent; (3) recursive Nat-cost telescoping over finite trees; (4) asymptotic corollary using logarithms. Lean compiler was unavailable during this work; these are paper proofs, not checked Lean declarations. The DataGoblin companion is a public-witness routing proxy rather than a factoring or DLP solver.
