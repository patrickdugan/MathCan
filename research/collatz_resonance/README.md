# Collatz resonance (COL)

Source: supplied manuscript, *Prescribing cycles in a Collatz-like map by quadratic reciprocity*, 25 November 2026. This note records deductions and proposed experiments; manuscript priority and empirical receipts require independent audit.

For positive d = 1 mod 4, S_d(n) halves even n, sends n = 1 mod 4 to 3n+d, and n = 3 mod 4 to n+d. The accelerated odd map has a finite absorbing core [1,d].

## Exact deductions
For a cycle with u triple branches and A halvings, let g=gcd(n,d) at any cycle member (assuming gcd(d,6)=1). Then 2^A = 3^u mod d/g. On units this yields a rank-two lattice in (u,A). The full periodic invariant is the orbit of n mod d under <2,3>, by manuscript Theorem 4. For primes p_i = 1 mod 24, individual Legendre symbols are invariant; CRT and Dirichlet permit k auxiliary primes separating all 2^k subset products of distinct primes q_j>3. Ternary sign vectors imply at least 3^k cycles, including at least 2^k unit cycles.

## Research plan
- COL-01: Lean finite core, cycle product congruence, and conditional reciprocity construction.
- COL-02: exact lattice basis by CRT / integer normal forms; verify against direct modular exponentiation.
- COL-03: preregister held-out parameter census, compare shortest near-slope-six resonance against observed counts; compare random mapping and size-only baselines. The slope is a 2-adic heuristic, not a theorem about cycles.
- COL-04: distinguish same-class basins with nonperiodic certificates and quantify complexity.
- COL-05: derive rigorous lower bounds using the lattice and A>=2r>=2u, and investigate stronger inequalities.
 
## Applications
EvalMath: invariant discovery, counterexamples to completeness, proof-certificate search, held-out parameter splits. LoopedTransformers: recurrent state probes against exact quotient labels; separate basin identity from invariant identity; equal-budget random and oracle controls. Compactification-Theory: measure collision-induced error of exact finite quotient versus richer compressed state. DataGoblin: generate verified traces and proof obligations with parameter-level deduplication. Storyworlds: construct deterministic hidden-state puzzles with preserved observables and distinct terminal outcomes.

Prior conversational census reports 137 cycles at d=160833217, 55 unit cycles, with 53 sharing (u,A)=(3546,21230) and 2 sharing (9116,55912). These figures are provisional until the census artifact is replayed. The source manuscript reports 95 periodic classes and 137 cycles. No claim of applicability to ordinary Collatz convergence is made.
