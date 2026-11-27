# PGC-SNF-01: gauge quotient, Smith invariants and finite phase aliases

## General mathematical statement

Let X be a connected finite two-dimensional CW complex with V vertices, E oriented edges and F oriented 2-cells. Fix a spanning tree and set the V-1 tree edge phases to zero by a vertex gauge transform. The remaining g=E-V+1 chord phases determine the gauge class uniquely (up to the constant vertex gauge). The restriction of the integer face coboundary to these chord coordinates is an F by g integer matrix A.

Use normalized phases in T=R/Z; multiply by 2π to recover radians. The observation map is A:T^g→T^F. The Smith normal form theorem supplies unimodular matrices U,V with UAV=D, where D has r nonzero diagonal entries d1|...|dr. Both transformations induce torus automorphisms. Thus the homogeneous invisible phase group is

    ker(A) ≅ T^(g-r) × ∏_{i=1}^r Z/d_i Z.

Every nonempty observation fiber is a translate of this kernel. The continuous dimension g-r is the first Betti number of X over R. The finite cyclic factors give discrete phase ambiguities arising from the integral presentation (torsion in H_1(X;Z)). A rank-complete observation system still admits finite ambiguities if a Smith invariant exceeds 1.

For a finite cyclic phase grid of size M, the number of invisible gauge classes is exactly

    |ker(A mod M)| = M^(g-r) ∏_{i=1}^r gcd(M,d_i).

Proof: unimodular maps are invertible modulo M, a zero diagonal coordinate admits M choices, and d_i x=0 mod M has gcd(M,d_i) solutions. For arbitrary observed data, the transformed coordinates must lie in the image of the corresponding diagonal maps; if they do, the fiber has the same cardinality.

## Executed audit

The dependency-free Node reference calculates the determinantal divisors using exact BigInt minors and exhaustively enumerates the finite cyclic kernel. This is appropriate for small matrices; use a certified polynomial-time SNF algorithm for larger complexes.

- 28 fixtures; 152 modulus checks; 271,796 assignments enumerated.
- Q3: all six faces and every five-face subset have five unit Smith factors. Every four-face subset has four unit factors and one free coordinate.
- Circle: one continuous holonomy. Torus CW presentation: two continuous holonomies.
- RP2 degree-two attaching map: full rank with a Z/2 alias. Degree-six attaching map: Z/6 alias.
- Mixed presentation [[2,4],[6,8]]: factors 2,4, giving eight points on the torus kernel, but only four on a six-point cyclic grid.
- Rank-deficient presentation [[2,4,0],[4,8,0]]: two continuous directions plus Z/2.

Replay:

    node research/pregeometric_identifiability/smith_observation_audit.mjs > /tmp/snf.json
    diff -u research/pregeometric_identifiability/smith_observation_audit.json /tmp/snf.json

## Formal boundary

SmithObservation.lean states a general fiber-equivalence theorem conditional on certified inverse basis maps and a commuting observation diagram. It provides mutually inverse maps on the fibers and explicit linear integer reduction identities for the mixed example, plus finite enumeration identities on seven moduli. The Smith existence theorem, spanning-tree gauge reduction for arbitrary CW complexes and general gcd formula are mathematical derivations above, not yet Lean-formalized. The Q3 finite integer result remains a separate verified fixture. No hardware experiment is needed to establish any of these algebraic identities.
