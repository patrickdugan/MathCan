# VPVNP-02H canonical recurrence exact audit

Registration: 651c9f5140cf620d204f479590a51b42229885c1.

Independent integer enumeration through ambient dimension four including dimension zero checked every full frame, every possible diagonal marking mask, and the tail-diagonal prefix/last decomposition. All comparisons passed.

| n | frames | masks | canonical signed sums | factorization checks |
|---:|---:|---:|---|---:|
| 0 | 1 | 1 | 1 | 1 |
| 1 | 1 | 2 | 1,-1 | 2 |
| 2 | 6 | 4 | 6,-2,2 | 18 |
| 3 | 168 | 8 | 168,-24,8,-8 | 672 |
| 4 | 20160 | 16 | 20160,-1344,192,-64,64 | 100800 |
| total | 20336 | 31 | | 101493 |

The new Lean module CanonicalRankRecurrence.lean proposes actual matrix-unit/frame equivalences, signed prefix reduction with a tail-diagonal representative, the product solution, and a theorem for arbitrary matrices using the 02G rank invariance. Native verification is pending. The exact audit and proposed general Lean declarations are separate evidence. 02I still needs the rank-one sampling formula and the normalized Walsh composition for the sharp observer bound.
