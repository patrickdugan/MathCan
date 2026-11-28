# VPVNP-02E local exact results

Registration and 02D repair: 86ced18e5437ca7a1c619b3732a413f4bd1bb3d9. Independent exhaustive span-extension enumerator confirmed every full ordered binary frame at n=1..4, including the empty prefix at n=1. Every prefix had a unique nonzero normal and the final vector had pairing one. All signed-fiber checks passed.

| ambient n | full frames | nonzero normals | frames per normal | signed fiber checks |
|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 1 |
| 2 | 6 | 3 | 2 | 6 |
| 3 | 168 | 7 | 24 | 21 |
| 4 | 20160 | 15 | 1344 | 60 |
| total | 20335 | | | 88 |

Signed count in each marked-rank stratum matches 02C, and only the matching normal contributes. Its signed count is minus 2^(n-1) times the smaller-dimensional signed count at dual rank k-1. This is exact finite evidence; the Lean implementation is pending kernel verification.

OrderedFrameFibers.lean proposes an explicit linear-equivalence-based frame fiber and a common-fiber equivalence. E4 remains open: transport the signed sum along the equivalence, use cancellation and restriction, and derive the all-dimension normalized recurrence.
