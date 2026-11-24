# VPVNP-02C local exact results and scope

Registration: b30ad95af9aed1df3537d31f1d4d10bdbed46658. 02B [native verification](https://github.com/patrickdugan/MathCan/actions/runs/45328238240) passed.

An independently executed exact integer span-state DP checked the closed form, the recurrence (for n>=2), and the rank-one numerator for every dual rank at sizes 1 through 6. The following are signed basis counts for k=0,...,n. This DP sums weights of represented bases by merging identical span states; it does not iterate over individual invertible matrices at n=6.

| n | signed counts |
|---|---|
| 1 | 1, -1 |
| 2 | 6, -2, 2 |
| 3 | 168, -24, 8, -8 |
| 4 | 20160, -1344, 192, -64, 64 |
| 5 | 9999360, -322560, 21504, -3072, 1024, -1024 |
| 6 | 20158709760, -319979520, 10321920, -688128, 98304, -32768, 32768 |

The largest calculation used 2824 cached nonterminal spans. A total of 27 dual-rank strata (including rank zero) and 21 nonbase recurrence comparisons were checked. The Python replay additionally cross-checks overlapping probabilities against 02A and emits an artifact; its CI result is a separate pending gate.

BinaryWalsh.lean supplies proposed finite-character orthogonality, inversion, actual scalar/vector shift energy, increment sums and recurrence uniqueness. The native 02C kernel check is pending. The distributional proof of the recurrence (uniform hyperplanes, independent restrictions, final-coset cancellation) remains the C4 Lean obligation. No all-n matrix bound is advertised as kernel verified yet.
