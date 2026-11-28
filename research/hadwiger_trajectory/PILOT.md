# HAD-GYM-01A: exact-witness scheduler synthetic pilot

Status: CHECKED finite synthetic results. Run from this directory:
```sh
python bench.py
python direct_fit.py
```
Local environment: NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0. LP is numerical; proposed nonnegative weights are rounded to denominator 10^9, equalized at the anchor, and repaired using an exact inverse of a full-rank chord basis. The exact witness certifies an upper bound, not LP optimality. Inputs are integer coordinates; activation quantization and its error budget are a future obligation.

## Results
Seeds 11, 23, 37; 64 edges per path; dimensions 3, 8, 16. Synthetic anisotropic cross-polytope with axis scales 120(i+1). Random axis steps drawn from ±{12,24,36,48,60}. Budget 1/2. Each method uses the same per-path chart count; Euclidean minimax is exact DP on these one-axis edges, for which Euclidean and L1 lengths coincide. Gauge minimax is exact DP on certified edge costs; greedy is optimal in chart count for those costs (inductively, its kth endpoint is at least as far as the kth endpoint of any competing feasible segmentation). No claim of optimal chart count for actual geometric fit.

| rank | gauge | Euclidean | fixed |
|---|---:|---:|---:|
| 3 | 37/37 | 27/37 | 26/37 |
| 8 | 27/27 | 20/27 | 19/27 |
| 16 | 16/16 | 10/16 | 13/16 |
| total | 80/80 | 57/80 | 58/80 |

Gauge minimax also passed 80/80. Maximum certified edge-mass sum: gauge 0.5, gauge minimax 0.5, Euclidean 0.6654761914285714, fixed 0.833333334. Every accepted chart was checked by exact rational coefficients and its affine lower bound checked at every state. All 576 edge masses were between the analytic optimum and optimum+10^-6. All 343 dense asymmetric clipped-cube chords passed; four negative controls (oversize, degenerate hull, fractional input, corrupt chord) rejected. Bench wall time 2.168 s locally, excluding interpreter import. This is one small synthetic pilot.

## Direct-fit control
A second LP minimizes the cross-polytope radius with unrestricted common center. Its rounded center supplies an exact upper certificate and half the diameter supplies an exact lower certificate. Therefore cases are classified as feasible, impossible, or unresolved; float solver success is not itself evidence.

| method | direct feasible | impossible | unresolved | path-budget failures recovered |
|---|---:|---:|---:|---:|
| gauge | 80 | 0 | 0 | 0 |
| Euclidean | 77 | 3 | 0 | 20 |
| fixed | 75 | 5 | 0 | 17 |

The apparent 23-chart improvement against Euclidean shrinks to 3 charts under actual fit. Path certificates are conservative, especially for backtracking. Direct fit is a required control, not a new training result.

## Next gate: two-stage scheduler
Cheap exact additive witness first; if the budget fails, attempt a direct common-translation feasibility LP before splitting. For a fixed lambda and points x_j, seek v and nonnegative coefficients w_j with Vw_j=x_j-v, sum w_j=lambda. Feasibility is hereditary on subintervals. Longest feasible prefix greedy minimizes number of contiguous charts under exact feasibility (same endpoint dominance argument), but numerical unknowns must be reported and cannot be treated as mathematical infeasibility. General direct-fit certificates need exact primal/dual validation. Compare against axis-normalized Euclidean, gauge-only, and direct-only, logging solver time and cache hit rate, using matched count and matched wall-time separately. No RAM tiers measured here: the optional cache is an entry-count LRU, with 128 entries in this pilot. No real model activation, BPD steering or MMS learning-benefit evidence.

Local source hashes: scheduler.py b007e19f77da369b2f660883bc52a70d516799849f2c61e7b76b7e5cf5eeb6a4; bench.py 44bb892dd022a4c7d14e1d67184e1285235de6151014c18164a9135c0f8a0915. The local source was mirrored into GitHub contents commits; hosted CI and Lean replay remain unverified.
