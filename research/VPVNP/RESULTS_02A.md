# VPVNP-02A: exact rank observer pilot

Status: PASS (local Python execution, 2026-11-24). Registration commit: 04e1d892ad6cf8398c8f08379049436686523a30.

All 66,064 matrices at n=2,3,4 were enumerated, and all rank counts matched their exact product formulas. Every dual-rank representative agreed with the predicted rank-one and full-rank probabilities. The maximum squared ratio was attained at dual rank 1 alone at each size.

| n | matrices | maximum D(n)^2/D(1)^2 | rank distance control | sqrt(rank) control |
|---|---:|---:|---:|---:|
| 2 | 16 | 3/2 | 4 | 2 |
| 3 | 512 | 7/4 | 9 | 3 |
| 4 | 65,536 | 15/8 | 16 | 4 |

The fixed nonlinear three-coordinate map at n=2 has D(1)^2=311/9 and D(2)^2=287/6, with exact agreement between direct evaluation and the Walsh identity. All H1-H4 passed. A constant observation has undefined normalized ratio. The registered negative controls retain their predicted ratios; the rank triangle inequality was also exhaustively checked at n=2.

The all-n bound remains a mathematical proof draft until reviewed and kernel checked. The finite experiment validates its identities at the registered sizes, and gives no evidence of a learned mechanism. Run: python3 research/VPVNP/rank_geometry.py --out /tmp/rank_geometry.json ; diff -u research/VPVNP/results/rank_geometry.json /tmp/rank_geometry.json.

VPVNP-01 independent native/Comparator replay is a separate pending gate; the upstream success is not a MathCan receipt.
