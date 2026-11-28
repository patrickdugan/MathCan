# VPVNP-01: verification contract and source map

Pin 11b6c7e3c927df2658f513b6b68ea7f8929c62c5. The inventory records every .lean blob in vp-vnp: 324 files, exact sizes and Git object hashes in [source_inventory.tsv](source_inventory.tsv). Group sizes: Nc 236 / 2,047,904 B; NS1 29 / 330,754 B; Paper 43 / 959,109 B; Ov 11 / 80,524 B; root 4 / 8,528 B; scripts 1 / 377 B. Total 3,427,196 B. These are metadata counts, not theorem counts.

Trusted statements: Statement.lean imports Mathlib alone and defines Computes, Approximates, Family, VP, VNP, VPBar, MainTheorem, MainTheoremApprox, Separation and SeparationClosure. Solution.lean imports Statement and Paper.Approximate, and proves five target theorems: mainTheorem, mainTheoremApprox, separation, separationClosure, permanent_over_real. Challenge.lean contains the placeholder versions for Comparator and must not enter the solution closure.

| Proof family | Entry points (relative to upstream vp-vnp) |
|---|---|
| Tensor spectral points and prices | Paper/Prices.lean; Nc/Price/Basic.lean; Ov |
| Midpoints and nonpositive curvature | Paper/Curvature.lean; Paper/Fan.lean; Paper/Toolkit.lean |
| Flat/contracting dichotomy | Paper/Alternative.lean; Nc/Flag/Exchange.lean; Nc/Flag/Cases.lean |
| Flat lower bound | Paper/Flat.lean; Paper/Rate.lean; Nc/CaseI/Lower.lean |
| Group hierarchies and network computations | Paper/Tower.lean; Nc/Tower/Tower.lean; Paper/Groups.lean |
| Scale lifting and accelerators | Paper/Scales.lean; NS1/Main.lean; Nc/Acc/Main.lean |
| Field transfer | Paper/Transfer.lean; Paper/Fields.lean |
| Border complexity | Paper/Approximate.lean; Paper/ApproxScales.lean |

Verified upstream job: [verify (vp-vnp)](https://github.com/anthropics/formal-math/actions/runs/45272623486), build and Comparator both success. Independent acceptance requires fresh pinned checkout, identical inventory, native build, all five axiom reports allowlisted, and Comparator's acceptance with nanoda. Tool pins: comparator 575674928e239f5bc452aab72d1dd7b0f1326494; nanoda 68d5ca9db226849b41a6fff59d796ff19d0a8840; landrun 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4; lean4export v4.33.0 fallback commit 15f6055e299ad5b89345e533cc2192f4cc00f659. The separate replay workflow records logs. Source audit emits local lexical module edges and the Solution transitive closure; it is a file-level import inventory, not the elaborated declaration dependency graph.

Review work remaining: independent semantic correspondence of Statement.lean with classical circuit definitions; paper Appendix Q; declaration-level dependency DAG, maximal trust cuts, and human mathematical review. Do not equate a successful kernel run with completion of these checks.
