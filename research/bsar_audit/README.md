# BSA-R Step 7: formal-statement-to-PDE claim audit

Date: 2026-11-22. Independent audit note for MathCan. Source pin: [`VivienSweetbrier/bsa-r@80c6243`](https://github.com/VivienSweetbrier/bsa-r/tree/80c62433b0eb671175bd8d6169822d3ebd922b60), particularly [`Step7VorticityDirectionPdeRound6.lean`](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/lean/Step7VorticityDirectionPdeRound6.lean) and [`ROUND6_COLLABORATOR_SPEC.md`](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/navier_stokes/ROUND6_COLLABORATOR_SPEC.md). The [November 3 preprint TeX](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/navier_stokes/bsar_navier_stokes_arxiv.tex) openly lists unconditional direction-cone integrability as an unresolved analytic frontier.

## Five source-level findings

| Step 7 declaration | What the Lean statement establishes if kernel-checked | What the global PDE interpretation still needs |
|---|---|---|
| `step7_polar_palinstrophy_lagrange_splitting` | Identity among integer vector and Jacobian polynomials | Formalization for differentiable fields over the reals, handling the vorticity null set, and integration over the torus |
| `step7_zero_gap_bony_paraproduct_uv_gate` | Conditional sign inequality from assumed bounds on `T_LL`, `T_lin`, `T_HH`, `kap`, `D4`, `P4` | Establish those assumptions from Navier–Stokes solutions for all relevant times and frequencies |
| `step7_holder_half_cone_biot_savart_bound` | Determinant bound on integer vectors assuming a discrete chord/coherence inequality | A real-valued Biot–Savart singular integral and PDE-derived control of the time-dependent direction-cone constant |
| `step7_holder_half_quadratic_d3_to_d2_reduction` | Algebraic square-completion bound involving integer scalars `C_star`, `kh`, `D`, `g`, `nu`, `P_dir` | Legitimate analytic norm estimates linking the integers to physical enstrophy and palinstrophy |
| `step7_leray_quadratic_doubling_closure` | `dfinal ≤ Pow2 K * d0`, given `hchain : LerayDoublingChain M K d0 dfinal` | Construct `hchain` from PDE evolution and bound the number/size of windows uniformly near any candidate blow-up time |

The Lean file contains substantive constructive integer algebra, including vector Lagrange identities. The individual theorem names and surrounding explanatory comments refer to Navier–Stokes operators, but the **types of the declarations** establish the narrower facts above. A `#print axioms` line or successful kernel compilation certifies the formal statement it checks; it cannot upgrade the statement to an analytic PDE theorem. We have inspected these five statements directly and have **not** run Lean 4.35.0 or reexecuted the interval-arithmetic certificate suite in this environment.

## Reproduction

```sh
git clone https://github.com/VivienSweetbrier/bsa-r.git
cd bsa-r && git checkout 80c62433b0eb671175bd8d6169822d3ebd922b60
cd ../MathCan
python -m research.bsar_audit.source_gate --source ../bsa-r/lean/Step7VorticityDirectionPdeRound6.lean --output bsar_statement_audit.json
python -m unittest tests.test_bsar_source_gate -v
```

The parser emits five theorem signature records and `source_sha256` so later reviews can identify changed premises. It reads Lean text and makes a **static statement classification**. A complete audit also requires the upstream Lean compiler output, any imported axioms, independent mathematical verification of analytic reductions, and separate reproduction of numeric claims.

## Proposed MathCan follow-up (research gym)

Introduce explicit dependency gates from algebra to PDE: `real_vector_identity`, `spatial_omega_xi_decomposition`, `biot_savart_operator_bound`, `holder_cone_evolution`, `time_integrated_budget`, `uniform_window_count`, and `global_smoothness`. Train a proof-task selector on distinguishing a verified algebraic lemma from a missing bridge. A correct model should return `UNRESOLVED` on unconditional regularity unless it produces a valid analytic bridge and a kernel-checked theorem with the intended types.
