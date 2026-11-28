# RHD-05: deeper Galois row premises

Original upstream: leanprover-community/riemann-hypothesis, commit `f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`.
Source checks in `galois_row_deep_audit.py` assert **11 immutable Git blobs** and direct supplier interfaces. This is a source proof *route* audit. It does not independently reconstruct, replay, or certify the mathematical proofs imported by the original declarations.

## Geometric row premise

The exact source-level construction is:

1. `geoOne_holds : GeoOne` calls `geometric_realization_of_weight_one weight_one_geometric_realization`.
2. `geometric_realization_of_weight_one` calls `geoOne_of_parts steps_holds (kodaira_spencer_of_weight_one hW) Pl.planEx_holds`.
3. `geoOne_of_parts` takes `Steps`, `KSAll` and `PlanEx`. The `Steps` structure has **17 fields**, including representation, crystalline, étale, jump, Frobenius, and theta transport conditions. `KSAll` contains **six** fields, ending in `KSHodge`.
4. `PlanEx` is a quantified existence theorem for geometric `Plan` packages across CM-field, prime, odd-weight, splitting, local saturation, and automorphic conditions. The source supplies it via `planEx_holds`, using `VecEx`, `ExpOf`, `SpecTop` through `exists_unitaryGroupDatum_of_vector_exponent_spectral` and a larger 15-field assembly.
5. The Hodge component requires `LocalSmoothExtension.HolomorphicLefschetzFormula` plus `FixK`. The former is supplied by `weight_one_geometric_realization` and reduces to `GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence`. Its upstream theorem statement concerns finite étale correspondences on smooth projective schemes, a fixed-point finite set, tangent matrices, and a Hodge-trace equality. The supplier is in the étale-clopen Lefschetz proof module.

Important issue for proof auditing: the `PlanEx` result and the Galois-row application are conditional on demanding local and global admissibility predicates. A source-level witness name can coexist with an empty domain of relevant applications. The review must exhibit at least one representative instance satisfying the antecedents used in the actual row, and then verify the theorem supplies the intended representation.

## Theta-lifting premise

`UpperTheory.TP.K.tLiftK` calls `UpperTheory.TP.tLift_holds_k`, which calls `tLift_of_tools_k`. The latter supplies `tLift_of_k` with a `Tools_k` record and the following major proof components: `HgtFst_k`, `RealPair_k`, `NonVan_k` (built via Rallis, decomposition, bump, datum, tail and Schur arguments), `LiftAut_k` and `ReadLift_k`.

The quantified claim fixes `E`, `B`, `n` and the Hermitian `X` first, then chooses an eventual bound `d₀` before later skew-Hermitian `W`, characters, weights and admissible automorphic `U`. The weight inequality `d + mW(w) ≤ 2 λ(w)_k` is part of the later antecedent. A useful nonvacuity test must construct compatible data at dimensions covered by the theorem and by the Galois-row use site.

The source declarations `TLift_k` and `TLiftK` were found textually identical after namespace normalization in RHD-04. That result checks proposition spelling. A compiled elaborated type-equivalence and proof-term/axiom audit are still valuable independent tests.

## Acceptance checks

- Recover compiled upstream declarations for `GeoOne`, `PlanEx`, `HolomorphicLefschetzFormula` and `TLiftK` from the pinned toolchain. Report `#print axioms` for the actual upstream constants, including `galoisLocalGlobalStrong_recParameter` and the final Main theorem.
- Extract proof-expression references at each named supplier and follow any axioms, `sorryAx`, custom trusted constants, typeclass assumptions or compressed proof-term boundaries.
- Prove or exhibit the relevant antecedents at the exact Galois-row call site. In particular, check `PlanEx` admissibility and eventual `TLiftK` witnesses jointly, not as unrelated existence exercises.
- Compare the mathematical meaning of the local Langlands input `recTExists` and its use in `everyCharacter_of_row` after the geometric and theta-lift gates pass.

Source baseline for the extra 11 files is recorded by the auditor under `SOURCES`, including the direct Lefschetz bridge, PlanEx supplier, 17-field Steps record, six-field KSAll record and theta construction. The receipts deliberately mark `proof_term_data=false`.


## External whole-proof verification as of 2026-11-21 12:55 UTC

Andrew Sutherland's independent checking log at https://math.mit.edu/~drew/grh/
reports that all 175,187 upstream modules compiled and passed Lean `leanchecker`
replay; the Rust nanoda kernel and con-leche accepted the full export; lean4lean
accepted the compiled modules; and con-leche's independent statement comparator
found all five headline Main theorems justified against the Mathlib-only
challenge. The five headline declarations list only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The report still listed the
full `lake comparator` and default/paranoid Lean export-kernel replay as
running at that timestamp.

This is independent *whole-proof* checking and substantially strengthens the
formal correctness evidence. The local RHD-05 CI is deliberately a much narrower
source-pinning and proof-interface gate. Its purpose is now to identify the
actual geometric, automorphic and local-global mathematical claims and exhibit
their intended nonvacuous instantiations. Statement meaning and the exact
row-call hypotheses take priority over redundant abstract Lean wrappers.

The external comparison reports that the claimed RH and four Dirichlet
L-function statements are exactly the Mathlib-only challenge statements.
This is evidence about encoded theorem semantics at the headline level.
It leaves room for a detailed mathematical audit of the underlying Galois
row's role, especially how `PlanEx` and `TLiftK` discharge their hypotheses
in the eventual construction. Maintain separate evidence levels for
source matches, compiled proof-term checks, and mathematical interpretation.
