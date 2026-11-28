# RH-26B-09 registration: local budgets to admissible tables

**Date:** 2026-11-24 (Asia/Manila). Registered before new upstream source reads.
**Frozen upstream:** leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Observed consolidated main 362d9476fbd4548dead48ed7b6a54600879e1e17; no equivalence claim.
**Host:** MathCan research/rh26-extraction-rubrics-20261123, draft PR #265.

Question: inspect the actual implementation of NLink.admittedStatements_of_localBoundsConclusion and trace how the local multiplicity capacity predicate MultLe enters the admissible table and its weighted inequalities. Recover the exact role of multiplicities, local valuation/length errors, weights, denominators and zero-space ranks. Determine whether the E04C weighted allocation abstraction can apply to any actual source sum; do not assert equivalence merely from terminology.

Start at src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmittedStatementsOfLocalBoundsConclusion.lean:1–250. Follow explicit relevant imports and named helpers for AdmT and the weighted budget. Limit eight source files, 250 returned lines per file, 1200 aggregate, two dependency hops. Stop at exact next unread line when a supplier exceeds this limit. Record source pin, exact file/line anchors, theorem contracts, proof dependencies and unresolved steps. Source-only experiment, independent from the pending E04C repair audit.

Pass: exact admissible-table supplier, identification of how MultLe is passed or consumed, and a source-justified finite algebraic extension with stated hypotheses and counterexample. Partial if the actual weighted summation remains uninspected. Quantitative global theta multiplicity exponent remains unsourced. No claim that the source realizes generic capped allocation or a new RH proof. No full source scan/build, GPU/QPU or paid compute. Deliverables RH26B09_ADMISSIBLE_TABLE.md, inventory, ledger, draft PR checkpoint.
