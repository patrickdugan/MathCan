# RH-26B-07 registration: local multiplicity and rank-capacity chunk

**Date:** 2026-11-24. Registration precedes new upstream source reads.  
**Frozen source:** leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Consolidated upstream main observed f38c099ec6017a3ce839cba4e06857eda6c9a057, a distinct version.  
**Host:** MathCan draft PR #265.

Question: what is the mathematical role of MultLe, the sum-of-multiplicities inequality at BoundAtTwoThreeFamily.lean:117–119, and can the exact source identify its supplier or consumer? Null: this condition concerns a local zero-space capacity independently of the global theta comparison; a theta-lift multiplicity growth theorem does not follow from the name.

Start with src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean and the previously traced ThetaPairLifts/ThirdPlaceSeries local bound chain. Search narrowly scoped directory filename metadata for MultLe, zero-space rank, family conclusion and explicit local multiplicity proof filenames. Follow direct names and imports, at most eight upstream Lean files, 250 returned lines per file, 1200 aggregate, two dependency hops from the selected interface. Record exact source windows, assumptions, inequality and proof status. If the theorem supplier is not located, retain PARTIAL and exact next targets.

Pass for this chunk inventory: exact capacity predicate and at least one direct role in a bundled conclusion or an explicit supplier. Stronger target: a proof connecting it to local rank or theta machinery. A separate independent paper lemma should retain the required nonnegativity and capacity hypotheses, with a counterexample if a summand bound is mistaken for a total budget. Candidate experiments may explore direct-sum rank, weighted allocations, majorization, dual certificates or local-to-global aggregation only when the relationship is explicit.

Deliverables: RH26B07_LOCAL_CAPACITY.md, CHUNK_INVENTORY.md update, LEDGER.md and draft PR checkpoint. No full upstream build, copied proof source, independent Lean claim, GPU/QPU or paid compute in this source session. New experiments must be preregistered and tested separately.
