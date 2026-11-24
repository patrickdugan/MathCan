# RH-26B-14 registration: completion of point bound and aux3 export

**Date:** 2026-11-24 (Asia/Manila). Frozen before new source reads.
**Pinned upstream:** leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Observed consolidated main a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1; no equivalence claim.
**Host:** MathCan research/rh26-extraction-rubrics-20261123, draft PR #265.

Question: complete the source point_bound proof, locate the exact use of its coefficient in aux3 / family export, finish loc_le_lamB and trace lamG and prime-wise etaAt bounds. Establish what the cohomological infinite sum does and what hypotheses remain. Test whether the conditional 105 replacement from B13 can be carried to the downstream source contract, preserving all premises. Identify one new independent mathematical consequence and a control.

Registered starts: src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean:1001–1250 and src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean:501–750. Follow actual named dependencies only if needed, max eight distinct files, 250 returned lines per file, 1200 aggregate, two dependency hops. Reuse earlier source anchors without rereads. Stop at a precise continuation if the proof exceeds the window.

Pass: exact completion of point_bound and its next numerical consumer, or explicit unresolved supplier/continuation. Preserve all eligibility, summability and nonnegativity premises. No claim of improved RH exponent or actual arithmetic realization. Independent refinements remain paper results pending separate registered kernel checks. No full source scan/build, copied proof imports, GPU/QPU or paid compute.

Deliverables: RH26B14_AUX3_EXPORT.md, rolling inventory, ledger and draft PR #265 checkpoint. E05A/B/C/D/E remain separate proposed experiments.
