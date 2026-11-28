# RH-26B-08: good-point multiplicity rank certificate

**Date:** 2026-11-24. Source-only registration before upstream source reads.
**Immutable upstream:** leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Consolidated main observed f38c099ec6017a3ce839cba4e06857eda6c9a057. No equivalence claim.
**MathCan:** research/rh26-extraction-rubrics-20261123, draft PR #265.

Question: identify the exact theorem goodPointMultiplicityLeRank_proof, its mathematical hypotheses and conclusion, the transfer/cut conversion, and the consumer linkN_along_family_of_localBounds. Test whether the previous NLink.MultLe joint budget follows from the local good-point rank certificate or belongs to a separate hypothesis family. Null: a pointwise or local rank statement is insufficient to certify a total multiplicity budget across distinct indices.

Start at src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProofStatement.lean and LinkNAlongFamilyOfLocalBoundsStatement.lean, directly imported by LinkNFam.lean. Follow immediate declaration/definition imports and actual named theorem calls. At most 8 distinct files, 250 returned lines/file, 1200 aggregate lines, 2 further dependency hops. Record exact paths, windows, theorem types, hypotheses, conclusion and any unresolved bridge. Do not assume names imply equivalence. No full clone or source scan.

Pass: exact local multiplicity rank theorem and a source-anchored use or conversion. If the conversion to MultLe remains unlocated, keep PARTIAL. Extract one independent mathematical lemma tied to the actual certificate, with a worked example and a falsifier of any missing assumption. Distinguish this from a quantitative theta-lift growth exponent, which remains UNSOURCED until separately traced.

Deliverables: RH26B08_RANK_CERTIFICATE.md, CHUNK_INVENTORY.md and LEDGER.md updates, draft PR checkpoint. Candidate E04 experiment can be registered after selecting the faithful smaller theorem. No new Lean kernel claim, copied upstream proof source, full upstream build, GPU/QPU or paid compute.
