# RH-26E-05C1 registration: numerical export assembly certificates

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, research/rh26-extraction-rubrics-20261123.
**Source inspiration:** frozen leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b, ExportBoundOfAdmissible.lean:936–1096 and 1184–1203, inspected in B13/B14. No new upstream reads/imports. E04A/B/C passed 10/11/11 declarations.

## Question

Certify the exact scalar assembly with the original five sum suppliers and global correction, preserving the scale absorption ratio. Separately certify the proposed assembly with stronger scalar supplier bounds from B10–B13, as explicit hypotheses rather than verified upstream facts. Propagate a verified coefficient through the nonnegative rank multiplication and padding step. Establish least integer envelope coefficients on the relaxed scalar domain; these are not lower bounds on actual arithmetic data.

Use real C,H,b,X; W=(C+1)^2*H^18; rho_o=1164022/4000000 and rho_r=11042/4000000. The scalar supplier tuple has generator, small/3, ramified, generic-small, exceptional and global-correction terms. A supplied Y is bounded by their sum. The source scale condition is 4000000 W<=b<=X; X>=0. The actual arithmetic interpretation is X=f*m*b*g², H=Ub, g=x^eps.

## Fifteen frozen public theorem declarations (RH26E05C1 namespace)

1. scale_nonneg: W>=0 for real C,H.
2. original_absorption: 4000000 W<=b<=X implies 1164022 W<=rho_o X.
3. refined_absorption: same premises imply 11042 W<=rho_r X.
4. original_gap_identity: 2(C+1)^3-12C=2C³+6(C-1/2)²+1/2.
5. original_envelope: for C>=0, 1000(C+1)^3+12C+rho_o<=1002(C+1)^3.
6. original_integer_minimum: for natural K, (for all real C>=0, original scalar envelope<=K(C+1)^3) iff 1002<=K. Use C=1/2 for the lower control.
7. refined_gap_identity: 4(C+1)^3-27C=(2C-1)^2(C+4).
8. refined_envelope: for C>=0, 104(C+1)^3+(73/36)C+rho_r<=105(C+1)^3.
9. refined_integer_minimum: for natural K, (for all real C>=0, refined scalar envelope<=K(C+1)^3) iff 105<=K. A positive C witness suffices.
10. original_assembly: C>=0, X>=0, scale absorption, Y<=sum of six actual terms with respective upper bounds 2W,8CX,4CX,1000(C+1)^3X,1164000W,20W imply Y<=1002(C+1)^3X.
11. refined_assembly: same structural premises with respective upper bounds 2W,2CX,(C/36)X,104(C+1)^3X,11020W,20W imply Y<=105(C+1)^3X. The stronger component suppliers are external premises of this theorem.
12. export_propagation: eta<=R(Y+V), Y<=KX, R>=0,K>=0,N>=0 imply eta<=R[K(X+N)+V]. V remains arbitrary real with coefficient one inside the bracket.
13. missing_scale_control: explicit positive C,H,X,b and original supplier tuple with Y bounded by its sum, all original supplier bounds, b<=X, but 4000000W>b and Y>1002(C+1)^3X.
14. negative_rank_control: concrete real parameters obey the two scalar upper premises of export_propagation and K,N>=0, but R<0 and its conclusion fails.
15. negative_padding_control: concrete real parameters obey the scalar upper premises, R,K>=0, but N<0 and its conclusion fails.

## Acceptance

All fifteen exact theorem names compile on pinned Lean 4.35.0 and Mathlib v4.35.0 and pass the full allowlist audit (propext, Classical.choice, Quot.sound only). No custom axioms, sorry/admit/native_decide. Record compiler/dependency/source hashes, elapsed time and RSS, literal audit artifact, failed receipts and proof-only repairs. No theorem weakening after first executable run. Isolated MathCan source research/rh26/lean/RH26E05C1Assembly.lean, existing experiments/deligne_mathlib environment; one GitHub-hosted CPU job per proof/workflow change, 25-minute timeout. No full upstream or Deligne build, GPU/QPU or paid compute. Verification certifies the scalar consequences under explicit supplier hypotheses. An upstream integration and the stronger component suppliers for 105 remain separate.

Deliverables: report, ledger, chunk inventory and PR #265 checkpoint. Next E05F finite-support and padding slack, E05B weighted rank/degree coverage, remaining E05C components, or separately registered B15 source inventory.
