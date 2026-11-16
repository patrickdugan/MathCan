# ROC-01 dated amendment C: null-calibrated tags, physical T-C arms, odd ranks

**Dated 2026-11-16, before ROC-02 task generation, fitting, checkpoint replay or unsealing.** Supersedes the prospective diagnostic thresholds, intervention identities, objective scaling and rank grid in the original ROC-01 registration and Part 4. Both original frozen files and amendment B remain unchanged. This is a protocol amendment; all ROC-01/NRF retrospective statistics and frozen sources retain their original definitions. No ROC-02 data were generated to choose these corrections.

## C1. Conditional-on-rank null calibration

For every frozen checkpoint/state/output horizon, model rank k and candidate U, draw the registered 128 unconstrained SHA256-keyed Haar/QR rank-k null subspaces, with at least 100 distinct *subspaces* and their per-state rows public. These are different from the readout-containing conditional completions used only in T-B. Let (a,b,c,s) be the originally reported ||A||F, ||B||F, ||C||F divided by ||T-I||F and the output-Gram energy fraction. Preserve all four raw numbers as descriptive quantities. Let m_a,m_b,m_c,m_s be the corresponding null medians at this same checkpoint, state, horizon and rank.

Prospective effect sizes are r_a=a/m_a, r_b=b/m_b, r_c=c/m_c and, when 0<m_s<1, r_s_low=s/m_s and r_s_high=(s-m_s)/(1-m_s). A ratio with zero or undefined denominator is **undefined**, not an invented zero. A zero-dynamics state, tr(H)=0, insufficient/distinctness-failing null, or constant-null metric abstains from hypothesis tagging for that metric. Keep analytic exact-zero facts separate from inference.

For each observer/state, predeclare the six one-sided directions **a↓, b↓, c↓, b↑, s↑, s↓**. Compute add-one empirical p=(1+#{null as or more extreme})/129, counting ties as extreme, and use Holm adjustment over the complete six-test family. A diagnostic predicate must meet both the effect-size threshold and Holm-adjusted p≤0.05:
- near-zero A, B or C: r≤0.20 and corresponding lower-tail test;
- large B: r_b≥1.20 and the upper-tail B test;
- high s: r_s_high≥0.80 and the upper-tail s test;
- low s: r_s_low≤0.20 and the lower-tail s test.

The five **nonexclusive** tags then use the same logical combinations as the original card: closed quotient (B small), invariant subspace (C small), latched memory (A/B small and s high), output register (B large, A/C small), irrelevant (A/B small and s low). The old "invariant/driver" label is deprecated. A raw card without the registered null returns `unclassified` and `null_calibration_required`; historical absolute-cutoff tags may be printed as `legacy_absolute_threshold_tags` solely for replay and must not pass the ROC-02 classification gate. Ties or unavailable nulls never count as a significant discovery.

For observer fitting, use the frozen training/calibration state population S (never sealed test labels):
`J(U)=mean_{i∈S} task_MSE_i(U) + λ mean_{i∈S} [b_i(U)/m_{b,i}(k)]²`.
The *same* rank/state/clock-specific 128 null medians define each denominator for every candidate U. If any denominator is zero or unavailable, label this objective undefined for that candidate and report it without claiming a penalized optimum. The fixed reference remains λ=1 and the exploratory grid remains {0,0.05,0.2,1,2}. Report the raw B fractions and both old and amended objective values in distinct, labeled columns; older NRF selected γ and envelope claims stay in old units. The rank-relative squared reference is 1 for a basis at the rank-matched null median, removing the automatic k/d slope of the old raw B².

## C2. Physical T-C interventions

The original signature column `freeze_U` was incorrectly modeled as though it selected A alone. A frozen U register cancels *both* A=UᵀDU and B=UᵀDQ at that step; for the stipulated synthetic exemplars its corrected column is (1,1,0,1,0), in the row order closed quotient / invariant subspace / latched memory / output register / irrelevant. With that correction the invariant and register rows coincide across all four original arms. It is an **unidentifiable** four-arm design, and the earlier physical interpretation of the synthetic cover is withdrawn.

Replace the third registered active arm with `observed_to_observed`: a finite-radius perturbation entirely inside span(U), introduced at a declared pass after source-state capture, with matched physical L2 random control, matched readout and declared output horizon. This directly probes within-observed effects A; the separate `observed_to_dark` and `dark_to_observed` arms retain their directions. `ablate_readout` remains the mandatory fourth control. A whole-register `freeze_U` may be reported separately as an exploratory composite intervention and cannot count toward the four-arm separation or completeness gate.

For the **hypothetical** corrected four-arm binary signature table, relabeling the former third column as observed-to-observed preserves the exact minimum cover size three, with **three** distinct size-three covers. The idealized unit-variance Gaussian max-min allocation remains (1,1,2,1)/5 in order dark→observed, observed→dark, observed→observed, ablate-readout, worst-pair KL 1/5. Retain source type "synthetic" until measured outcome distributions establish which actual mechanisms can be distinguished. No empirical allocation is inferred from this table.

## C3. Odd-rank and operator-norm corrections

Supersede the old even-only rank grid by **k={1,2,3,4,7,8,12,16,32}**, subject to k≤d and k≥rank(G) in readout-constrained sweeps. It contains SPC's k=7 claim and can test real parity obstructions. Use the same model seeds, null seeds, task splits, training budgets and rank-selection discipline. New ranks are registered here ahead of ROC-02 data.

The finite-horizon T-B proof may use M=||T||op instead of ||T||F in the same recurrence; the operator-norm version is a stronger lower bound and is the primary floating-point closure-sweep output. Retain the older exact-rational Frobenius certificate for regression, labeled as such.

An **interior** counterexample is T=1⊕R90⊕R90 on R⁵ and G=e₁ᵀ. Real invariant subspaces of the four-dimensional quarter-turn block have even dimension. Therefore L*(2)>0, L*(3)=0, L*(4)>0 while all are strictly below d. A unit-vector/dimension argument further gives L*(2)=L*(4)=1 for this orthogonal witness.

## Evidence gates

Amend the EvalMath ROC evaluator's canonical arm names, source pin and card audit on its existing PR #36. Both repositories must carry matching amendment/version claims before ROC-02 samples are drawn. Require public NRF-09 checkpoint matrices and observer adapters before claiming neural 128-basis replay, causal H, or any L*(k) neural sweep. The twelve depth-16/32 NRF-09 128×128 matrix pairs are small enough to publish if licensing/provenance allows, but **have not been supplied or published by this amendment**.
