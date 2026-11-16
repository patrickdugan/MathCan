# NRF v0.6: fifth technical review corrections

Morality Lab, 16 November 2026. This is a public **review draft**, not the publication-ready journal paper.

- [Full v0.6 Markdown manuscript](NRF_Observable_Fibers_Revised_v06.md)
- [14-page v0.6 PDF](NRF_Observable_Fibers_Revised_v06.pdf)
- [v0.5 random-relative per-seed table](NRF_v05_random_relative_by_seed.csv)
- [v0.5 random-relative audit summary](NRF_v05_random_relative_summary.json)
- [NRF-10/11 risk receipts](NRF_v04_selected_observer_risk.csv)
- [v0.4 complete 1,584-row shadow-state audit](NRF_v04_bidirectional_per_state.csv)

## Review delta

1. **Penalty costs by evaluation fold.** Seeds 131 and 149 (selected gamma=1) cost 2.133x and 1.900x task-only MSE on NRF-10; on fresh NRF-11 folds their ratios are 1.851x and 1.791x. The moderate-gamma seed 137 is also costly on NRF-11 (1.711x), making a blanket superlative inappropriate.
2. **Depth-specific initial readout mechanism.** At depth 32 the supervised observer receives more dark-to-visible computed change and less within-subspace change than random controls. At depth 16 its incoming signal is only 1.02x random. The conclusion states this scope.
3. **Appendix typesetting.** Long filenames now use short descriptive Markdown link labels in the PDF; the 14-page page-layout preflight reports all text within the margins.

The full experiments were performed earlier and remain exploratory with respect to the previously chosen lambda. No new neural experiments were run for this version.

## ROC-01 note

ROC-01 [PR #99](https://github.com/patrickdugan/MathCan/pull/99) has already registered the three corrections in dated Amendment C: rank-conditioned 128-null thresholds with Holm p-values, a physical within-observed perturbation in place of the invalid freeze arm, and odd-rank evaluation. The paper review does not modify that frozen registration.
