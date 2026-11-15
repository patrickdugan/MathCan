# Task-Conditioned Observable Fibers: public manuscript

**Morality Lab · 15 November 2026 · Working draft v0.3**

- [Latest revised technical manuscript](NRF_Observable_Fibers_Revised_v03.md) (Markdown, easiest to paste into Carbon)
- [Web reading version](NRF_Observable_Fibers_Revised_v03.html)
- [Revised v0.2 manuscript, frozen for review history](NRF_Observable_Fibers_Revised_v02.md)
- [Full and skip-adjusted Jacobian diagnostics](NRF_skip_adjusted_metrics_v03.csv)
- [Penalty frontier and skip-adjusted diagnostics](NRF_skip_adjusted_frontier_v03.csv)
- [Original post-review gain measurements](NRF_postreview_metrics.csv)
- [Original post-review penalty-frontier measurements](NRF_postreview_gamma_frontier.csv)

The paper separates archived preregistered NRF-01–11 synthetic experiments from **retrospective** post-review controls. It foregrounds the equal-budget task-only comparator and the cost of leakage-aware regularization in task MSE. Version v0.3 corrects the identity-skip normalization, adds matched random-observer controls, and reports per-model squared-leakage break-even penalty weights. Sources and full proof scopes are in the manuscript.

**Source repos:** [LoopedTransformers applied data](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/numerical_range_fixed_point_v1) and [MathCan analytic results](https://github.com/patrickdugan/MathCan/tree/main/research/compactification).

This is a research working draft for technical review, not a published peer-reviewed article. Synthetic model weights received 16 or 32 optimizer updates. Its readout changes do not imply model capability or safety improvements.
