# Task-Conditioned Observable Fibers: public technical-review manuscript

**Morality Lab · 16 November 2026 · Working draft v0.4, after three technical reviews**

- **[Current Carbon-readable manuscript, v0.4](NRF_Observable_Fibers_Revised_v04.md)** (authoritative review edition)
- [Full 1,584-row bidirectional Jacobian measurements](NRF_v04_bidirectional_per_state.csv)
- [132 per-seed/arm averages](NRF_v04_bidirectional_per_seed.csv)
- [24 NRF-10/11 seed-level risk and leakage rows](NRF_v04_selected_observer_risk.csv)
- [Exact objective lower-envelope and selected-arm thresholds](NRF_v04_envelope_summary.json)
- [Reproduction instructions and limitations](NRF_README_v04.md)
- [Public standard-library verification tests](reproduction_v04/test_nrf_v04_public_receipts.py)
- [Raw tensor Jacobian replay and SHA gates](reproduction_v04/nrf_bidirectional_v04.py)
- [Exact-fraction penalty-frontier recomputation](reproduction_v04/nrf_frontier_envelope_v04.py)

The v0.4 revision acknowledges that lowering **absolute** dark-to-observed Jacobian leakage can favor readout subspaces with smaller observed change gain. The task-only control accounts for most of the observed normalized dark-fraction movement, and the selected joint readout improves that fraction on five of six depth-32 seeds. Reverse-channel measurements show that observed-to-dark change remains large. Its retrospective six-arm penalty lower envelope switches at lambda 0.1365, 0.8758, 1.2427 and 1.3917; these differ from pairwise break-even weights against task-only.

**Earlier reviewed artifacts:** [v0.3 Markdown](NRF_Observable_Fibers_Revised_v03.md), [v0.3 PDF](NRF_Observable_Fibers_Revised_v03.pdf), [v0.3 HTML](NRF_Observable_Fibers_Revised_v03.html), and [v0.2 Markdown](NRF_Observable_Fibers_Revised_v02.md). The PDF and HTML links point to the previous reviewed edition; v0.4's source of record is its Markdown.

**Source projects:** [LoopedTransformers applied receipts](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/numerical_range_fixed_point_v1) and [MathCan analytical proofs](https://github.com/patrickdugan/MathCan/tree/main/research/compactification).

This is a technical-review working draft, not an independently validated real-language-model result. The synthetic models received 16/32 optimizer updates on one Gaussian signed-permutation task family. The post-review calculations are descriptive; the underlying trained weights and frozen adapters remain in a separately distributed reproduction archive, while this PR publishes the derived data and executable source needed to check the reported arithmetic.
