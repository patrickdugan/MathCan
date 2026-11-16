# NRF observable-fibers paper, technical review v0.4

**Read-only working draft, 16 November 2026.** The model/training runs were completed in November 2026. The v0.4 diagnostics were added after the third review and use the same model seeds and previously exposed input folds.

## Manuscript and public data

- `NRF_Observable_Fibers_Revised_v04.md`: primary Carbon-readable manuscript.
- `NRF_v04_selected_observer_risk.csv`: 24 public seed/depth/study rows with task-only and selected-observer errors and leakage. Enables independent computation of the NRF-10/11 pooled break-even penalties (0.624215, 0.566663).
- `NRF_v04_envelope_summary.json`: evaluated mean task errors, mean per-seed squared leakage, pairwise cuts and full lower-envelope switches (0.136474, 0.875804, 1.242665, 1.391717).
- `NRF_v04_bidirectional_per_seed.csv`: six-seed/double-depth directional coupling, 11 observer arms per model.
- `NRF_v04_bidirectional_per_state.csv`: every one of the 1,584 observer-arm × shadow-state measurements, with incoming/outgoing/within change gains and ratio definitions. The two per-state Pythagorean identities can be checked directly from the CSV; this check requires no checkpoint binaries.
- `NRF_skip_adjusted_metrics_v03.csv` and `NRF_skip_adjusted_frontier_v03.csv`: earlier per-seed and gamma frontier measurements, used with the v0.4 reanalysis.

## Scripts

`reproduction_v04/nrf_bidirectional_v04.py` reconstructs the dense suffix Jacobians on the original frozen checkpoint bytes and computes both off-diagonal blocks of `D = T-I`. It SHA-256 checks every original network and adapter against each NRF-11 receipt, checks original leakage parity, and asserts the two norm identities at each shadow state.

`reproduction_v04/nrf_frontier_envelope_v04.py` is standard-library-only and needs just the public `NRF_skip_adjusted_frontier_v03.csv` and `NRF_v04_selected_observer_risk.csv`. Run from the repository root:

```bash
python papers/reproduction_v04/nrf_frontier_envelope_v04.py
```

`reproduction_v04/test_nrf_v04_public_receipts.py` is standard-library-only and checks all 1,584 published per-state measurements, both energy identities, mean aggregation, registered-arm hash-compatible numeric summaries, the four lower-envelope switches and selected-observer thresholds:

```bash
python papers/reproduction_v04/test_nrf_v04_public_receipts.py
```

`reproduction_v04/nrf12_diag.py` and `reproduction_v04/nrf_frontier.py` preserve the earlier retrospective controls; the helper source snapshots are in `reproduction_v04/nrf09_local/` and `reproduction_v04/nrf10_work/`.

### Full PyTorch replay

The **public MathCan draft does not contain the 12 `.pt` model weights or 12 `.pt` frozen observers**, whose bytes were distributed in the earlier `NRF_Revised_v02_Site_Draft_and_Reproduction.zip` conversation artifact. To rerun the dense Jacobians, obtain that artifact and extract it so it contains a `reproduction/` directory with `nrf09_local/checkpoints` and `nrf11_work/receipts/observers`.

Using the scripts from this repository:

```bash
python papers/reproduction_v04/nrf_bidirectional_v04.py \
  --root /path/to/extracted/reproduction \
  --output /tmp/nrf_v04_check
```

PyTorch CPU 2.10 was used. No new training, no optimizer updates, and no new held-out task distribution are involved in this audit. The base scripts and full native experiment implementation are in [LoopedTransformers](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/numerical_range_fixed_point_v1).

## What this can support

The public CSVs support full reconstruction of the **reported numerical aggregation and local quadratic identities**, not a fully independent rerun of the neural training. The full archive with model/adapter bytes is needed to verify the saved-state computations against weights. The paper's mathematical proofs are written and the Lean fragments are narrower than the full norm theorems. The results remain exploratory, with 16/32 training updates and one synthetic task family.
