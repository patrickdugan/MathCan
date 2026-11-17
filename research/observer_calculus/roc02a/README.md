# ROC-02A retrospective frozen-NRF rank/causal-capture pilot

**Status:** independently reviewable public source and original measurements. 
**Preregistration:** [source-pinned protocol](roc02a_preregistration.json), committed to [LoopedTransformers](https://github.com/MoralityLabAI/LoopedTransformers/commit/650c61b35b46b9c74a75e988090bfead2de7c348) before the pilot was run.
**Scope:** 12 pre-existing short-trained synthetic checkpoints (six seeds, depths 16/32), two fixed shadow states per model, nine ranks, 128 rank-matched null subspaces per state/rank. This is retrospective ROC-02A, **not** prospective ROC-02 delayed-rule neural training.

- [Read the report](ROC02A_FROZEN_NRF_RANK_CAUSAL.md)
- [480 observation/state rows](roc02a_rank_observers.csv)
- [27,648 public null rows (compressed lossless CSV)](roc02a_rank_nulls_compact.csv.gz)
- [216 independently checkable random-null medians](roc02a_rank_null_medians.csv)
- [Rank/seed outcome table](roc02a_rank_by_seed.csv)
- [3D rank/task/leakage Pareto membership](roc02a_3d_pareto_by_seed.csv)
- [Summary JSON](roc02a_retrospective_summary.json)
- [Manifest](roc02a_manifest.json)
- [Standalone measurement code](roc02a_frozen_rank_causal.py) and [source-ready NRF09 generator](nrf09_local.py).

Public receipt arithmetic (only standard Python library):

```sh
python -m unittest discover -s tests -p 'test_roc02a_public_receipts.py' -v
```

Complete checkpoint rerun requires twelve original NRF-09 .pt files, twelve frozen NRF-11 .pt adapters and their twelve source receipts, preserving original bytes. The conversation's downloadable reproduction ZIP contains those artifacts, and the pilot runner **hard stops** on any SHA-256 mismatch. Use `PYTHONPATH=research/observer_calculus/roc02a` and pass the extracted binary archive root explicitly.

At R32 k8 the frozen task-only arm has held-out MSE 0.1571, B/random-null 0.716, output Gram capture 0.674; the frozen leakage-aware arm has 0.2470, 0.442 and 0.537. All six seeds exhibit lower incoming B and lower output capture for the leakage-aware subspace. The output Gram uses a separately fitted train-only final-state ridge head and represents *that specified output*, not model-native language reasoning.

Random-null effect sizes and empirical p-values follow MathCan [ROC-01 Amendment C](../ROC01_AMENDMENT_2026-11-16C.md) on [PR #99](https://github.com/patrickdugan/MathCan/pull/99). No new prospective ROC-02 neural task, causal-neural type identification or global invariant quotient is claimed.
