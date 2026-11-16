# ROC-01 Part 3: NRF v0.4 carry-over, per-seed accounting

**Retrospective, 16 November 2026.** Derived entirely from the already-public
NRF-11 fold-13 per-state source
[papers/NRF_v04_bidirectional_per_state.csv](../../papers/NRF_v04_bidirectional_per_state.csv).
All six model seeds are paired between the same task-only and selected
leakage-aware frozen observers. Selected gamma per seed is taken from
[papers/NRF_v04_selected_observer_risk.csv](../../papers/NRF_v04_selected_observer_risk.csv).
The deterministic source script is [nrf_retrofit.py](nrf_retrofit.py).

On **each** of twelve shadow states per seed, let B=W_delta*rho_delta.
The symmetric decomposition is

    delta B magnitude = 0.5*(W_joint-W_task)*(rho_joint+rho_task)
    delta B fraction = 0.5*(rho_joint-rho_task)*(W_joint+W_task).

These two terms sum identically to joint B minus task-only B **per state**.
No multiplication of means is used. Aggregate state contributions first
within seed, and only then across the six seeds.

## Per-seed paired results

| Depth | Seed | Chosen gamma | Delta incoming B | Magnitude contribution | Fraction contribution |
|---:|---:|---:|---:|---:|---:|
| 16 | 131 | 0.20 | -0.08918 | -0.07930 | -0.00988 |
| 16 | 137 | 0.05 | -0.02904 | -0.02529 | -0.00375 |
| 16 | 139 | 0.20 | -0.09232 | -0.06297 | -0.02936 |
| 16 | 149 | 0.05 | -0.04404 | -0.02983 | -0.01420 |
| 16 | 151 | 0.20 | -0.07222 | -0.05879 | -0.01343 |
| 16 | 157 | 0.05 | -0.03638 | -0.02768 | -0.00870 |
| **16 mean (k/6)** | | | **-0.06053 (6/6)** | **-0.04731 (6/6)** | **-0.01322 (6/6)** |
| 32 | 131 | 1.00 | -0.27999 | -0.31734 | **+0.03735** |
| 32 | 137 | 0.20 | -0.13659 | -0.08780 | -0.04879 |
| 32 | 139 | 0.20 | -0.16442 | -0.09583 | -0.06859 |
| 32 | 149 | 1.00 | -0.28805 | -0.26905 | -0.01899 |
| 32 | 151 | 0.20 | -0.13772 | -0.09831 | -0.03941 |
| 32 | 157 | 0.20 | -0.16472 | -0.10209 | -0.06263 |
| **32 mean (k/6)** | | | **-0.19525 (6/6)** | **-0.16174 (6/6)** | **-0.03351 (5/6)** |

The magnitude contribution at depth 32 is about **82.84%** of the average
incoming reduction under this algebraic split. The depth-16 corresponding
share is about **78.16%**. Reverse C coupling at depth 32 remains large
(0.77618 task-only versus 0.76489 joint). Seed 131 shows why the absolute
and proportional claims must be separate: B falls even as rho rises.

## NRF v0.4 Table 4 and lower-envelope switch points

The **historical** pooled J(lambda) lines use mean-over-six *per-seed
squared raw leakage*, the original task MSE convention and already
examined folds. The pairwise break-even points against task-only are:
gamma 0.05 at 0.136474, gamma 0.2 at 0.471086, gamma 1 at 0.742934,
task-free supervised start at 0.852508, random start at 0.954164.

The **actual lower envelope** switches at lambda 0.136474, 0.875804,
1.242665, 1.391717. The winning arms are respectively task-only,
gamma 0.05, gamma 0.2, gamma 1, task-free supervised start. The
random-start local optimum is never globally optimal among these fixed
candidates. Pairwise 0.471086 is **not** the optimal gamma=0.2 switch.

The source script [frontier.py](frontier.py) rebuilds this finite envelope
with exact rational intersections of public decimal measurements. None of
these lambda values is the new ROC **normalized B** exchange rate; no
checkpoint-backed normalized-B rank surface is available.

## Manuscript and provenance

The v0.4 manuscript
[papers/NRF_Observable_Fibers_Revised_v04.md](../../papers/NRF_Observable_Fibers_Revised_v04.md)
now includes Table 3C with selected gamma per depth-32 seed, the symmetric
split, Table 4/4B distinction and a depth/conclusion narrative emphasizing
write magnitude and substantial initialized coupling.

- [ROC01_NRF11_PER_STATE_PARTIAL.csv](ROC01_NRF11_PER_STATE_PARTIAL.csv):
  **1,584** per-state per-arm rows, A/B/C per sqrt(8), with unavailable
  H, task state-MSE, full D Frobenius and valid 128-rank null fields empty.
- [ROC01_NRF11_PER_SEED_DECOMP.csv](ROC01_NRF11_PER_SEED_DECOMP.csv):
  **12** six-seed/depth paired observation rows with chosen gamma and
  split contributions.
- [ROC01_NRF11_SUMMARY.json](ROC01_NRF11_SUMMARY.json):
  counts, six-seed means and the historical global envelope.
- [tests/test_roc01_retrofit.py](../../tests/test_roc01_retrofit.py)
  asserts both source blob hashes, per-state identity, the seed-level
  decomposition, and the public old envelope.

The original checkpoint and observer adapter binaries are external to the
public repository. A new neural sweep cannot be inferred from these
retrofits. All claims in this file are retrospective.
