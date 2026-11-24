# VPVNP: spectral geometry and recurrent computation

Opened 2026-11-24. Research source: [Anthropic formal-math, vp-vnp](https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp).
Pin: 11b6c7e3c927df2658f513b6b68ea7f8929c62c5; Lean v4.33.1. Upstream [CI](https://github.com/anthropics/formal-math/actions/runs/45272623486) reports success for lake build and the Palomar Comparator gate (nanoda enabled). The upstream README says that the AI-written proof and paper have not been checked by a human mathematician. MathCan's independent replay remains pending until our own receipt exists.

## Workstreams

| ID | Goal | Initial state |
|---|---|---|
| VPVNP-01 | Pinned source inventory, lexical imports, five theorem interfaces, independent native and nanoda replay | registered; source metadata collected |
| VPVNP-02 | Rank-conditioned spectral geometry, exact finite-field tests, reusable Lean proof targets | registered |
| VPVNP-03 | Recurrent computation: compare rank-conditioned geometry of state and task observables | conditional on VPVNP-02 |
| VPVNP-04 | Circuit/precision bounds with weight reuse and an explicit resource model | research question |
| VPVNP-05 | Lean reasoning gym with dependency-held-out targets and native verification | design registered |

Read [SOURCE_MAP.md](SOURCE_MAP.md), [EXPERIMENT_02.md](EXPERIMENT_02.md), [EUCLIDEAN_RANK.md](EUCLIDEAN_RANK.md), [GYM_SPEC.md](GYM_SPEC.md). The upstream proof is isolated from MathCan's Lean 4.35.0 project; no dependency upgrade or import into the production library is required. This directory contains original research notes and upstream metadata, not a vendored copy of the proof. Upstream license: Apache-2.0.

Local exact pilot: `python3 research/VPVNP/rank_geometry.py --out rank_geometry.json`.
Pinned source audit: `python3 research/VPVNP/audit_source.py /path/to/formal-math --out source_audit.json`.
Results of the algebraic theorem do not establish Boolean P vs NP or neural-network lower bounds. The proposed neural tests have a separate mathematical scope and a saturation control.
