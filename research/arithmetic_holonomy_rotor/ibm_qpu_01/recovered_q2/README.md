# AHR-QPU-01R: recovery of the original IBM Q2 execution implementation

**Status:** Draft integration of historical implementation from [MathCan PR #254](https://github.com/patrickdugan/MathCan/pull/254), pinned at commit `981b07b6d555b268ce0f28add39176bf3f39beb4`. Run offline tests before review. This directory is separate from the live simulator introduced by merged PR #255.

The November 23 IBM Fez Q2 experiment succeeded on physical qubits 9 and 10, with 73,728 shots, signed forward and reverse phase estimates +38.90° / −42.86°, and 21 free QPU seconds charged. The **immutable evidence was already merged** in [PR #262](https://github.com/patrickdugan/MathCan/pull/262) at `../receipts/hardware_q2/`, along with an independent standard-library replay.

This recovery preserves the original Q2 compiler, full statistical analysis, hardware submission preflight and interrupted-job collection logic. Source imports resolve within this directory; the newer simulator's modules and tests remain untouched.

## Source provenance and modifications

All recovered module blobs, the original ten protocol tests, and the historical public calibration fixture come from the pinned #254 commit. Their Git blob hashes remain unchanged **except `experiment.py`**, which has an added independent authorization gate. This is a recovery/replication package, not a replacement for the current QPU-01 simulator.

## Offline reproduction

Run from this directory with Python 3.12:

```sh
python -m pip install -r requirements.txt
python -m pytest -q tests
python offline_replay.py
python ../hardware_q2_replay.py
python experiment.py simulate --out runs/local-reproduction
```

The archived hardware data are read from `../receipts/hardware_q2/`. The original project-local `receipts/calibration.json` is the captured input fixture used by the historical compiler and its tests.

The first four commands perform local computation and read stored data. They never request an IBM hardware job or connect to the live IBM account. Simulation also stays local.

## Recovery-specific cloud safeguards

The original historical Q2 pilot authorization does **not** authorize a new execution.

This recovery adds four independent submission requirements, in addition to the original verified Open Plan, current calibration, bounded resource estimate, physical layout, QPY and case-order checks:

- Explicit `--confirm-free-qpu` operator action.
- `AHR_QPU_ALLOW_LIVE_SUBMISSION=YES`.
- `AHR_QPU_FREE_PLAN_VERIFIED=YES`.
- `AHR_QPU_LEGACY_RECOVERY_APPROVED=YES` and `AHR_QPU_APPROVED_MANIFEST_SHA256` equal to the exact planned `manifest.json` file SHA256.

The entire recovered package remains HOLD for new cloud submission. Each future job requires separate approval of its exact manifest, present calibration, shot budget, and free allocation. Q3 stays simulation-only.

## Verification gates

Run the original 10 tests, the replay-equality check against stored `hardware_analysis.json`, explicit denial of unauthorized QPU submissions, and simulated interruption/recovery using a fake IBM service. The CI workflow installs the original versions recorded in `requirements.txt` and performs no cloud operations.

This mathematical experiment establishes signed finite-dimensional magnetic holonomy under measured controls. It does not establish a quantum advantage, a new proof of RH, or machine consciousness.
