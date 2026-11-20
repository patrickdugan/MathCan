# SelfModels continuity mathematics v0.3: temporary MathCan home

Original target: [MoralityLabAI/SelfModels](https://github.com/MoralityLabAI/SelfModels).
This directory stages the full `research/continuity_v1` package unchanged in MathCan while SelfModels branch-write access is unavailable.

The work covers exact event-history reduction and replay, NafsProbe read-only SQLite import and observation sidecar, finite autobiography information bounds, cumulative adapter-margin certificates, persona reweighting and certified-support containment, and sparse-feature geometry.

**Evidence status:** the Python CPU reference completed 38 unit tests, with one optional import from the full NafsProbe source skipped outside that checkout (37 passing). Lean proof sources are candidate files until a successful Lean kernel build is recorded. The `formal/` directory has its own pinned Lean toolchain; MathCan's root toolchain is independent. Historical NafsProbe experiment files are untouched.

Run from the MathCan root:

```sh
python -m unittest discover -s research/continuity_v1/tests -v
python -m research.continuity_v1.core
cd research/continuity_v1/formal && lake build
```

Provenance and scope: [README.md](README.md), [THEOREMS.md](THEOREMS.md), [formal/README.md](formal/README.md). The accompanying workflow runs the Python tests and independent Lean build in GitHub Actions.

When MoralityLabAI/SelfModels write access becomes available, cherry-pick or copy the `research/continuity_v1` directory and `.github/workflows/continuity-cpu.yml`. The MathCan staging note itself can be omitted from the downstream copy.
