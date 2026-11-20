# SM-MATH-01 to 06: CPU-only continuity mathematics

This isolated package gives `MoralityLabAI/SelfModels` a small, exact reference for **canonical autobiographical state, continuation memory lower bounds, adapter succession margins, external persona stability, sparse-feature geometry, and certified-action containment**. It does not change `nafsprobe/`, either SMTK snapshot, or their historical results.

## Run

From repository root, Python 3.10+ with the standard library:

```sh
python -m unittest discover -s research/continuity_v1/tests -v
python -m research.continuity_v1.core
```

The tests complete in under a second on the development CPU. The second command prints a deterministic JSON receipt, checked byte-independent against the committed parsed fixture.

## Included

- `core.py`: append-only typed event replay with alternative justifications; interpretation-only model-version changes cannot mutate canonical state; distinct canonical and full-history SHA-256 digests.
- `core.py`: exact enumeration of all `n`-bit histories under every size-`k` subset-count continuation query; 12-bit/6-subset reference.
- `core.py`: rational local and sequential Hessian-margin lower bounds, including a two-adapter interaction counterexample.
- `core.py`: exact rational reweighting, total variation, and stepwise trajectory-coupling bound.
- `core.py`: exact one-dimensional subspace-angle and coactivation conditioning diagnostics; certified-support persona sorter.
- `THEOREMS.md`: the mathematical statements, proofs, assumptions, failure conditions, related repositories, and bibliography.
- `results/EXACT_CPU_RECEIPT.json`: committed expected exact output; the tests independently regenerate it.
- `tests/test_core.py`: exhaustive finite checks and fixture-level regressions.

## Measured in this CPU reference

- `n=12, k=6`: 4,096 different continuation signatures, 13 total-count classes, largest total-count fiber 924.
- `m(a,b)=1/4-a*b`: isolated update margins `1/4,1/4`, composed margin `-3/4`; cumulative-start second-order bound exactly `-3/4`.
- Persona multipliers `(1,9)` with prior `(3/4,1/4)`: TV exactly `1/2`, attaining the sharp multiplier-range bound.
- Uniform per-step TV at most `1/10` for four steps: trajectory divergence bounded by `3439/10000`.
- Two coactive, unit-norm features: minimum squared singular value exactly `2/10001`; sign reversal of a line leaves its subspace unchanged.
- Model interpretation annotations and arbitrary persona multipliers cannot introduce new certified actions in the reference semantics.

These are exact constructions and conditional inequalities, not observational evidence about an LLM's selfhood or self-modification. Neural checkpoint verification and Lean kernel checks are subsequent work.

## Design relationship to existing code

`nafsprobe/causal-v0.2/nafs_probe.py` already persists a dataclass `SelfModel` in SQLite. The new graph illustrates how its recorded claims could be supported by independently addressable evidence. The starter SMTK's `Ledger` and `CommitmentAutomaton` are richer in other directions; they remain unchanged.

For deployment, keep the canonical reducer inside a trusted storage and execution boundary. The current hash is a reproducibility fingerprint and supplies neither authentication nor append-only enforcement against an attacker controlling storage. The prototype has no external tools and runs without a GPU.

## v0.2: read-only NafsProbe bridge and observed-revision sidecar

`nafsprobe_bridge.py` imports the **actual** NafsProbe `agent_state(run_id,payload)` SQLite schema without modifying its historical code or database. It validates the seven stored `SelfModel` fields. Current simulator-recorded identity, commitments and belief summaries become namespaced canonical claims (`nafs.*`); model-authored reflections, episodes and autobiographical prose remain attributed interpretations. No imported claim is an `authorized:*` action grant. The source JSON remains an unverified mutable snapshot, regardless of a simulated `signed_dispatch` label.

```sh
python -m research.continuity_v1.nafsprobe_bridge \
  --db path/to/nafsprobe.sqlite3 --run-id experiment1
```

NafsProbe overwrites one JSON state for each `run_id`. It does not store the original assertion/retraction chronology. To record **when this adapter first sees** changes, a separate SQLite observation sidecar can append versioned source-state changes and interpretations, with deterministic event IDs, retraction targets, a hash chain and independent replay/audit:

```sh
python -m research.continuity_v1.nafsprobe_sidecar \
  --db path/to/nafsprobe.sqlite3 \
  --sidecar path/to/continuity-sidecar.sqlite3 --run-id experiment1

python -m research.continuity_v1.nafsprobe_sidecar \
  --sidecar path/to/continuity-sidecar.sqlite3 --run-id experiment1 --audit-only
```

The source database is always opened read-only. The sidecar is an optional **separate output database** and only changes when the sync command runs; this package does not create a background observer or an autonomous agent. A sidecar event marks an observation of snapshot differences, not the true historical time of a legacy action. Re-running sync on unchanged bytes is idempotent, and exact source payload bytes are bound by SHA-256. The chain detects uncoordinated edits but does not authenticate data against an attacker capable of rewriting the chain.

Commitments and simulated beliefs are entrusted to the input snapshot only under the explicitly limited simulator assumption. The sidecar currently replays its whole history during audit and preserves every observed narrative annotation. That is suitable for a small finite gym; scalable indexing, signatures, conflict semantics, retention/privacy rules, and real authorization checks are future work.

The legacy schema compatibility test uses synthetic SQLite fixtures locally and a real import of `nafsprobe/causal-v0.2/nafs_probe.py` **when run in the full SelfModels checkout**. Local stand-alone artifact testing skips only that latter source-dependent test.

## v0.2: initial Lean module

`formal/ContinuityV1.lean` gives elementary proofs and exact witnesses for annotation separation, idempotent canonical extraction, certified-support containment, the two-update counterexample, and arithmetic cases for coupling and sparse geometry. It is a lightweight, Mathlib-free Lean 4 package with a CI job using `leanprover/lean-action`.

```sh
cd research/continuity_v1/formal
lake build
```

**Proof status:** The local environment has no Lean compiler or network access to install one. Lean source is provided for independent kernel checking in CI. Only the Python suite has run locally. Full theorems for arbitrary subset-continuation families, Hessian remainder bounds, sharp persona total-variation bounds, and Python-to-Lean reducer refinement remain explicitly outstanding.

## v0.3: formal event semantics and chained adapter receipts (21 November 2026)

The new CPU-only mathematics extends the baseline without changing the
historical NafsProbe experiments or existing frozen result receipts.

- `formal/ContinuityV1/Refinement.lean` models evidence nodes, assertion
  retractions, and versioned narrative notes. It supplies an independent
  recursive specification and a fold-based collector, with a general
  refinement proof. Downstream claims are evaluated after retractions.
- `formal/ContinuityV1/AdapterSuccession.lean` defines a finite path of
  locally bounded decision-margin changes and proves cumulative preservation
  when the total loss cap is below the original margin.
- `refinement_checks.py` implements an independent recursive support oracle
  for Python conformance testing on positive-support DAGs.
- `adapter_succession.py` checks linked checkpoint and rational Taylor-bound
  receipts, including the bilinear two-adapter interaction counterexample.
- `tests/test_refinement.py` and `tests/test_adapter_succession.py` supply
  deterministic finite controls.

```sh
python -m unittest discover -s research/continuity_v1/tests -v
cd research/continuity_v1/formal && lake build
```

The first command is locally verified. `lake build` requires Lean 4.24.0 and is
prepared for CI; local kernel checking remains unavailable. The formal result
is a theorem about **two Lean models of the event collector** and a general
integer-scaled certified-margin path. It is *not* yet a Lean proof of Python's
implementation, of the SQLite sidecar, or of an empirical neural Hessian cap.
See `THEOREMS.md`, Theorems I and J, for precise assumptions and scope.
