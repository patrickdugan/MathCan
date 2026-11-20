# Continuity v0.3: Lean 4 formal reference

The package requires Lean `v4.24.0`, with only its bundled `Init` library.

```sh
cd research/continuity_v1/formal
lake build
```

Modules:

- `ContinuityV1.lean`: original canonical-stream, certified-support, and
  exact integer-witness lemmas from v0.2.
- `ContinuityV1/Refinement.lean`: fold-based event collector equals a separately
  recursive event specification. Both use an ordered positive-support graph
  and a globally collected retraction set. It proves annotation-inertness,
  active-node and claim correspondence, and checks two retraction examples.
- `ContinuityV1/AdapterSuccession.lean`: an inductive proof that finite
  chronological margin losses telescope, with strict positivity after any
  number of bounded steps and an exact two-adapter counterexample.

The Lean event model uses Nat identifiers, while Python uses unique String
identifiers. The correspondence is conditional on injective renaming and on
Python's event-validation restrictions. It excludes JSON serialization,
SHA-256, SQLite transactions, and real-world evidence authentication.

The adapter theorem assumes each **actual** checkpoint update already has a
valid local margin-loss upper bound. A Hessian-derived cap is a mathematical
source of such a bound when a uniform segment-wise operator-norm premise is
satisfied. The supplied exact-rational Python checker validates arithmetic,
not the model or Hessian premise.

**Verification status:** All new Lean sources are awaiting kernel checking.
The environment used for artifact construction has no `lean` or `lake`, and
cannot resolve the Lean download host. The source and GitHub Actions build
are delivered as unverified proof candidates until CI succeeds. Python
conformance testing is independent of this statement.
