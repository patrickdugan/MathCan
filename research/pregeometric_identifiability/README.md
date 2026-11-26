# PGC-01: operational identifiability

The module [OperationalIdentifiability.lean](../../MathCan/OperationalIdentifiability.lean) proves four elementary statements about an observation map. Lean 4.35.0 checks every declaration with an empty axiom dependency list. Its only import is `Std`.

## Mathematical claim

Let `observe : World → Record` and `property : World → Property`. If two worlds have the same accessible record and different property values, every decoder from those records fails on at least one of the worlds. Formally:

\[
o(w_0)=o(w_1)\ \land\ p(w_0)\ne p(w_1)
\quad\Longrightarrow\quad
\neg\exists d\;\forall w,\ d(o(w))=p(w).
\]

| Declaration | Checked statement |
| --- | --- |
| `decoder_constant_on_observation_fibers` | Equal records receive equal decoded values. |
| `no_uniform_decoder_of_indistinguishable_worlds` | A property difference inside an observation fiber obstructs a uniformly correct decoder. |
| `postprocessing_cannot_remove_decoder_obstruction` | Deterministic processing of accessible records preserves that obstruction. |
| `observation_preserving_update_cannot_separate` | An update preserving each accessible record also preserves equality between records. |

The last theorem assumes record preservation. Quantum trace preservation has a separate mathematical meaning.

## Reproduce

From the repository root, with its declared toolchain installed:

```sh
lake env lean MathCan/OperationalIdentifiability.lean
```

The four `#print axioms` reports appear in [lean_validation.log](lean_validation.log). The [validation receipt](lean_validation.json) records the source SHA-256 and compiler version. The [compiler release receipt](compiler_release_receipt.json) records the official download and its verified digest. The focused CI workflow checks the source directly and compares its printed reports to the committed log.

## Scope and experimental witnesses

The types in the theorem are arbitrary. A physical application requires a specified class of admissible worlds, an observation protocol and an exhibited pair with different target values. Establishing a pair of indistinguishable spacetime models would supply such an application.

[SelfModels' finite observer experiment](https://github.com/MoralityLabAI/SelfModels/tree/research/pgc01-observer-budget-20261126/research/pregeometric_observer) provides a concrete witness for a Boolean dependence property. Its world `0` has all four truth-table outputs equal to zero. World `8` changes the fourth output. The first three fixed queries produce the same record, while the dependence labels differ. An additional query separates those worlds.

[Compactification Theory's PGC-01](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/pgc01-operational-foundations-20261126/research/pregeometric_compactification) checks operational influence with supplied registers and update ticks. Its assumption audit records the further work required for a Lorentzian continuum, a universal null boundary, dimension selection, Einstein variables and a derived gravitational coupling.

The module's proof scope ends at equality and decoding. The computational witnesses are checked by their respective Python suites; their code is outside this Lean module.
