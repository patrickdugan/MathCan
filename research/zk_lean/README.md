# ZKL-01–09: proof-carrying circuit design (development)

This module is a core-Lean starting point, with no new dependency or admitted proof. Run
`lake env lean MathCan/ZKLean.lean` and `lake build` on the repository-pinned Lean version.
The authoring environment did not contain Lean; compilation and axiom inspection are pending.
Inspect `#print axioms MathCan.ZKLean.trace_invariant`, `divSpec_unique` and `holds_append`.

| Gate | Scope in this branch | Still required |
|---|---|---|
| 01 | Canonical modular R1CS relation | Prove equivalence with Nova field implementation |
| 02 | Shape type targeted by SHZ importer | Actual synthesizer capture and identity attestation |
| 03 | Integer range weakening, no-wrap, exact min, quotient/remainder uniqueness | Boolean/range, comparison, division constraint refinements |
| 04 | Composition, redundancy, optimization transport | Wire-renaming, gluing and field backend theorem |
| 05 | Deterministic local loss and aggregate default waterfall | Full signed PnL, checked Rust arithmetic, ordered pro-rata, per-key claims |
| 06 | Cash conservation/floor, generic trace induction | Full book identity and capital sufficiency relation |
| 07 | Exact byte-width and conditional initial/terminal/count trace theorem | SHA-256, canonical bytes, public limb binding, real verifier reduction |
| 08 | Companion DataGoblin finite-domain gym | Proof-producing optimization and independent Lean replay |
| 09 | Relational interoperability contract | Pinned Clean/CLAP versions, actual translation, field and wire mapping |

For any backend B, prove `equivalent (denotation circuit_B) spec` over the same typed
public relation. For cross-field arithmetic additionally prove integer range and canonical
representation agreement; do not equate residues of different fields. Compose only with
an explicit shared interface. A cryptographic proof of acceptance requires an independent
reduction to the exact R1CS and application pins, under the proof system assumptions.

Production use is blocked. The companion SHZ audit design must pin source commit, compiler,
features, field, wire map, shape and verification key; the verifier must use those artifacts.
This branch does not claim a theorem about any live circuit or that a cryptographic hash is injective.
