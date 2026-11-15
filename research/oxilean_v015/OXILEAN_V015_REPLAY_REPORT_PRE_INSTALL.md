# OxiLean v0.1.5 independent replay report

2026-11-15, Asia/Taipei. **The pinned Hodge replay is not complete.** The exact
4.32.0-rc1 toolchain is unavailable and was not installed. No target NDJSON,
OxiLean target verdict, or pinned exported statement comparison is claimed.

## Measured results

- Built unmodified OxiLean `3adb983d2aefc6a596bdc8b63438f54feecd1f55` using
  preinstalled Rust 1.94.1. The three zero-runtime-dependency crates were
  compiled directly with rustc to avoid downloads/resolving unrelated Cargo
  workspace development dependencies. The full source SHA-256 manifest is
  included. Binary SHA-256: `831e7ad751d69d7f27e8ee59ec40246a6256e971e11f418b0e92f9722771e9fa`.
- All eight supplied controls passed the exact named-verdict checks. Every
  record has a `--json-full` verdict; counts are recomputed from that array,
  input hashes are compared, and the expected named rejection sets are tested.
  **73 verified, 0 unsupported, 32 rejected**, over 105 top-level export
  records. Inductive bundles are atomic OxiLean report entries; these are not
  105 separately reported constructor/recursor constants.
- The unchanged, byte-exact Hodge source compiled under the already installed
  Lean 4.35.0 and passed that distribution's leanchecker. Its native dependency
  closure contains **1,378 constants** and axioms **propext, Quot.sound**.
- Six new Init-only integer recurrence theorems compiled and passed leanchecker.
  Five use **propext, Quot.sound, Classical.choice** through the core arithmetic
  proof dependencies; corrected_error_identity uses propext and Quot.sound.
  There is no sorryAx, added axiom declaration, or unproved Lean assumption.
- The native graph union for Hodge and the six new theorems contains 1,546
  constants. Full edges and each root's closure are included. Native graph and
  `#print axioms` inventories agree. This is Lean 4.35 evidence only.
- New Fraction controls pass **83,362 assertions**; five dependency-auditor
  tests pass. The replay shell script passes `bash -n` and stops at the
  missing TC432 gate before performing any compilation or installation.

## Source and environment integrity

| Component | Exact pin / observed version |
|---|---|
| OxiLean | `3adb983d2aefc6a596bdc8b63438f54feecd1f55`, v0.1.5 |
| lean4export source | `3de59f10bc4b4a0f2de698597aeb1246caa0df0a` |
| Required Lean | 4.32.0-rc1, source `b4812ae53eea93439ad5dce5a5c26591c31cb697` |
| Installed Lean | 4.35.0, source `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| MathCan source | `13151576dd83939f7850f7f3025a49fa98e370b8` |
| Hodge Git blob | `1207f7604ab9e04188188764b80d655866a5fa71` |
| Hodge source SHA-256 | `6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5` |
| Compactification base | `714c5ba87bb17a16f1ce4814c02abde2d1093e9d` |
| Export format in control files | NDJSON 3.1.0, Lean 4.32.0-rc1 |

The Lean 4.35 installation and MathCan lean-toolchain file were preserved.
Fresh clones/worktrees initially received Windows line-ending conversion;
normalization restored exact Git blob bytes before measured tests. No original
repository worktree was reset. Git worktree metadata created on Windows was
not usable by Linux Git; source-integrity checks in the Linux build use a
manifest generated from checked Git blobs instead. Initial preflight errors
were infrastructure errors, not proof verdicts.

## Exact target preserved

```lean
theorem closed_path_gauge {V : Type u} (q : V → V → Int)
    (p : V → Int) (start : V) (xs : List V)
    (closed : endpoint start xs = start) :
    pathSum (fun u v => q u v + (p v - p u)) start xs =
      pathSum q start xs := by
  rw [pathSum_gauge, closed]
  simp
```

This is arbitrary vertex type, integer-valued directed quotes and potentials,
and arbitrary finite lists, with the explicit closed-walk assumption. The
source, proof and assumptions are unchanged. Native `#check` output agrees;
comparison with an imported pinned NDJSON statement is **not yet possible**.

## Measured control verdicts

| Fixture | verified | unsupported | rejected | exit |
|---|---:|---:|---:|---:|
| ProjOutOfProp | 5 | 0 | 2 | 1 |
| ProjRecIndexed | 22 | 0 | 0 | 0 |
| RecRuleTruth | 12 | 0 | 3 | 1 |
| RecRuleJunk | 7 | 0 | 8 | 1 |
| RecRuleControl | 3 | 0 | 2 | 1 |
| RecNameMixedStyleTruth | 9 | 0 | 4 | 1 |
| RecNameMixedStyle | 8 | 0 | 5 | 1 |
| RecNameFlat | 7 | 0 | 8 | 1 |

ProjOutOfProp rejects both the witness projection and its false theorem;
ProjRecIndexed accepts all 22 valid records. RecRuleJunk rejects the malformed
family and every dependent, including boom. RecNameMixedStyle rejects the
malformed family and dependent false claims while allowing the unrelated
definition under the now-free hierarchical name. The Truth fixtures deliberately
contain invalid claims. Their nonzero rejection counts are expected controls.
These runs use the repository's committed NDJSON; they were not regenerated
and were not differentially replayed under missing Lean 4.32 in this campaign.

- `ProjOutOfProp.ndjson`: `ed7c545acc77f3cff50be3377a4bbff971384122d7a7bc7898cbcb5ef4dd0a22`
- `ProjRecIndexed.ndjson`: `53905a2f589da6eccda8081eb04bd88794b2374e39fcb9c2d98a5f448c93b28b`
- `RecRuleTruth.ndjson`: `eaf3c38c0638fe1b2d6b42b5a38eb5ebe9136dcc39fc07bfa0e33057db81d63a`
- `RecRuleJunk.ndjson`: `9f88927a96df3c7b439b1d6441e199b0f9e1504a9d8d7a29dad468b0bd3cc8a9`
- `RecRuleControl.ndjson`: `1ab47077e7aa6400eaf11bf02cd8800ef770392bbd846e04a5298f219aa1d919`
- `RecNameMixedStyleTruth.ndjson`: `1f36640514c59330a0f6bd7faab1f5c5fd078155bd809272555d9682a68a5af0`
- `RecNameMixedStyle.ndjson`: `0df8e3d31665a47128aa6da412df065936637a8ae4cafe623e37a3fb06d908cf`
- `RecNameFlat.ndjson`: `a7fcb06a69cb6616821d990d769c36b7e8f11a4489a1f68aca1698aac9893cc9`

## Axiom and dependency audit

`OXILEAN_AXIOM_AUDIT.json` distinguishes the unavailable pinned target inventory
from the measured native inventories. The native graph walks both types and
proof/definition bodies, including opaque values, mutual-family metadata and
recursor rules. It agrees with every printed root axiom list and contains no
missing explicit reference. The new NDJSON auditor also tracks projection
type names and implicit literal types, preserves name components, reports
duplicate owners and missing constants, and treats inductive bundles atomically.

An axiom record being verified means its type is admissible as an assumption,
not that the axiom was proved. Native Hodge is not axiom-free. In particular,
propext and Quot.sound are understood Lean logical principles. Classical.choice
appears in five new lemma closures and is explicitly disclosed.

The graph auditor is structural, not another kernel. Its five tests exercise
positive bundle closure, flat/hierarchical name separation, duplicate-name
retention, fail-closed unknown expression references, and transitive axiom/type
dependencies. A malformed control can be structurally closed and still invalid.
Kernel outcomes and graph diagnostics remain separate.

## Mathematical progress and exact limits

See `QUANTIZATION_D_DIMENSION_THEOREM.md`. Complete arguments establish
factorial-normalized INTEGER adjacent jet transport, a fixed correction
alphabet, uniform recurrence error, a sentinel digit reader with precision
propagation, a bounded-weight table lookup with exact dense parameter count,
shifted-grid coverage/median stability, triangular multiplication and polynomial
transport-noise growth conditional on correct digits. The six Lean statements
and axiom printouts are in the source and `quantized_jet_lean435.log`.

The whole-network result is explicitly conditional on the compiled spatial
interface. Its resource implication is P_actual=O(N+B log(NB)),
L=O(B log(NB)+log N), b_frac=O(B+log(NB)), constants depending on d,s.
It is not asserted as an unconditional approximation theorem. Two explicit
counterexamples refute the old correction sign and a two-sided robustness
claim for finite digit packing without a sentinel.

The new quadratic test has 1,025 points, 248 payload bits and 498 stored
fractional bits; maximum error 1/1024 equals its bound. The historical claim
of 863 points, 288 bits and maximum error 23/524288 was recovered only as
conversation text. Its original source hashes, logs and computations cannot
be independently audited because the archive is unavailable.

## Remaining prerequisites and exact commands

The package and original REPORT, CONSTRUCTIVE_UPPER_BOUND, JET_STABILITY_ADDENDUM,
replay/auditor sources, packed-jet source/results and acceptance log were not
found in the searched user/workspace/WSL locations. Prior chat written results
were recovered; its sandbox links did not expose local artifacts. All new
scripts are clearly replacements, not recovered originals.

Provision an existing Lean 4.32.0-rc1 distribution with lean, lake and
leanchecker (Linux x86_64 in this workspace), then build the already retrieved
exporter source at its exact pin. These commands are supplied, not executed:

```bash
export TC432=/absolute/path/to/lean-4.32.0-rc1-linux
export EXPORTER_SOURCE=/absolute/path/to/pinned/lean4export
export PATH="$TC432/bin:$PATH"
"$TC432/bin/lean" --version
git -C "$EXPORTER_SOURCE" rev-parse HEAD
(cd "$EXPORTER_SOURCE" && "$TC432/bin/lake" build lean4export)
export EXPORTER="$EXPORTER_SOURCE/.lake/build/bin/lean4export"
export MATHCAN_SOURCE=/absolute/path/to/unchanged/pinned/MathCan
export OXI_BIN=/absolute/path/to/work/build/oxilean-verify
export REPLAY_OUT=/absolute/path/to/new/replay-results
export AUDITOR=/absolute/path/to/audit_export.py
bash /absolute/path/to/replay.sh
```

Use a source-only MathCan worktree at the pinned commit for that script; the
new research branch has additional files. Git paths in this shell example
must be native to the executing OS. The script deliberately refuses missing
prerequisites and never downloads/installs. It writes 4.32 objects separately,
leaving the 4.35 toolchain and outputs intact. A completed script still needs
an explicit statement comparison, satisfactory verdict for every target
dependency, and an understood axiom inventory before campaign acceptance.

## Local branches and validation

- MathCan: `research/quantized-jet-replay-20261115` from the requested source pin.
- Compactification-Theory: `research/quantization-d-audit-20261115` from
  the clean existing checkout above.
- OxiLean diagnostic worktree: `research/v015-control-audit-20261115` at the
  requested pin; no checker source change.

`COMMITS.json` in the delivered packet records the resulting local commits.
No push, merge, installation, paid compute, external message or calendar change
was performed. `TETSUYA_PROPOSED_EXCHANGE.md` is an unsent draft.
