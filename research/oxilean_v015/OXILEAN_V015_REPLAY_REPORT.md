# OxiLean v0.1.5 replay and quantized spatial-interface report

Continuation of 2026-11-15. **The exact Hodge replay is accepted. The spatial
interface is supplied by an explicit construction with complete resource
accounting.** The full analytic network theorem has a paper proof; its elementary
integer clipping/capture and recurrence components are Lean/OxiLean checked.

## Hodge: executed acceptance evidence

- Intended target: `MathCan.Hodge.closed_path_gauge`.
- Exact MathCan source: `13151576dd83939f7850f7f3025a49fa98e370b8`.
- Original Hodge Git blob: `1207f7604ab9e04188188764b80d655866a5fa71`.
- Original Hodge source SHA-256:
  `6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5`.
- Lean 4.32.0-rc1, commit `b4812ae53eea93439ad5dce5a5c26591c31cb697`:
  unchanged source compiled, and matching leanchecker accepted its olean.
- lean4export source: `3de59f10bc4b4a0f2de698597aeb1246caa0df0a`, built locally.
- OxiLean source: `3adb983d2aefc6a596bdc8b63438f54feecd1f55`, unmodified.
- Exact export SHA-256: `05013ce15f2a75b521a8f9b0911060b3b129042dc75c331fa161ca4693f70892`.
- OxiLean `--json-full`: **1,256 verified, 0 unsupported, 0 rejected**.

The intended target has an explicit verified verdict. Its dependency-closed
graph contains 1,255 atomic export records, representing 1,414 constants. Every
required owner record has an explicit verified verdict. The exporter also
includes `Quot.ind` as part of the quotient primitive package: it too verifies,
giving 1,256 records and 1,415 constants overall. Minimality is not required
for dependency closure; the extra primitive is named and accounted for.

A separate Lean reference-parser comparison reconstructs the NDJSON terms and
compares **all 1,415 exported constants** with the unchanged native source
environment. Names, declaration kinds, universe parameters, types and proof/
definition values match. The only normalization erases expression metadata and
normalizes the non-semantic `let nondep` optimization hint. There is no reduction,
replacement theorem or substituted assumption. Source and comparison program
are retained, as are all raw JSON reports and exact input bytes.

The complete transitive axiom inventory is exactly **propext and Quot.sound**,
matching native `#print axioms` under both Lean 4.32 and the preserved 4.35
installation. Verified axiom records are understood assumptions, not proved
axioms. No sorryAx, extra axiom declaration, or unsafe dependency is present.

The precise source statement and proof remain:

```lean
theorem closed_path_gauge {V : Type u} (q : V → V → Int)
    (p : V → Int) (start : V) (xs : List V)
    (closed : endpoint start xs = start) :
    pathSum (fun u v => q u v + (p v - p u)) start xs =
      pathSum q start xs := by
  rw [pathSum_gauge, closed]
  simp
```

The closed-walk assumption, arbitrary vertex type, integer quotes and potentials,
finite-list walk and proof script were preserved. The earlier blocked report
is retained as OXILEAN_V015_REPLAY_REPORT_PRE_INSTALL.md; it is superseded here.

## Independent formal replay of the research components

The six QuantizedJet lemmas and eight new SpatialInterface lemmas all passed
native Lean 4.32 and leanchecker. Their combined dependency export reports
**1,449 verified, 0 unsupported, 0 rejected**, and all **1,616 constant types
and values** match the source environment. The export SHA-256 is
`8342c55b9a827072c73d8a5110b767b34fe1fdc519d5a3c54430d8b0ea246e37`.

Each theorem's exact statement is in its Lean source and native log. Each axiom
inventory is computed transitively from the exported graph and checked against
native `#print axioms`. They use subsets of propext, Quot.sound and
Classical.choice; every subset is listed individually in the JSON audit.
Capture itself uses propext and Quot.sound. There is no sorryAx. Full per-record
verdicts and each theorem's dependency-record IDs are included.

The new results formalize clipping range and step shortening, the integral
microstep identity for clipped translated anchors, exact bounded binary gates,
integer triangular selection and one-hot capture at a chosen finite index.
They do not formalize real differentiation or the full network approximation
theorem. The preserved Lean 4.35 environment is checked separately for project
compatibility; no default toolchain setting was changed.

## Spatial-interface construction and approximation theorem

SPATIAL_INTERFACE_THEOREM.md gives a full real-domain construction. It addresses
all previous missing obligations:

1. Continuous plateau selectors give exact coarse/fine addresses on safe sets.
2. Bounded-weight table interpolation selects only the correct code and initial
   jets there, with a narrow aggregation before shared amplification.
3. Clipped anchors remain inside the cube. A finer dyadic lattice makes all
   shortened endpoint steps integral; each frame pays for a bounded step tag.
4. A fixed serpentine rank and triangular one-hot gates capture the exact
   selected jet while carrying only a fixed number of registers.
5. Every ReLU layer, fixed coefficient, bias, zero dense slot, carry channel,
   code bit and polynomial-precision coefficient is charged.

For k=ceil(s)-1 and J=binom(d+k,d), the stated Hölder ball is uniformly
approximated with error O_{d,s}((NB)^{-s/d}), and sufficient resources

    P_actual=O_{d,s}(N+B(1+log B)+log(NB)),
    L=O_{d,s}(B(1+log B)+log(NB)),
    w=O_{d,s}(N+B^{1/d}+1),
    b_frac=O_{d,s}(B+log(NB)),
    maximum weight/bias=R_{d,s}, independent of N,B.

The paper includes explicit constants and a complete dense-layout ledger.
It proves correctness for every real point, with zero additional median boundary
error and no extension outside the cube. The former conditional interface premise
is discharged for this construction; temporal capture is explicitly charged at
O(B log B), not claimed free or O(B). Finite certified jet data suffices for
offline encoding; no training algorithm or efficient derivative acquisition is
asserted. Parameters are exactly dyadic. Fixed IEEE activation precision does
not suffice as code length grows; propagation bounds have their stated scope.

This yields the (Pb)^{-s/d} rate in the sufficient proper-quantization range
specified in the theorem, and logarithmic losses in the depth-limited case.
It does not settle all prescribed small widths, the whole under-quantization
regime, or a cost-free depth/precision conversion. The full network theorem is
proved on paper and implemented; it is not advertised as a Lean theorem.

## Executed regression evidence

- The original eight OxiLean controls retain their exact named verdicts:
  **73 verified, 0 unsupported, 32 expected rejected**. They are separate from
  the successful target/lemma exports; rejected controls are not campaign failures.
- New explicit spatial circuits pass **8,299 exact assertions** in
  six suites. Tests cover endpoints, corners, boundaries, safe addresses,
  snake ranks, packed streams, exact capture, polynomial arithmetic, dense
  counts, weight/precision bounds and the full ReLU median network.
- An independent numeric-matrix evaluator agrees with the register evaluator.
  The materialized small example has 907,727 dense scalar slots, width 94,
  depth 1,014, maximum coefficient 64 and 36 fractional bits. These large
  finite constants are reported honestly; asymptotic constants depend on d,s.
- The previous **83,362** exact component assertions remain valid. Five
  dependency-auditor tests and fifteen shell syntax checks pass. Five additional acceptance tests prove that
  zero-exit unsupported targets, omitted dependency verdicts, changed hashes,
  mismatched proof values and unexpected axioms are refused.

The tests are finite implementation checks. The all-domain proof and resource
derivations are in the theorem document, not inferred from these counts.

## Installation, reproducibility and remaining limits

The user authorized installation in this continuation. The official release
archive's SHA-256 was verified as
`ce6e79dd19ea03c0bc17f9d565c3bac20cd2884561e3b431e5b293c1fbb2b5b3`.
Lean 4.32 is installed privately under work/toolchains, alongside the untouched
4.35 runtime. Linux library symlinks were restored after Windows extraction;
the installed files were compressed with NTFS compression to recover disk
space without changing their contents. Binary hashes and build logs are included.
The temporary installer archive was removed after successful verification.

The old evaluation archive is still unavailable. Its historical numerical
claims are not relabeled as reproduced evidence. New sources, exact exports,
logs, comparison programs, acceptance receipts and circuit matrices are delivered.
There is no remaining Hodge toolchain or replay blocker. Remaining research scope
is full Lean formalization of the analytic theorem and tighter resource tradeoffs
outside the stated sufficient regime.

Work remains on the two isolated research branches. COMMITS.json in the packet
records exact final local commits and clean-worktree checks. No push, merge,
external message or calendar change was performed. The old Tetsuya draft remains
unsent and predates this continuation.
