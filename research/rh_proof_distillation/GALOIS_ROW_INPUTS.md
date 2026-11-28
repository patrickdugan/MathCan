# RHD-04 | Galois row: geometric realization and eventual theta lift

Live RH proof source pin: `leanprover-community/riemann-hypothesis`
commit `f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`.
This note investigates the actual character-theorem input branch.

## Two independently supplied mathematical premises

`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` is built
from `UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift`
with `UpperTheory.TP.K.tLiftK`. The former invokes
`galoisLocalGlobalStrong_of_geometry_lift` on the proof
`UpperTheory.Gal.Int.Geo.geoOne_holds` and the provided lift.

The geometric term `GeoOne` is produced by
`geometric_realization_of_weight_one` using the source
steps theorem, the Kodaira-Spencer/holomorphic Lefschetz step,
and a `PlanEx` construction. The theta-lift term uses
`tLift_holds_k`, built from `tools_holds_k` and
`tLift_of_tools_k` with a theta integrability premise.

These are concrete, source-named theorem inputs rather than
generic placeholders. The mathematical task is to review what
their geometry and lift statements assert and whether their
imported prerequisites are independently justified.

## Two theta lifting propositions agree syntactically

`HalfIndexLattices/TLiftK.lean` defines `UpperTheory.TP.TLiftK`.
`ThetaKernels/GalTPDefs.lean` defines `UpperTheory.TP.TLift_k`.
After replacing the qualified `GoodK` name with the local
namespace spelling and normalizing whitespace, their
entire quantified statements coincide byte-for-byte.

The source states for every admissible initial CM-field datum
and Hermitian input a dimension threshold `d0` such that,
for every `d>=d0` and every later admissible skew-Hermitian
input, character, weight and automorphic representation,
an appropriate lifted representation exists. In particular,
`d0` is chosen before the later data, though it can depend
on the original field, rank and Hermitian input.

`MathCan/RHGaloisRowInputs.lean` proves a conditional logical
Galois-row interface and two quantifier-order counterexamples.
A pointwise threshold `d0(local)` cannot automatically replace
the stronger source threshold selected before all later data.

## Separately supplied local Langlands witness

The final `everyCharacter_of_row` construction passes
`UpperTheory.Zero.LLC.recTExists` separately from the
Galois row. The pinned `RecTExists.lean` source builds
that witness from `artEx`, `cuspEx`,
`GlobalTheory.LocLanglands.exists_isLExt`, dimension and
twist transport, and other explicit representation properties.
The exact source audit records this route independently.

## Verification level

The dedicated RHD-04 CI uses a sparse checkout of **twelve**
source files, requires every original Git blob to match the
published pinned commit and verifies the named source links.
It checks the theta-lift statement equivalence as a normalized
source-text comparison. The independent Lean 4.35/Init
theorems assert only conditional logic and quantifier ordering.

The source-level statements here do not establish the global RH
result, nor constitute a kernel recheck of the 175k-module
published formalization. The further work is actual theorem
dependency extraction for `GeoOne` and `TLiftK` premises.
