# RHD-03 | Actual Main proof route and OpenLiteratureStatements

Source pin: `leanprover-community/riemann-hypothesis` commit
`f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`. This is a
source-text dependency audit; mathematical and kernel verification of
the full claimed RH proof remain separate.

## Which RH route is used by Main?

The original [`src/Main.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Main.lean)
states `riemannHypothesis := rhOfAll`. The theorem
`rhOfAll` in `src/Supplements/Kernels/MainTheorems.lean` calls
`Formalism.VW.rh_of_every allChi`. Here `allChi` is supplied by
`UpperTheory.FinalTheorems.everyCharacter`.

The final-character theorem in
`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`
constructs `everyCharacter_of_row` from an integral Galois row
and an automorphic window. The literature theorem applies
`every_character_of_theta_integrals_local_matching`, a
`topCovolSlim2_use_alt_alt` covolume bound, and
`local_langlands_gl_recT_exists_of_literature`.

This identifies the direct theorem route relevant to the actual
statement in Main. The conditional family theorem `rh_of` in the
`ZetaZeroFreeRegion` formalism is a separate source route. The
source audit does not establish whether it is present among the
original Main proof's transitive imported artifacts.

## The published OpenLiteratureStatements interface

The source defines three fields:

- `caraianiLocalGlobalDual : UpperTheory.One.M.Row`
- `localLanglandsExists : UpperTheory.Zero.LLC.RecTExists`
- `galoisRepOfPolarizedPairLit : UpperTheory.One.M.Row`

At the proposition level this is equivalent to a single `Row`
witness and a `RecTExists` witness. The result is proved in
`MathCan/RHMainLogic.lean` under Lean 4.35 with Init.

## Wrapper census from source bodies

The pinned literature source contains 195 theorem wrappers taking
an explicit `O : OpenLiteratureStatements` parameter. A lexical
source scan finds no occurrence of the identifier `O` in 152 of
their displayed theorem-value bodies; 43 do mention `O`.
Four wrapper bodies directly select one of the three O fields
(two the same Row type, one local Langlands field).

A graph of *named wrapper-to-wrapper calls in the source bodies*
has 311 observed edges and visits all 195 wrappers when traversed
from `every_character_of_literature_of_vWin`. These are
source-text observations under the pinned Git blob identity.

The unused-parameter count does not establish that the theorem is
mathematically vacuous or that a Lean proof is invalid. A wrapper can
have an explicitly present but unused parameter because its conclusion
has been established elsewhere. For full kernel semantics we would
need to inspect the elaborated proof terms, their axioms and the
construction of the imported theorem constants.

## Where further mathematical effort belongs

Directly audit `galoisRepresentations_of_thetaLift tLiftK`,
`automorphic_window_of_inputs`, the local Langlands witness, and
the covolume bound that feeds the final every-character theorem.
Preserve the distinction between independently established input
lemmas, copied proof parameters, imported compiled artifacts, and
unverified mathematical premises.

## Reproduced source graph

The [pinned CI run](https://github.com/patrickdugan/MathCan/actions/runs/44915161411) passed four source-audit mutation tests and four native Init Lean proofs. The uploaded [original JSON graph](https://github.com/patrickdugan/MathCan/actions/runs/44915161411/artifacts/14711581539) is SHA-256 `b00378b34fa738fd2eecd176dfb3fc9977ab02ad84e3eaacf56f8ada4804994f` (unzipped JSON bytes). The [compact receipt](main_source_census_receipt.json) retains the verified node/edge counts and four direct parameter-field consumers.

Direct `O` projections are found only in `literature_automorphy`, `carU_local_global_of_literature`, `pair_u_of_literature`, and `local_langlands_recT_exists_of_literature`. This statement concerns the 195 wrapper theorem values within the exact archived source file. Indirect dependencies through other wrapper constants and external imported theorems require separate examination.
