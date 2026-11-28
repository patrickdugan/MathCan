# ACE-03C | Class closure certificates and upstream L audit

Status: OBJECT CHECKER PASS; construction of L and ZF derivations of its
closure properties remain open. No RH choice-elimination certificate.

## Pinned upstream

Zike Liu, lean-constructible-universe, commit
7f5a7d03d63d9769172f17350bbe8303996e5b53:
https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53

Inspected the pinned README, MATHEMATICAL_SCOPE.md, lean-toolchain,
lakefile.lean, root module and Constructible.lean export inventory;
also inspected declarations in VEqualsL.lean, TransitiveZFClosure.lean
and CHRelativeConsistency.lean. This is a source-interface audit,
not a full independent proof review or upstream build.

Upstream pins Lean v4.33.0-rc1 and mathlib
eba3d887fc52c98627f4b81507c0efc3096e91b9.
MathCan pins v4.35.0 and the ACE modules use Init. Avoid importing
upstream directly without a separate toolchain compatibility test.

The upstream project explicitly identifies its L as an external class
of Mathlib ZFSet, with individual levels internal ZFSets. Its semantic
models_ZFC theorems use the ambient Lean axioms propext,
Classical.choice and Quot.sound, according to its own scope statement.
The supplied semantic satisfiability theorem is not a derivation of
Con(ZFC) in ZFC. In particular, its external separation predicates,
ordinal-indexed recursion and choice are not automatically object-
language ZF proofs. This is the central foundational boundary.

Useful upstream interfaces:
- LStageZF, DefZF, L, LStageZF_isTransitive, LStageZF_mono:
  hierarchy construction and closure.
- TransitiveZFClosure.lean: empty_mem_of_isTransitiveZFModel,
  unorderedPair_mem_of_isTransitiveZFModel and
  sUnion_mem_of_isTransitiveZFModel. These go from model axioms to
  ambient closure; ACE-03C proves a complementary closure-to-axiom
  direction in its own proof calculus.
- TransitiveZFOmega and TextbookNaturalAddition/Multiplication/Power:
  arithmetic interpretation blueprint.
- VEqualsL.lean: constructibleWithParametersFormula has arity 14
  and its exact semantics is proved on LCarrier with canonical
  parameters; internalLStageAtFormula has arity 15. vEqualsLSentence
  existentially closes the parameter tuple. The upstream README
  explicitly limits the adequacy of this chosen sentence in arbitrary
  ZFC models. Do not treat it as a verified unary definition of L
  in arbitrary ambient ZF.
- CHRelativeConsistency.lean: semantic satisfiability statements
  with LCarrier witnesses.

All claims above are about inspected declarations and upstream
documentation; no fresh upstream kernel or axiom audit was run.

## ACE-03C construction

In zf_interface.mjs, classProofs() constructs five closed conditional
object derivations with a generic class predicate G. Define T by
forall x,z, G(x) and z in x implies G(z). Define EC by existence of
an empty set belonging to G. Define PC and UC by existence of the
ambient pair and union witnesses in G for G-valued inputs.

The output proofs conclude exactly:
T -> Extensionality^G;
EC -> Empty^G;
PC -> Pairing^G;
T -> UC -> Union^G;
T -> Foundation^G.

Extensionality transports equality of restricted members to equality
of all ambient members using transitivity. Union needs transitivity
to ensure the intermediate witness belonging to the input set lies
in G. Foundation obtains a minimal member using ambient Foundation
and uses transitivity to guard that member. Pairing and empty only
restrict universal membership characterizations of supplied witnesses.
These are checked as closed implications, not axioms about L.

For a concrete control, G(x) := forall y, y notin x. In ZF, extensionality
makes this class the singleton {empty set}; it is a proper subclass
of the universe and a set-sized class, not a proper class.
We discharge T, EC and UC with three closed proofs using definitional
class conversion, ordinary ZF empty-set axiom, and the fact that an
empty set is its own union. By modus ponens with the generic proofs,
four exact relativized axioms are checked from ZF with no hypotheses:
extensionality, empty, union, foundation. Each is also accepted by
the ACE-03B certificate compiler, in closed and open contexts.
The conjunction of the empty and union axioms compiles from a
3-node source proof to a 106-node target proof; tree representation
counts repeated subproofs, and this does not estimate RH proof costs.

Pairing closure is intentionally undischarged for this class. Pairing
fails because the singleton of the empty set does not itself belong
to the class. No claim that this class models all ZF.

## Actual experiment

Five conditional proof sizes (nodes): extensionality 40, empty 12,
pairing 22, union 46, foundation 31. Three closure proofs have sizes
11, 7, 24. Closed relativized axiom sizes: extensionality 52, empty 20,
union 83, foundation 43. All four imports checked at free depth 2
as well as depth zero.

Exhaustive all binary membership relations on domains of sizes 1..3
(530 structures), all subclasses (4,164 class/structure pairs).
16,194 conditional checks with required ambient axioms true; 4,836
with all class closure premises true. 2,120 closed-goal checks,
1,181 with required ambient axioms true. All nonvacuous checks passed.
133 singleton-empty pairing failures among ambient structures with
extensionality and empty, 144 nontransitive extensionality failures
with ambient extensionality true. Seven malformed/unauthorized
certificate controls rejected. These finite structures need not
satisfy ZF; finite semantic comparisons are independent regression,
not a proof of object-kernel soundness. The proof checker is still
an executable prototype and is not formally verified.

Prior ACE-03A and ACE-03B suites were rerun along with runC. The updated
zf_interface_receipt.json contains all three result blocks. Native
Lean modules are unchanged by this experiment; CI was still queued
when checked. No paid compute.

## ACE-03D gate

1. Specify an actual parameter-free pure set-language formula for L(x),
   with verified capture-safe encoding. Establish ambient ZF adequacy.
   The upstream parameterized formula is a blueprint, not this proof.
2. Produce closed object proofs of T, EC, PC and UC for that exact
   definition. The five conditional theorems can then discharge the
   corresponding relativized ZF axiom instances without new proof logic.
3. Establish internal infinity, power set, separation and replacement
   schema certificates, then the internal well-order and AC proof.
4. Keep choice-free object derivations distinct from metatheoretic
   semantic model construction; audit Lean universe strength separately.
