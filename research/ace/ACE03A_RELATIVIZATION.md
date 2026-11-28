# ACE-03A | Generic class relativization and restricted proof translation

Status: FINITE EXECUTABLE CHECKED; LEAN KERNEL PENDING. The class C is an
explicit unary predicate, not a definition of the constructible universe.

## Object language and translation

De Bruijn variables range from zero to k-1 at context depth k.
Atoms are equality, membership, falsum, and (target only) the class
predicate G. Compound formulas use conjunction, disjunction,
implication, universal and existential quantification. Source inputs
are checked to exclude G. Quantification increments the scope by one.
Relativization R preserves atoms and propositional connectives and maps
universal bodies p to G(0) -> R(p) and existential bodies p to
G(0) and R(p). Indices refer to the same binders after translation.

The lift operation increments free indices, accounting for intervening
binders. Instantiation replaces bound index zero with a specified
in-scope free variable and lowers indices above the removed binder.
The compiler uses the identities R(lift p) = lift(R p) and
R(inst p x) = inst(R p x). They follow by syntax induction: new guards
are locally bound at index zero and stay fixed when traversed below
their quantifier. Executable instances of both identities are tested;
a kernel-checked syntactic proof is still due.

## Derivation transformation

The executable kernel checks a restricted intuitionistic natural
deduction calculus with hypotheses, reflexivity, implication,
conjunction, disjunction, falsum elimination, and both quantifiers.
Equality substitution, general axiom schemas, classical inference,
and a full ZF proof kernel remain outside this fragment.
The source judgment Gamma |- p at depth k translates to
G(0), ..., G(k-1), R(Gamma) |- R(p).
Hypothesis references map to target derivations and guard references
are maintained separately. The following invariant is preserved by
induction on derivation structure.

* A hypothesis uses its corresponding target derivation. Reflexivity
  and propositional rules are retained; newly assumed formulas are
  relativized, and hypothesis maps extend under local assumptions.
* Universal introduction shifts existing context formulas, introduces
  a fresh guard at the newly bound variable, then discharges the guard
  by implication introduction before universal introduction.
* Universal elimination instantiates the translated universal and
  discharges its guard by implication elimination with the stored
  evidence for the chosen variable.
* Existential introduction pairs the stored guard with the translated
  witness formula and introduces the guarded existential.
* Existential elimination shifts the prior context and introduces the
  conjunction of guard and witness property; its left projection
  supplies the new guard and its right projection supplies the
  source witness assumption. The kernel requires the branch
  conclusion to be the lifted target, preventing witness escape.

These cases provide the mathematical proof sketch of the compiler's
invariant. The executable kernel rechecks each emitted proof against
the translated context and independently compares the inferred goal
with the expected relativized goal. The proof calculus and compiler
have not themselves been verified in Lean.

## Semantic lemma

MathCan/ACERelativization.lean states and proves the intended semantic
transport result for a generic membership relation E and subtype
defined by C. Assignments on the subtype and ambient domain agree
pointwise after forgetting the subtype proof. Satisfaction on the
subtype (with G interpreted as True) is equivalent to satisfaction of
the relativization in the ambient interpretation. Induction on formulas
handles quantifiers by constructing a subtype witness from its class
membership proof. It requires no selected global inverse.
The native Lean statement uses total assignments Nat -> Subtype C,
so it cannot instantiate an empty subtype. The executable finite
semantics also covers empty classes with closed formulas.
This theorem is not a definition of L or of its satisfaction predicate
inside ZF. Lean elaboration and the actual transitive axiom report
remain pending.

## Reproducible finite experiment

Three seeds 109,113,127; 128 finite relational structures and class
predicates per seed; ambient cardinalities 1 through 4. For each
instance one generated formula of depth 4 is compared under an
induced-subclass evaluator and a separate ambient guarded evaluator.
There are 384 successful comparisons including 88 empty classes;
384 lift commutation checks and 226 instantiation checks.

Each instance generates ten proof families (identity, universal
elimination, existential introduction, universal introduction,
existential elimination, quantified modus ponens, existential modus
ponens, disjunction elimination, falsum elimination, reflexivity).
All 3,840 source proofs compile to accepted target derivations with
the exact expected goal; the generated source proofs have 1..3 free
variable slots. This is a template-driven smoke test, not a benchmark
of arbitrary derivations. The implementation also supports closed
judgments and additional propositional rules, but this run does not
provide positive coverage of every implemented rule or closed-proof
compilation. A future adversarial audit should include deeper nested
proofs, independent checker implementation, all rule forms, mutated
target certificates and alpha/capture controls.

6,800 ambient assignment evaluations completed, of which 2,462
satisfy all premises; 4,338 are vacuous implications. All 12 malformed
proof checks reject. Two explicit truth flips establish that dropping
a quantifier guard changes meaning. The finite evaluators share
the syntax but use separate domain-handling implementations.
These are synthetic relational structures, not models of ZF.

Proof AST node totals: source 14,592; target 21,888 (1.50x).
JSON proof bytes: source 275,022; target 417,324 (about 1.52x).
Context bytes, shared subexpression compression, theorem library,
class definition, axiom proof obligations and wall time are excluded.
The compiler invokes the source checker during intermediate steps;
node counts are proof-tree sizes, not the total runtime work.
No efficiency or RH-scale expansion claim is supported.

Replay:
```sh
node research/ace/relativization.mjs > /tmp/ace03.json
diff -u research/ace/relativization_receipt.json /tmp/ace03.json
lake env lean MathCan/ACERelativization.lean
```
The JavaScript functions were executed in the authoring runtime before
serializing them to the committed Node file. Standalone Node replay
and the Lean kernel/axiom report have not been observed.

## ACE-03B gate: explicit set-theoretic proof interface

1. Add full first-order inference including equality substitution
   and classical logic, with an audited axiom-instance checker.
2. Encode ZF/ZFC with separation and replacement schemas and verify
   that the proposed class interpretation proves every required
   relativized axiom instance from the target theory. A declared
   premise cannot serve as its own certificate.
3. Define L and prove the needed class properties and arithmetic
   interpretation. Keep finite-formula satisfaction separate from
   any purported definable truth predicate for the whole universe.
4. Combine a proof-checked translation of each source derivation with
   the arithmetic isomorphism lemma in ACE-02 and the specific
   arithmetic encoding of the target statement.
5. Audit background strength of native Lean-to-set-theory translation
   independently; no bare ZF corollary follows from a native Lean
   proof without a suitable foundational interpretation.

No paid compute. No ZFC axiom instances have yet been discharged in
L, no object-level ZF derivation of RH has been produced.
