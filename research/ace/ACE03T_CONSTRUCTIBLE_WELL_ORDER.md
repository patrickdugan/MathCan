# ACE-03T | Least definition codes and coherent constructible orders

Status: thirty-three object-language proof checks passed the unchanged
executable ZF kernel, with 8,113 kernel visits and thirty-three
independently reconstructed exact conclusions. These checks cover
thirty-one new theorem modules and two reused pair lemmas. They
establish least-code and successor relation sets, the source Choice
axiom's body under a carrier-order premise, and conditional transfer
to a limit order. A finite syntax-code implementation checks concrete
stage constructions. Uniform code adequacy, the canonical transfinite
history and membership of its orders in the pinned class L remain
proof obligations.

The local target is precise: a well-ordered set of codes with a
single-valued evaluation relation that reaches every member of a set
induces a well-order of that set by least codes. Applying this to the
pinned Def operation also requires a uniform bridge from finite
relation traces to syntactic program codes. A coherent order on all
constructible stages then requires an initial-segment invariant.

## 1. The local theorem

Work in ambient ZF. Let C and B be sets, let R strictly well-order C,
and let E(c,X) be a first-order evaluation relation. Assume

\[
 \forall X\in B\ \exists c\in C\ E(c,X)
\]

and

\[
 \forall c\in C\ \forall X,Y\
   ((E(c,X)\land E(c,Y))\longrightarrow X=Y).
\]

E may assign several codes to the same value. Define

\[
 \operatorname{Min}(c,X)\ \equiv\
 c\in C\land E(c,X)\land
 \forall d\in C\,(E(d,X)\longrightarrow\neg R(d,c)).
\]

For each X in B, Separation forms the fiber

\[
 F_X=\{c\in C:E(c,X)\}.
\]

Surjectivity makes this fiber nonempty. Its R-least member satisfies
Min. If c and d both satisfy Min for the same X, strict totality
leaves c=d: either strict comparison would contradict one of the
minimality clauses. Write this unique member as m(X).

The selector is injective. If m(X)=m(Y), the common code evaluates
to both values, and the functionality premise gives X=Y.

Define

\[
 X\triangleleft Y\ \equiv\
 X,Y\in B\land
 \exists c,d\,(\operatorname{Min}(c,X)\land
 \operatorname{Min}(d,Y)\land R(c,d)).
\]

This relation strictly well-orders B. Irreflexivity follows from
uniqueness of m(X). For transitivity, the two occurrences of the
middle value have the same code, so transitivity of R applies.
Distinct X and Y have distinct least codes; totality of R then gives
one strict comparison.

For the well-order clause, take a nonempty set S contained in B.
Separation on C gives

\[
 T=\{c\in C:\exists X\in S\ \operatorname{Min}(c,X)\}.
\]

Choose its R-least member c and an X in S with Min(c,X). For every
Y in S, its least code lies in T. Either m(Y)=c, in which case
functionality gives Y=X, or R(c,m(Y)). Thus X is the least member
of S under the induced order.

Both set constructions use Separation on a previously given set.
The proof obtains each selected value through a unique minimum.
Ambient Choice is absent from the argument. A set containing the
selector's graph can be formed separately by Separation on B times C.

### Exact scope for the object proof

The executable proof retains the well-order premise, code coverage,
and evaluation functionality as explicit antecedents. It instantiates
R(c,d) and E(c,X) with the pinned Kuratowski-pair graph predicate
Val(r,c,d) and Val(F,c,X). The displayed functionality premise covers
every ambient output of a code in C. Min includes the code-domain
guard; guards for X,Y in B appear in the induced order formula.

The conclusion applies to the pinned Def after those antecedents
have proofs for its intended code system. The local theorem verifies
the well-order laws of the induced formula. The relation-realization
proof below then constructs a set with exactly that binary relation
and transfers the well-order laws to it.

The proof of leastness quantifies over every set S contained in B.
Checking the three order laws alone would establish a strict linear
order and would leave this clause outstanding.

## 2. A code system for the pinned Def

The source of truth is
[constructible_definition.mjs](constructible_definition.mjs). Its
Def(A) uses positive finite widths and finite relation traces.
Each step asserts that one of the permitted operations produces the
next relation. Those traces contain semantic relations on A^n.

Introduce a syntax code e for a finite sequence of tagged instructions.
The code fixes a positive width n(e), a positive program length, and
the coordinate or predecessor indices of every instruction. Its
allowed instructions have the following meaning.

| Instruction | Data | Result |
| --- | --- | --- |
| Equality | Coordinates i,j below n | Assignments whose coordinates agree |
| Membership | Coordinates i,j below n | Assignments with coordinate i a member of coordinate j |
| Complement | Earlier step k | Complement of that relation in A^n |
| Intersection | Earlier steps k,l | Intersection of those relations |
| Existential projection | Earlier step k and coordinate i | Assignments agreeing off i with an accepted assignment |

A fixed injective encoding by natural numbers orders the syntax.
An object proof must establish the encoding's finite-sequence
properties inside ZF. Host-language strings and JavaScript array
indices provide a finite implementation of this syntax.

Given A, a valid e and a base tuple b in A^n(e), evaluate the
instructions in sequence, then take the final relation's slice at
coordinate zero using the remaining coordinates of b. Keeping the
entire base tuple agrees with the pinned definition; its unused
coordinate zero only gives extra codes for a value.

There is also one distinguished empty code, interpreted as the empty
set. The code set is the tagged disjoint union

\[
 C_A=\{\mathsf{empty}\}\ \sqcup\
 \coprod_{\substack{e\in\omega\\ e\ {\rm valid}}} A^{n(e)}.
\]

This gives a code for the empty subset when A is empty. In that case
every positive-width tuple fiber is empty, and the distinguished code
is the only code.

The finite implementation in
[well_order_codes.mjs](well_order_codes.mjs) stores only coordinates
1 through n-1 of b. For nonempty A, completing such a tuple with
the R-least member of A at coordinate zero gives the least full
base tuple with those remaining coordinates. Evaluation is independent
of that dummy coordinate. When A is empty, every resulting subset
is represented by the distinguished empty code. The finite validator
rejects program presentations on that empty stage, where completing
a positive-width base tuple would be impossible.
The implementation's least-code claim concerns the finite list of
presentations provided to it.

### The two adequacy directions

For a valid syntax code, induction on its finite instruction sequence
constructs a unique relation at every step. Extensionality gives
uniqueness; Separation on A^n provides the atomic relations,
complements and projections. Intersections use the already constructed
sets. The resulting relation trace satisfies the pinned validProgram
predicate. Its final slice therefore satisfies the pinned definable
predicate. The distinguished code uses that predicate's empty branch.

Conversely, take a witness to the pinned definable predicate. In its
nonempty branch, the witness contains a finite relation trace f with
domain m, a width n, and a base tuple b. At step k, entry(f,k,...) says
at least one allowed operation produces the witnessed relation.
Each tag has a finite collection of eligible coordinate and
predecessor indices. Order those finite instruction descriptions and
select the first one that produces the given relation. Replacement
over the finite domain m collects the uniquely specified instructions.
Their syntax code evaluates to the original trace, by finite
induction and Extensionality, and its slice is the original X.

These paragraphs are written ZF proofs of the proposed coding bridge.
The uniform object-language derivations are open. Their quantifiers
must cover every internally finite program accepted by the pinned
formula. Replaying a bounded sample of external programs establishes
the corresponding finite regression claim.

### Ordering the parameters

Suppose R strictly well-orders A. Put the empty code first. Compare
the remaining codes by natural-number syntax code e, then by the
lexicographic R-order on the fixed-width tuple b.

For a nonempty subset of A^n, a least tuple can be found by finite
induction: choose the least first coordinate that occurs, restrict to
that fiber, and take the least tail. For a nonempty subset of the
tagged sum, take the least syntax index with an occupied fiber and
then the least tuple in that fiber. Thus the code order is a
well-order, including when A is empty.

The tuple length must be fixed before lexicographic comparison.
Dictionary order across variable-length tuples has the descending
chain

\[
 (1)>(0,1)>(0,0,1)>(0,0,0,1)>\cdots
\]

over the well-order 0<1. The syntax-index-first construction avoids
that defect because each index fixes its width. Shortlex ordering,
with length compared first, is another construction that would need
its own exact specification.

## 3. Coherent successor stages

Let A=L_alpha, let B=Def(A)=L_(alpha+1), and assume R_alpha
well-orders A. Stage transitivity gives A contained in B.
Apply the local theorem to get the least-code order W_A on B.
Let N=B minus A be the set of fresh members. Define

\[
 R_{\alpha+1}
 =R_\alpha\ \cup\ (A\times N)\
   \cup\bigl(W_A\cap(N\times N)\bigr).
\]

This is the ordered sum of the old stage and the fresh members.
For a nonempty subset S of B, if S meets A, its R_alpha-least
member precedes every member of S in N. Otherwise S is contained
in N and its W_A-least member is least. The order laws follow
from the same two blocks.

The invariant is

\[
 R_{\alpha+1}\restriction(A\times A)=R_\alpha,
 \qquad
 x\in A,\ y\in B\setminus A\ \Longrightarrow\
 R_{\alpha+1}(x,y).
\]

Every old stage stays an initial segment. Once a pair has received
an order, later stages preserve it.

This successor rule is the construction stated in Justin Moore's
*MATH 6870: Set Theory*, Theorem 14.1, printed page 36. That theorem
also states the target order by a formula whose quantifiers range
over L. Proposition 13.2 gives the preceding definable-subset
well-order mechanism. See the
[author's notes](https://pi.math.cornell.edu/~justin/Limited2Cornell/lecture_notes.pdf).

Sorting all of B afresh by its current least codes does not carry
the invariant in its premises. For example, an old order a<b
can coexist with a new code enumeration 0 maps to b, 1 maps to a,
and 2 maps to a fresh c. The induced order b<a<c is a well-order,
but its restriction reverses the old pair. This finite example is
a regression against inferring coherence from the local theorem.

### Checked ordered-sum and initial-segment theorems

[successor_well_order.mjs](successor_well_order.mjs) implements the
ordered-sum argument in the original object calculus. Its inputs
are sets A,B,r,s with

\[
 A\subseteq B,\qquad
 \operatorname{WO}(A,r),\qquad
 \operatorname{WO}(B,s).
\]

Both r(x,y) and s(x,y) use the pinned set-coded relation predicate.
The output is the formula

\[
\begin{aligned}
 T(x,y)\ \equiv\ x,y\in B\ \land\bigl[
 & (x,y\in A\land r(x,y))\\
 {}\lor{}& (x\in A\land y\notin A)\\
 {}\lor{}& (x,y\notin A\land s(x,y))\bigr].
\end{aligned}
\]

Five modules prove irreflexivity, transitivity, totality, the
minimum clause and their combined well-order conclusion.
Separation forms the intersection of a test subset with A for the
minimum argument. Two additional modules prove

\[
 A\subseteq B\ \Longrightarrow\
 \forall x,y\in A\,(T(x,y)\leftrightarrow r(x,y))
\]

and

\[
 \forall x\in A\ \forall y\in B\
   (T(y,x)\longrightarrow y\in A).
\]

The downward-closure theorem follows from the displayed formula
without any well-order hypothesis.

The least-code module produces a well-order predicate, and the
successor theorem accepts a set-coded s. The relation-realization
proof below supplies the required set and establishes pointwise
equivalence. It also realizes the successor output T as a set
relation. These are ambient ZF constructions; membership of the
resulting relations in the pinned class L remains an obligation.

## 4. Limit stages

For a limit ordinal lambda, assume the previous orders form a
coherent chain of initial segments and set

\[
 L_\lambda=\bigcup_{\alpha<\lambda}L_\alpha,\qquad
 R_\lambda=\bigcup_{\alpha<\lambda}R_\alpha.
\]

Any finite collection of elements lies in one earlier stage.
Coherence therefore transfers the strict order laws to the union.

To prove well-ordering, take a nonempty subset S of L_lambda and
one element x in S. Pick alpha below lambda with x in L_alpha.
The set S intersect L_alpha has an R_alpha-least member m.
Any element of S lying outside L_alpha lies above every member
of L_alpha by the initial-segment invariant. Consequently m
is least in all of S.

Agreement on old pairs by itself would be too weak for this
argument. For each natural n, order the set n in reverse natural
order. Each order is finite and well-founded, and its restriction
to a smaller stage agrees with the earlier order. Their union
orders omega in reverse and gives every n a predecessor n+1.
The entire domain has no least member.

The limit proof uses the least-element definition of well-ordering.
It does not replace that definition by the absence of a countable
descending sequence, an equivalence that requires care in ZF.

Transfinite recursion on the deterministic successor rule and the
limit union now gives a written ambient construction. Its formal
instance must carry the initial-segment invariant through every
successor and limit. Given a constructible x, all its predecessors
then lie in a stage containing x. The global order is set-like.

### Checked transfer theorem for a given common relation

[coherent_well_order.mjs](coherent_well_order.mjs) proves the
limit mechanism in the original object calculus. Given sets B,H,r,
write r(x,y) for the pinned Val(r,x,y) predicate. Its premises are:

\[
 \forall x,y,z\in B\
   \exists a\in H\,(x\in a\land y\in a\land z\in a),
\]

\[
 \forall a\in H\,
   \bigl(a\subseteq B\land\operatorname{WO}(a,r)\bigr),
\]

and

\[
 \forall a\in H\ \forall x\in a\ \forall y\in B\
   (r(y,x)\longrightarrow y\in a).
\]

The conclusion is WO(B,r). Capturing any triple in a common
stage transfers transitivity; repeated variables give the
corresponding single-element and pairwise arguments. For the
minimum clause, Separation forms S intersect a. A predecessor
of its minimum belongs to a by downward closure, where local
minimality rules it out.

Five checked modules prove these order laws and their combined
conclusion. The hypotheses refer to a given set relation r and a
given family H. Applying them to a constructible limit still
requires constructing H and the union order r, identifying the
local restrictions, and proving the downward-closure premise.

## 5. Realizing order predicates as sets

[relation_realization.mjs](relation_realization.mjs) constructs
actual relation sets for the induced order and the successor
order. Each input formula Q(x,y) includes x,y in B as explicit
guards. Let P be the power set of B and let D be the power set
of P. Separation on D gives

\[
 t=\{p\in D:\exists x,y\in B\,
        (\operatorname{Pair}(p,x,y)\land Q(x,y))\}.
\]

The Kuratowski pair of x and y is
\(\{\{x\},\{x,y\}\}\). When x,y belong to B, its two members
are subsets of B, so the pair belongs to D. A checked double-power
bound makes this argument available to the construction. Pair
existence and pair injectivity come from existing object-language
proofs, which are replayed as dependencies.

For all ambient x and y, the resulting set satisfies

\[
 \operatorname{Val}(t,x,y)\ \longleftrightarrow\ Q(x,y).
\]

The forward implication uses pair injectivity to identify any
witnessed endpoints with the endpoints used by Separation.
For the converse, the explicit domain guards allow the pair-bound
theorem to place the required pair in D.

A separate checked transport theorem transfers every well-order
clause across this pointwise equivalence. Combining that theorem
with the original least-code conclusion proves, under its exact
code-order, functionality and coverage premises, the existence of
a set-coded induced well-order. Applying the same construction
to the ordered sum gives a set-coded successor well-order under
its exact inclusion and incoming-order premises.

The Separation construction contains pairs only. The exported
existence theorem records pointwise agreement and well-ordering.
A later proof of canonical recursion must use the full defining
membership condition to establish uniqueness of each stage relation
and of its history.

## 6. The internal Choice gate

An ambient order on constructible elements supplies mathematical
structure. A relativized Choice import additionally needs the
selected function to satisfy the pinned predicate L.

One sufficient route is to prove a parameter-free formula
Theta(x,y) defining the canonical order with a checked internal
interpretation in L. For every relevant constructible domain a,
the required instance of Separation in L must then construct the
set relation

\[
 r_a=\{(x,y)\in a\times a:\Theta(x,y)\}
\]

inside L and identify it with the ambient restriction. Uniform
coding adequacy and absoluteness of the recursive order history
are obligations of that identification. A concrete stage bound for
the code histories and the restricted relation would also discharge
the membership requirement if supplied by a checked construction.

The internal well-order-to-Choice step can be stated without the
global order formula. Let F be a constructible family of nonempty
sets, let U be its union, and suppose a strict well-order r of U
belongs to L. Define

\[
 f=\{(X,x)\in F\times U:
       x\in X\ \land\
       \forall y\in X\,\neg r(y,x)\}.
\]

The least-element property gives exactly one value x for every
X in F. Pair and product closure supply the ambient domain of
the graph in L; the exact internal Separation instance places f
in L. Transitivity identifies the members of X with the elements
over which the relativized formula quantifies. It follows that
f is a choice function in L. For the empty family, the empty
graph is the required function.

This conditional argument exposes every dependency needed by the
import: constructible set operations, an internal well-order on U,
and the exact graph-Separation instance. Applying ambient Separation
to the same displayed predicate only proves that f exists in the
ambient universe.

### The source axiom's exact choice-set form

The fixed Choice axiom in
[zf_interface.mjs](zf_interface.mjs) uses a set that meets each
member of a pairwise disjoint nonempty family exactly once.
For a family F of that form, let U contain every member of every
X in F, and suppose r well-orders U. The direct construction is

\[
 C=\{x\in U:\exists X\in F\,
       (x\in X\land\forall y\in X\,\neg r(y,x))\}.
\]

For every X in F, its least member belongs to X intersect C.
If y belongs to that intersection, it is least in some Y in F.
Since y belongs to both X and Y, pairwise disjointness gives X=Y.
Uniqueness of the least member then makes X intersect C a
singleton. Separation on U supplies the ambient set C.

The checked choice_from_carrier_well_order theorem derives this
exact source conclusion from the displayed carrier and family
premises. The replay compares both the family antecedent and the
selection conclusion with the original Choice schema. The
relativized import still needs C in L and all corresponding
quantifier guards. The covering-carrier well-order remains an
explicit premise until the constructible order provides it.

The standard end theorem is the relativized Choice theorem of
constructibility. Its historical source is Kurt Godel,
[*The Consistency of the Axiom of Choice and of the Generalized
Continuum-Hypothesis*](https://pmc.ncbi.nlm.nih.gov/articles/PMC1077160/),
PNAS 24 (1938), 556-557, doi:10.1073/pnas.24.12.556.
This report follows that target while keeping the repository's
remaining object-proof obligations explicit.

## 7. Verification ledger

The measured local modules are in
[constructible_well_order.mjs](constructible_well_order.mjs).
An independent de Bruijn interface builder in
[constructible_well_order_replay.mjs](constructible_well_order_replay.mjs)
checks their exact conclusions before the original kernel runs.

| Kernel module | Visits | Principal premise or conclusion |
| --- | ---: | --- |
| least_code_total | 60 | Well-order and coverage yield a least code |
| least_code_unique | 52 | Code trichotomy yields uniqueness |
| least_code_injective | 25 | Functional evaluation gives injectivity |
| induced_irreflexive | 101 | Least-code order is irreflexive |
| induced_transitive | 142 | Least-code order is transitive |
| induced_total | 84 | Functional evaluation and least-code coverage give totality |
| induced_minima | 169 | Every nonempty subset has a minimal member |
| induced_well_order | 606 | Combines the exact conditional well-order conclusion |
| well_order_minimum_unique | 46 | A subset of a well-ordered carrier has at most one minimum |
| choice_from_carrier_well_order | 150 | Covered disjoint nonempty families have a choice set |
| Total | 1,435 | Ten modules |

Three ambient Separation schema instances occur in these proof objects.
The replay passes 21 rejection controls, including removal of the
carrier, well-order, nonemptiness and disjointness premises from the
exact Choice target. It also checks scope rejection and disables
Separation to reject the theorems that require it. ZF rejects a direct
source Choice axiom. These checks exercise the executable checker;
its formal semantic soundness proof remains open.

The independent replay
[successor_well_order_replay.mjs](successor_well_order_replay.mjs)
checks the successor step:

| Kernel module | Visits | Conclusion |
| --- | ---: | --- |
| successor_irreflexive | 42 | Ordered-sum irreflexivity |
| successor_transitive | 166 | Ordered-sum transitivity |
| successor_total | 144 | Ordered-sum totality |
| successor_minima | 144 | Least members of every nonempty subset |
| successor_well_order | 546 | Exact conditional ordered-sum well-order |
| successor_restriction | 46 | Old-stage restriction equals the old relation |
| successor_initial_segment | 25 | Downward closure of the old stage |
| Total | 1,113 | Seven modules |

This replay checks seven independently reconstructed exact goals,
two formula interfaces and fourteen rejection controls. One
Separation instance forms the intersection with the old stage.

The independent replay
[coherent_well_order_replay.mjs](coherent_well_order_replay.mjs)
adds the following measured modules:

| Kernel module | Visits | Conclusion |
| --- | ---: | --- |
| directed_irreflexive | 36 | Irreflexivity on the covered domain |
| directed_transitive | 54 | Transitivity from common-stage capture |
| directed_total | 40 | Totality from common-stage capture |
| initial_segment_minima | 111 | Global minima from local minima and downward closure |
| directed_initial_segment_well_order | 280 | Exact conditional well-order transfer |
| Total | 521 | Five modules |

This replay checks five independently reconstructed exact goals,
four formula interfaces and ten rejection controls. Its proof
objects use one Separation instance for the stage intersection.

Finally,
[relation_realization_replay.mjs](relation_realization_replay.mjs)
checks actual ambient relation sets and composes them with the
preceding order theorems:

| Kernel module | Visits | Role |
| --- | ---: | --- |
| ordered_pair_exists | 45 | Reused ACE-03F pair-existence proof |
| ordered_pair_injective | 206 | Reused ACE-03F pair-injectivity proof |
| ordered_pair_double_power_bound | 77 | Bounds pairs in the power set of the power set of B |
| induced.exact_relation_realization | 441 | Set relation agreeing globally with the induced predicate |
| induced.well_order_agreement_transfer | 131 | Transfers the induced predicate's well-order laws |
| induced.well_order_set_realization | 594 | Produces an agreeing set-coded well-order |
| induced.composed_well_order_realization | 1,222 | Combines realization with code-order, functionality and coverage premises |
| successor.exact_relation_realization | 441 | Set relation agreeing globally with the ordered-sum predicate |
| successor.well_order_agreement_transfer | 131 | Transfers the successor predicate's well-order laws |
| successor.well_order_set_realization | 594 | Produces an agreeing set-coded successor well-order |
| successor.composed_well_order_realization | 1,162 | Combines realization with inclusion and both incoming-order premises |
| Total | 5,044 | Nine new modules and two reused pair lemmas |

This replay checks eleven independently reconstructed exact goals,
two order-predicate interfaces, three shared-helper identities and
27 rejection controls. The set constructions use Pairing, Power Set
and Separation. The composed conclusions retain every premise of
their source order theorem.

Across all four proof replay families, the totals are 33 proof
checks, comprising 31 new theorem modules and two reused pair lemmas,
with 8,113 kernel visits and 72 rejection controls.

The finite replay,
[well_order_codes_replay.mjs](well_order_codes_replay.mjs), passed:

| Finite regression | Measured coverage |
| --- | ---: |
| Syntax program encode/decode round trips | 548 |
| Independent assignment-truth comparisons | 33,804 |
| Presented definition codes across four stage fixtures | 9,862 |
| Distinct selected subsets across those fixtures | 23 |
| Exhaustive nonempty-subset minimum and selection checks | 65,554 |
| Orders of the four-element incoming stage | 24 |
| Rejection controls | 44 |

The coherent finite chain has stage sizes 0, 1, 2, 4 and 16.
The replay also checks explicit finite prefixes of the reverse-order
and variable-width-lex counterexamples described above. The
mathematical infinite counterexamples follow from their displayed
formulas. A finite prefix alone is only a regression.

| Component | Required evidence | Status |
| --- | --- | --- |
| Generic least-code theorem and conditional Choice bridge | Original executable kernel checks closed conditional theorems and rejection controls | Ten modules passed |
| Finite code evaluator | Independent expected slices, code validity and duplicate-definition tests | Finite replay passed |
| Conditional successor and coherence | Original kernel proves ordered-sum well-order, restriction and initial-segment conclusions | Seven modules passed |
| Ambient relation-set realization | Construct induced and successor relation sets, establish exact agreement and transfer well-ordering | Eleven proof checks passed, including two reused pair lemmas |
| Limit premise audit | Reverse-finite-order counterexample to coherence alone | Written proof above |
| Conditional limit transfer | Original kernel proves well-ordering from triple capture, local well-orders and downward closure | Five modules passed |
| Pinned Def coding bridge | Uniform object-language syntax encoding and both adequacy directions | Open |
| Transfinite canonical order | Prove unique stage-order histories, construct their union and supply the checked transfer premises | Open |
| Internal constructibility | Checked L-membership of restricted orders, or adequate absolute definition and internal Separation | Open |
| Exact relativized Choice | Checked choice-set existence in L and source-axiom import | Open |

Full schema coverage, semantic soundness of the executable proof
checker, and native Lean/RH translation retain their existing
status from the ACE-03S checkpoint. The local theorem does not
discharge those obligations.
