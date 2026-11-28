# ACE-03W | Least-code well-order of the pinned Def operation

Status, 2026-11-25: the unchanged executable ZF kernel accepts the complete
least-code construction for the pinned Def operation. Ten independent
family replays passed, covering 118 proof checks, 376,400 kernel visits,
and 382 rejection controls. The per-commit CI job checks the complete
aggregate execution against its pinned expected receipt.

## 1. The composed theorem

Write `WO(A,R)` for the existing four-clause strict well-order formula,
interpreting comparisons through the pinned Kuratowski-pair `Val(R,x,y)`.
The final construction starts from a supplied well-order of an arbitrary
set A and produces an actual order set for its exact definable
successor:

\[
\forall A\,\forall R\;\left[
 \operatorname{WO}(A,R)\longrightarrow
 \exists B\,\exists S\;
 \bigl(\operatorname{Def}(A,B)\land\operatorname{WO}(B,S)\bigr)
\right].
\]

`Def` here is the unchanged formula used by the pinned definition of L.
The construction also composes with the existing successor-order theorem.
For a transitive A, the resulting order on B agrees with R on A and makes
A an initial segment:

\[
\begin{aligned}
 &\operatorname{Def}(A,B)\land\operatorname{Trans}(A)
   \land\operatorname{WO}(A,R)\\
 &\quad\longrightarrow\exists T\;
 \left[\operatorname{WO}(B,T)\land
 \left.\operatorname{Val}(T)\right|_{A\times A}
   =\left.\operatorname{Val}(R)\right|_{A\times A}
 \land \operatorname{Initial}(A,B,T)\right].
\end{aligned}
\]

The initial-segment clause says that if x belongs to A, y belongs to B,
and y precedes x under T, then y belongs to A. Agreement concerns the
binary relations interpreted by `Val`, so it applies to every supplied
R satisfying the stated well-order formula.

Both statements concern ambient sets in ZF. A coherent transfinite
history of these orders and membership of the required order sets in L
remain separate proof obligations.

## 2. Ordering every finite tuple length

The first proof family derives a membership well-order for a supplied
set w satisfying the exact `Omega(w)` formula. Its least-inductive-set
clause supplies induction. The proof establishes transitivity of w and
its members, the zero-or-successor decomposition, and comparison of its
members. Foundation supplies minima for nonempty subsets. The finite
induction generator is checked through two concrete instances.

For an alphabet A with supplied order R, tuples are the exact set-coded
graphs from the pinned definition. At a fixed length n, two tuples are
compared at their first differing position. The proof proceeds by
induction on n. A successor tuple is represented by its exact prefix
and final value. Restricting its graph constructs the prefix, while
graph extensionality proves that this representation determines the
whole tuple.

A general lexicographic pullback theorem handles this successor step.
It takes well-orders on two component carriers, together with coverage,
coordinate functionality, and joint injectivity of the representation.
Its minima proof first minimizes the represented first coordinate, then
minimizes the second coordinate within that fibre.

The induction proves a well-order for every supplied set of tuples of
length n. Shortlex then compares all finite lengths:

\[
 f<_{\mathrm{sl}}g
 \quad\Longleftrightarrow\quad
 \ell(f)\in\ell(g)
 \ \lor\
 \bigl(\ell(f)=\ell(g)\land f<_{\mathrm{lex}}g\bigr).
\]

This notation abbreviates existential witnesses for the two exact
graph domains. A separate graph-domain uniqueness proof ensures that
the lengths agree whenever the same tuple has two such presentations.
For a nonempty set of finite tuples, the minima proof chooses its least
realized length and then the least tuple in the separated fibre at that
length. Every fibre's well-order comes from the discharged induction.

## 3. Actual carriers and actual relation sets

Define

\[
 \operatorname{Seq}(w,A)
 =\{g:\exists m\in w\;\operatorname{Tuple}(g,m,A)\}.
\]

The exact carrier exists for arbitrary w and A. To construct it, take

\[
 U=(\bigcup w)\cup A.
\]

If m belongs to w, each index of a tuple on m lies in the union of w.
Each tuple value lies in A. Kuratowski graph entries therefore belong
to the double power set of U, and the graph itself belongs to the
triple power set. Separation within that bound constructs exactly
`Seq(w,A)`. Extensionality proves uniqueness of the carrier.

Given `Omega(w)` and `WO(A,R)`, the shortlex theorem gives its order.
The canonical relation construction realizes that predicate as a set
with exact pair membership. It also proves agreement with `Val` and
uniqueness of the resulting relation set.

Cartesian products receive the same treatment. The proof constructs
`A × B` inside the double power set of `A ∪ B`, proves exact membership,
and discharges the representation premises of the lexicographic
pullback theorem. Two supplied component orders yield an actual
lexicographic relation set on the product.

## 4. Normalized instructions and complete descriptions

The instruction alphabet is the actual well-ordered set

\[
 I=w\times(w\times w).
\]

An instruction is stored as

\[
 \langle t_{\mathrm{op}},\langle i,j\rangle\rangle.
\]

Negation uses the repeated operand pair \(\langle i,i\rangle\).
The five tags are the empty set followed by four successors. Their
existence inside w, distinctness, and componentwise uniqueness are
proved from `Omega(w)` and the exact successor formulas.

For the five syntax-field sets P and shared tags t, `Encodes` states
that g is the exact graph on m and that each row agrees in both
directions with the normalized instruction predicate:

\[
 \operatorname{Encodes}(g,m,P,t)
 \equiv \operatorname{Graph}(g,m)\land
 \forall k\in m\;\forall c\;
 \bigl(\operatorname{Val}(g,k,c)
       \leftrightarrow\operatorname{Row}(P,t,k,c)\bigr).
\]

Under `Omega(w)`, n,m in w, and membership of the shared tags in w,
the finite selector constructs g for every supplied syntax program.
The syntax bounds place all its values in I. Conversely, a shared g,
shared distinct tags, and the exact syntax premises determine every
member of each of the five field sets, proving equality of the fields.

A complete raw description records the variable width n, the
instruction graph g, and the parameter tuple b:

\[
 d=\langle n,\langle g,b\rangle\rangle.
\]

Its carrier is

\[
 C=w\times\bigl(\operatorname{Seq}(w,I)
                   \times\operatorname{Seq}(w,A)\bigr).
\]

Two product constructions give this exact carrier and its actual
well-order. The raw carrier allows arbitrary finite lengths for g and
b. Evaluation imposes the required program length and the condition
that b has length n. The syntax-to-description theorem retains the
specific supplied b throughout the packing step.

These descriptions use finite set-coded graphs over an explicitly
well-ordered alphabet. The least-code theorem accepts this carrier
directly; an additional encoding by one natural number can be studied
separately.

## 5. Exact evaluation and the empty branch

Positive evaluation parses d into n, g and b. It requires positive
finite width and program length, `Tuple(b,n,A)`, compatible syntax
fields P, exact `Encodes(g,m,P,t)`, and a semantic trace f of P.

The last-row condition retains the same encoded b:

\[
\begin{aligned}
 \operatorname{LastAtBase}(f,m,n,A,b,X)
 \equiv\exists k\in m\;[&\operatorname{Succ}(k,m)\land\\
 &\exists r\;(\operatorname{Val}(f,k,r)\land
   \exists z\in n\;[\operatorname{Empty}(z)\land
           \operatorname{slice}(X,r,A,n,z,b)])].
\end{aligned}
\]

The replay checks the exact transport

\[
 \operatorname{lastSlice}(f,m,n,A,X)
 \quad\Longleftrightarrow\quad
 \exists b\;[\operatorname{Tuple}(b,n,A)\land
              \operatorname{LastAtBase}(f,m,n,A,b,X)].
\]

The forward direction extracts the original base-tuple witness, which
the description then retains. For two
positive evaluations of the same description, pair injectivity fixes
n, g and b. Graph-domain uniqueness fixes the program length; exact
encoding then identifies all syntax fields. The existing trace and
slice uniqueness proofs identify the output sets.

The pinned `definable` formula includes an explicit empty-output
branch. A reserved description represents it:

\[
 d_0=\langle 0,\langle\varnothing,\varnothing\rangle\rangle.
\]

Empty tuple graphs place this description in C even when A is empty.
Positive evaluation requires nonempty width, which makes its codes
disjoint from the reserved zero-width code. Full evaluation is the
disjunction of the reserved empty-output branch and positive
evaluation.

The resulting checked statement is the exact equivalence

\[
 \operatorname{definable}(A,X)
 \quad\Longleftrightarrow\quad
 \exists d\in C\;\operatorname{Evaluation}(d,X;A,w,t).
\]

Its premises are the supplied omega set, the shared canonical tag
bank, the exact triple alphabet, and the exact raw carrier. Omega
uniqueness reconciles any omega witness inside the pinned definition
with the supplied w. The proof also establishes functionality of
`Evaluation` under the supplied omega and distinct-tag premises.

Evaluation may be undefined on descriptions outside its valid domain.
The least-code construction requires a functional relation whose
outputs cover the target carrier. These two properties are proved
for the exact evaluation relation here.

## 6. Least codes and the successor order

For a set B satisfying `Def(A,B)`, Separation on `C × B` constructs
an evaluation relation F with exact pair membership. Its `Val`
interpretation satisfies

\[
 \operatorname{Val}(F,d,X)
 \quad\Longleftrightarrow\quad
 d\in C\land X\in B\land\operatorname{Evaluation}(d,X).
\]

The preceding functionality and coverage theorems discharge the two
evaluation premises of ACE-03T's least-code theorem. Every X in B has
a least defining description, and distinct outputs have distinct
least descriptions. Comparing those descriptions well-orders B.
The canonical relation theorem constructs an actual set for that
order, with exact membership and uniqueness for its defining
predicate.

The final stage theorem discharges the actual Def-set existence and
omega existence proofs. For transitive A, the existing inflation
theorem gives `A ⊆ B`. The successor-order construction puts every
member of A before every new member of B, retains A's supplied order,
and uses the constructed order among the new members. The composed
proof yields agreement on A and the initial-segment property.

## 7. Verification ledger

| Proof family | Checks | Kernel visits | Rejection controls |
| --- | ---: | ---: | ---: |
| Omega and membership order | 16 | 3,309 | 44 |
| Lexicographic pullback | 5 | 1,585 | 22 |
| Exact pair products and their orders | 8 | 6,240 | 28 |
| Natural relation and triple alphabet | 5 | 9,202 | 21 |
| Finite tuple induction and shortlex | 20 | 26,874 | 59 |
| Exact sequence carriers and relations | 15 | 24,692 | 34 |
| Normalized instructions and canonical tags | 17 | 20,457 | 49 |
| Complete description carrier | 8 | 35,760 | 43 |
| Functional evaluation and exact definability | 15 | 74,366 | 36 |
| Least-code Def order and end-extension | 9 | 173,915 | 46 |
| **Total** | **118** | **376,400** | **382** |

The checks cover 117 new theorem statements and one independently
reproved existing tuple-range statement. Every conclusion has an
independent formula reconstruction. The replays also compare 82 formula
interfaces, check 24 proofs in pure logic, and compare the exact pinned
Def schema expansion in the final family.

The rejection total includes kernel rejection runs and comparisons of
changed contracts with retained, verified kernel conclusions. Actual
proof mutations return to the kernel. The controls include loss of the
encoded base tuple, omitted carrier and order premises, changed live
axiom instances, reversed Def arguments, and reversal of the
initial-segment condition.

The axiom audit records Extensionality, Foundation, Infinity, Pairing,
Power Set, Separation and Union across the complete new proof families.
It checks that the Choice axiom is absent from every accepted proof.
The original kernel and pinned L formula retain their previous bytes.

The aggregate runner compares all ten complete family receipts. It
verifies 75 earlier source-hash comparisons across 58 distinct files
and ten earlier receipt hashes. The current static import graph and
source hashes bind the receipt to the complete dependency chain, with
input hashes checked again after execution.

Each family runs sequentially in a separate process with a 3,072 MiB
heap limit. Nine families have a 300-second limit; the final composed
stage family has a 600-second limit. Its independent run completed in
220.057 seconds. The new `definable-stage-order-replay` CI job uses
Node 22 and a 20-minute job budget.

All ten family receipts came from successful independent runs. A later
local aggregate reproduced the first eight receipts before its evaluation
child was externally terminated. Monitored diagnostic attempts also ended
with SIGKILL. The aggregate's expected output was prepared from the
verified family receipts and the source/hash checks. The committed runner
executes every family and compares its output, making the per-commit CI
job the complete aggregate execution gate.

The preceding ACE-03V head passed
all 57 ACE jobs and both mathematical checks:
[ACE run 45642220528](https://github.com/patrickdugan/MathCan/actions/runs/45642220528)
and [mathematical checks run 45642222138](https://github.com/patrickdugan/MathCan/actions/runs/45642222138).

Replay from the repository root:

```sh
node research/ace/ace03w_replay.mjs > /tmp/ace03w.json
diff -u research/ace/ace03w_receipt.json /tmp/ace03w.json
```

Sources:

- [Omega order](omega_well_order.mjs)
- [Lexicographic pullback](lexicographic_pullback.mjs)
- [Exact pair products](pair_product_order.mjs)
- [Natural instruction alphabet](natural_code_order.mjs)
- [Finite tuple and shortlex order](finite_sequence_order.mjs)
- [Exact sequence carriers](finite_sequence_carrier.mjs)
- [Normalized syntax codes](syntax_instruction_codes.mjs)
- [Complete description carrier](description_carrier.mjs)
- [Exact evaluation](description_evaluation.mjs)
- [Composed Def-stage order](definable_stage_order.mjs)
- [Combined replay](ace03w_replay.mjs)
- [Combined receipt](ace03w_receipt.json)

## 8. Remaining constructible-universe work

The checked successor construction provides ambient set orders from
supplied previous orders. Transfinite recursion must still construct
a uniform coherent history and verify the hypotheses of the previously
checked conditional limit-transfer theorem. The proof also needs to
place the relevant restricted orders and the resulting selections inside the pinned
constructible class before importing the exact relativized Choice
axiom.

The executable checker has passed the recorded proof replays and
rejection controls. A formal soundness proof for that checker remains
open. The earlier Replacement schema coverage limits remain as recorded
in ACE-03S.

Paid authoring compute: $0.
