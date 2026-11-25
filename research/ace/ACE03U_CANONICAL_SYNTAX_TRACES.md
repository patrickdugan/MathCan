# ACE-03U | Canonical relation sets and syntax traces

Status, 2026-11-25: all 35 proof checks pass the unchanged executable ZF
kernel. They cover 34 new theorem statements and one reused graph lemma,
with 15,053 kernel visits, 35 independently reconstructed conclusions
and 93 rejection controls. The finite trace decoder passes a separate
semantic replay with 27 malformed-input or corruption controls.

The canonical order construction now specifies every member of its
relation set, which makes the set unique by Extensionality. A supplied
decoded program determines at most one semantic trace over any
transitive instruction domain. A separate finite induction theorem
assembles one witness per row from row-wise existential premises.
These results support the coding and recursion work needed for the
constructible well-order.

The report's checked results concern ambient ZF and the displayed
conditional interfaces. Uniform existence of syntax decorations for
every trace accepted by the pinned `Def`, natural-number coding,
the canonical transfinite order history and membership of its orders
in L remain open. The executable checker also retains its formal
soundness obligation.

## 1. A unique set for each canonical order predicate

ACE-03T constructs a set R whose ordered-pair values agree with the
induced order predicate. For use in a functional recursive definition,
the exported contract must determine the set itself.

The pinned value predicate is

\[
 \operatorname{Val}(R,x,y)
 \equiv \exists p\,(p\in R\land\operatorname{Pair}(p,x,y)),
\]

where `Pair` is the fixed Kuratowski-pair formula. This predicate
inspects the pair members of R. Adding an object which is not an
ordered pair preserves all of its values. In particular, the empty
set can be added in this way. Two finite fixtures in the replay
exhibit this behavior, with 52 coordinate comparisons in total.

The new contract is

\[
 \operatorname{Exact}_{\Phi}(R)
 \equiv
 \forall p\left[
  p\in R\ \longleftrightarrow
  \exists x\exists y\,
   \bigl(\operatorname{Pair}(p,x,y)\land\Phi(x,y)\bigr)
 \right].
\]

Both predicates instantiated in the replay include their output-carrier
guards. The first compares least definition codes from ACE-03T.
The second is the successor ordered sum, with the old stage preceding
newly added elements and its previous order preserved.

For x,y in the output carrier B, the Kuratowski pair lies in
\(\mathcal P(\mathcal P(B))\). Separation on this set constructs
\(\operatorname{Exact}_{\Phi}(R)\). If R and S both satisfy the exact
contract, every object belongs to R precisely when it belongs to S.
Extensionality then gives R=S. Pair existence and injectivity connect
the exact membership formula to global `Val` agreement.

The combined theorem yields a relation R with:

- exact membership and a unique set satisfying that membership formula;
- the strict well-order laws on B;
- global agreement between `Val(R,x,y)` and the chosen order predicate.

Each composed result retains its incoming hypotheses. The induced
order requires a well-ordered code carrier, functional evaluation
and coverage of the output carrier. The successor result requires
stage inclusion and both incoming orders. The relation constructor
is now functional as a set-valued operation under those premises.
Constructing its transfinite history requires further proof.

Sources: [generator](canonical_relation.mjs),
[independent replay](canonical_relation_replay.mjs),
[receipt](canonical_relation_receipt.json).

## 2. Supplied syntax determines its semantic trace

### The decoded syntax interface

The syntax is represented by five set parameters, one for each of the
fixed semantic operations:

| Field | Operand scope | Pinned semantic formula |
| --- | --- | --- |
| Equality | Both variable indices belong to n | `relEq` |
| Membership | Both variable indices belong to n | `relMem` |
| Negation | The earlier row belongs to k | `relNeg` |
| Intersection | Both earlier rows belong to k | `relAnd` |
| Existential projection | The earlier row belongs to k; the variable index belongs to n | `relEx` |

A binary instruction stores \(k\mapsto\langle i,j\rangle\).
Negation stores \(k\mapsto i\). The syntax formula requires every
field member to have this pair form with an in-domain row and scoped
operands. At every row, exactly one opcode and operand tuple is present.

`Trace(P,f,m,n,A)` states that f is the pinned exact graph on m and
that every row value obeys the semantic rule selected by P. A semantic
row is a set of assignments over A, represented with the unchanged
tuple and operation formulas from
[constructible_definition.mjs](constructible_definition.mjs).

The first bridge proves

\[
 \operatorname{Syntax}(P,m,n)\land
 \operatorname{Trace}(P,f,m,n,A)
 \ \longrightarrow
 \operatorname{validProgram}(f,m,n,A).
\]

The conclusion is the exact formula used by the pinned `Def`.
The replay rebuilds it independently. This implication and its
single-instruction helper both pass pure-logic checking.

### Uniqueness over an arbitrary transitive row domain

Let m be transitive, and suppose f and g both execute the same supplied
syntax P over A with width n. Each semantic operation specifies its
result by exact membership. Extensionality therefore proves that its
result is unique when its input relations and coordinates agree.

Separate the rows of m where the two traces disagree. If this set is
nonempty, Foundation supplies a row k with no earlier disagreeing row.
Transitivity of m keeps every earlier reference inside the domain.
The inputs at k consequently agree, so the operation's uniqueness
forces agreement at k as well. This contradicts its membership in the
set of disagreeing rows.

The checked conclusion is

\[
\begin{aligned}
 &\operatorname{Trans}(m)\land
  \operatorname{Syntax}(P,m,n)\land
  \operatorname{Trace}(P,f,m,n,A)\land
  \operatorname{Trace}(P,g,m,n,A)\\
 &\qquad\longrightarrow
 \forall k\in m\;\forall r\forall s\,
  \bigl(\operatorname{Val}(f,k,r)\land\operatorname{Val}(g,k,s)
    \longrightarrow r=s\bigr).
\end{aligned}
\]

The existing exact-graph extensionality lemma then yields f=g.
Slices at the same row, distinguished coordinate and base tuple
are equal by the pinned slice formula's own uniqueness theorem.

These statements have no numerical bound on program length. Their
assumptions include the syntax and the executing traces. Existence of
an execution for every well-formed syntax program remains a separate
theorem. The representation here consists of five sets; converting it
to a single natural-number code requires an additional construction.

Sources: [generator](syntax_trace_adequacy.mjs),
[independent replay](syntax_trace_adequacy_replay.mjs),
[receipt](syntax_trace_adequacy_receipt.json).

## 3. Assembling finitely many instruction witnesses

To recover syntax from a semantic trace, each row must supply an
instruction witness, and those witnesses must form one finite graph.
The new finite-selection theorem handles the graph step.

For a fixed first-order formula \(\Psi(i,c)\), with its displayed set
parameters, write

\[
 \operatorname{Total}_{\Psi}(m)
 \equiv \forall i\in m\;\exists c\;\Psi(i,c).
\]

The proof generator establishes

\[
\begin{aligned}
 \operatorname{Omega}(w)\land m\in w\land
 \operatorname{Total}_{\Psi}(m)
 \ \longrightarrow
 \exists g\bigl[\operatorname{Graph}(g,m)\land
   \forall i\in m\;\forall c\,
    (\operatorname{Val}(g,i,c)\longrightarrow\Psi(i,c))\bigr].
\end{aligned}
\]

`Omega` and `Graph` are the pinned formulas. The candidate relation can
offer several witnesses per row, and its witnesses can be arbitrary
sets. The final graph is exact, total on m and single-valued.

The empty set provides the base graph. At a successor, the proof opens
one existential witness for the new row and applies the existing
`graph_append_exists` proof. Separation forms the subset of w where
row-wise existence implies a selection graph. The least-inductive-set
clause of `Omega` puts every member of w in that subset.

The replay checks two fixed instances of the formula generator:

| Candidate formula | Parameters | Kernel visits across its four statements |
| --- | ---: | ---: |
| \(\operatorname{Val}(E,i,c)\) | E | 3,213 |
| \(\forall z\,(i\in z\rightarrow c\in z)\) | None | 3,197 |

The second formula contains an unbounded universal quantifier. In ZF
its relation is equivalent to c=i, using the singleton of i. The
measured replay covers these two formulas. The constructor accepts
other fixed formulas, subject to the existing syntax and schema
parameter checks; it does not add a quantified formula variable to
the object language.

The theorem supplies a graph for each finite m from its row-wise
existence premise. Infinite selection remains outside this conclusion.
For the `Def` application, local witnesses still need to be packed as
tagged instruction sets and decoded into the five-field interface.

Sources: [generator](finite_witness_selection.mjs),
[independent replay](finite_witness_selection_replay.mjs),
[receipt](finite_witness_selection_receipt.json).

## 4. Finite trace recovery and independent semantic checks

[trace_code_bridge.mjs](trace_code_bridge.mjs) supplies an executable
forward interpreter and a reverse decoder. A trace gives a Boolean
row for each instruction, indexed by assignments to all variable
coordinates. The decoder enumerates the permitted instructions at
each row and chooses the first whose semantics match that row.

The selection order is opcode followed by operand indices. This
defines a deterministic decoration of a semantic trace. Leastness
under the separate natural-number encoding of complete programs
remains outside its contract. Several different instructions can
produce the same row, so recovered syntax can differ from its source
program while preserving every intermediate relation.

The replay uses an independently written bitset evaluator. Its
assignment coordinates come from mixed-radix digits. A separate scalar
evaluator from ACE-03T then checks every prefix of the recovered
program against every assignment. This catches changes to an
intermediate row even when the last row remains unchanged.

| Finite check | Measured count |
| --- | ---: |
| Exhaustively enumerated raw traces | 4,469 |
| Valid traces accepted | 314 |
| Invalid traces rejected | 4,155 |
| Additional generated programs | 192 |
| Recovered rows checked | 2,489 |
| Scalar truth comparisons | 24,858 |
| Row occurrences with multiple admissible instructions | 1,906 |
| Source programs replaced by equivalent decorations | 177 |
| Full-base-tuple slice checks | 1,261 |
| Malformed-input or corruption controls | 27 |

Exhaustive enumeration covers traces of one through three rows for
the empty carrier at width one, the singleton carrier at width two,
and the two-element carrier at widths one and two. The additional
programs use seeds 109, 113 and 127 and exercise all five opcodes.

The implementation accepts at most eight distinct hereditarily finite
set codes, each between 0 and 31, with width between one and eight.
It also enforces a bound of 256 assignments and 64 rows. These bounds
belong to the executable fixture. The object-language theorems in the
preceding sections retain their quantified set domains.

An empty carrier has a unique empty assignment relation at each
positive width. Its raw semantic traces can therefore be recovered.
The finite slice API and the pinned `lastSlice` witness require a
full base tuple; none exists over that carrier at positive width.
The lower-level slice formula forces the output to be empty on an
empty carrier. The pinned `Def` also has its separate empty-set branch.

Sources: [finite replay](trace_code_bridge_replay.mjs),
[finite receipt](trace_code_bridge_receipt.json).

## 5. Verification ledger and reproduction

| Proof family | Checks | New statements | Reused helpers | Kernel visits | Rejection controls |
| --- | ---: | ---: | ---: | ---: | ---: |
| Canonical relation membership and uniqueness | 14 | 14 | 0 | 5,474 | 33 |
| Decoded syntax and semantic trace uniqueness | 13 | 12 | 1 | 3,169 | 34 |
| Finite witness selection | 8 | 8 | 0 | 6,410 | 26 |
| Total | 35 | 34 | 1 | 15,053 | 93 |

Each proof check has an independently rebuilt exact conclusion.
The reused helper is the 288-visit graph-extensionality proof from
ACE-03H. Imported lemmas are included as complete checked proof
trees. The visit total includes repeated visits when a later theorem
uses an earlier proof.

The canonical-relation replay also compares both order predicates
with ACE-03T's independent interfaces. The syntax replay checks five
formula interfaces and confirms the identity of its reused helper.
It checks two implication proofs in pure logic. Rejection controls
include omitted premises, out-of-scope formulas, altered semantic
extensions and an attempted source Choice import under ZF.

The set axioms appearing across the new proof trees are
Extensionality, Pairing, Union, Power Set, Separation and Foundation.
The finite-selection theorem receives its omega set as a premise.
All proofs run with the original ZF theory selector and the unchanged
[kernel](zf_interface.mjs).

Run the complete stage-U replay from the repository root:

```sh
node research/ace/ace03u_replay.mjs > /tmp/ace03u.json
diff -u research/ace/ace03u_receipt.json /tmp/ace03u.json
```

The combined runner executes all four family replays, compares each
output byte for byte with its pinned receipt, and verifies the proof
totals. Its receipt hashes the local static import closure, including
the existing generators, independent interfaces, kernel and pinned
L formula. The new CI job runs this same command and checks the
combined receipt.

The pinned L SHA-256 remains
`f6deb563af271469873b44118e8925b30394e1a21ec4c1e9fd8d103d1fdffdc0`.
The original source files listed in
[full_replay_provenance.json](full_replay_provenance.json) retain
their recorded bytes.

### Previously queued CI is complete

The previous head, `fb431eb23e88cf94eb4684e06843a9f396d75905`, passed
all 55 jobs in
[ACE run 45608847163](https://github.com/patrickdugan/MathCan/actions/runs/45608847163).
The full Separation and Replacement jobs reproduced their pinned
receipts, with 103,182 and 81,601 kernel visits respectively.
The five ACE-03T replays also passed.

[Mathematical checks run 45608847404](https://github.com/patrickdugan/MathCan/actions/runs/45608847404)
passed both its Lean and rational-oracle jobs. The tested pull-request
merge commit was `33e75ca8259ca52b07d53dd30380dfb1bdbd7d32`, combining
that head with main at `0082d2d6509278c1dfe888e8cede994d5cd836ca`.
Those runs used Node v22.23.5 for the JavaScript checks. Local stage-U
replay uses Node v24.22.3. CI for the stage-U commit has its own status
on the pull request.

## 6. The next proof connection

A direct next step packages each pinned `entry` witness as an
instruction set. With five distinct tag sets
\(\tau_0,\ldots,\tau_4\), use
\(\langle\tau_j,\langle i,l\rangle\rangle\) for binary
instructions and \(\langle\tau_2,i\rangle\) for negation.
Pair existence should give the local implication

\[
 \operatorname{entry}(f,k,r,n,A)
 \ \longrightarrow
 \exists c\;\operatorname{InstructionWitness}(c,\vec\tau,f,k,r,n,A).
\]

The candidate formula for finite assembly would then be

\[
 \Psi(k,c)\equiv\exists r\,
  \bigl(\operatorname{Val}(f,k,r)\land
   \operatorname{InstructionWitness}(c,\vec\tau,f,k,r,n,A)\bigr).
\]

The pinned `validProgram` condition supplies the row entries. The
surrounding `Def` witness also supplies `Omega(w)` and m in w, which
are required premises of finite selection. After checking the local
packing implication, instantiate that proof with this candidate
formula and the supplied finite-domain premises. Decoding the selected
graph into the five syntax fields would connect that existence
result to the trace-uniqueness theorem from this checkpoint.
These packing and decoding statements are proposed next steps.

The full Choice path additionally requires a natural code system with
proved adequacy for the pinned `Def`, existence and coherence of the
canonical transfinite order history, and a proof that its restricted
orders belong to L. The last import must match the source Choice
axiom's exact relativized disjoint-family and selected-set formula.
Unrestricted schema coverage and native Lean/RH translation retain
their open status.

Paid authoring compute: $0.
