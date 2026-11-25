# ACE-03V | Finite trace decoration and exact Def equivalence

Status, 2026-11-25: the unchanged executable ZF kernel accepts the complete
finite trace-to-syntax construction and its composition with the pinned
`definable` and `Def` formulas. The checkpoint contains 32 proof checks,
covering 31 new statements and one independently reproved existing
statement, with 87,128 kernel visits and 89 rejection controls.

For every supplied finite valid semantic trace, the proof constructs five
instruction-field sets satisfying the exact syntax and execution formulas
from ACE-03U. The same construction works over arbitrary set carriers A.
It has no fixed program-length or carrier-size limit.

The main new equivalence replaces a finite semantic trace's `validProgram`
condition with the existence of a compatible decoded syntax description.
Lifting that equivalence through the original definition preserves every
outer witness and the exact `lastSlice` formula. The pinned definition of
L retains its original bytes.

The representation consists of five set-coded instruction fields.
Encoding them by a single natural number and proving total execution for
arbitrary supplied syntax remain further proof obligations. The later
constructible-order work also needs a coherent transfinite history and
membership of its restricted orders in L before the exact Choice import.
Formal soundness of the executable checker remains open.

## 1. The finite decoration theorem

Write P for the ordered list of five syntax fields. `Syntax(P,m,n)` is
the exact ACE-03U formula: all field members have the required pair form,
their operands have the required bounds, and each row has one opcode
and operand tuple. `Trace(P,f,m,n,A)` says that f is the pinned exact
graph on m and every row follows its selected semantic instruction.

The composed theorem proves

\[
\begin{aligned}
 &\operatorname{Omega}(w)\land m\in w\land
  \operatorname{validProgram}(f,m,n,A)\\
 &\qquad\longrightarrow
  \exists P\,
  \bigl(\operatorname{Syntax}(P,m,n)\land
        \operatorname{Trace}(P,f,m,n,A)\bigr).
\end{aligned}
\]

The existential over P expands to five nested set quantifiers. Every
tag, selected instruction graph and field set used by the proof is
constructed and discharged before this conclusion. Its remaining
premises are precisely the supplied omega set, m in that set, and the
original valid trace.

The width n can be any set in this theorem. The outer pinned `Def`
witness supplies its stronger condition n in w, together with the
nonempty-width condition. A zero-length trace is also covered by the
decoration theorem; the later `Def` application retains its original
nonempty-length condition.

ACE-03U already proves the reverse implication from `Syntax` and `Trace`
to `validProgram`. Under the supplied `Omega(w)` and m in w premises,
their composition gives

\[
\begin{aligned}
 \operatorname{validProgram}(f,m,n,A)
 \ \longleftrightarrow
 \exists P\,
   \bigl(\operatorname{Syntax}(P,m,n)\land
         \operatorname{Trace}(P,f,m,n,A)\bigr).
\end{aligned}
\]

Compatible syntax can have several descriptions. The theorem constructs
one such description. The earlier trace-uniqueness theorem applies when
two executions share a supplied syntax program.

Sources: [composed proofs](syntax_decoration.mjs),
[independent replay](syntax_decoration_replay.mjs),
[receipt](syntax_decoration_receipt.json).

## 2. Obtaining five distinct instruction tags

The proof starts with the supplied `Omega(w)`. Its inductive-set clause
provides an empty member and four successive members. Write these as
\(t_0,\ldots,t_4\). The successor characterizations give

\[
 t_i\in t_j\qquad(i<j).
\]

If \(t_i=t_j\), this membership becomes \(t_i\in t_i\), contradicting
the existing Foundation-based no-self-membership theorem. The exported
tag theorem yields all ten inequalities and the membership of every
tag in w:

\[
 \operatorname{Omega}(w)\longrightarrow
 \exists t_0\cdots\exists t_4\,
 \left[
   \bigwedge_{i<5}t_i\in w\ \land
   \bigwedge_{i<j<5}t_i\ne t_j
 \right].
\]

The proof uses the already supplied omega set's base and successor
closure. Pairing and Foundation occur through the existing
no-self-membership helper. The two checked tag statements require
693 kernel visits and pass nine rejection controls.

Sources: [tag proofs](instruction_tags.mjs),
[replay](instruction_tags_replay.mjs),
[receipt](instruction_tags_receipt.json).

## 3. Packing semantic entries and selecting instructions

### Local instruction witnesses

The five branches of the pinned `entry(f,k,r,n,A)` formula provide an
opcode, bounded operands and the corresponding semantic clause.
A binary instruction is stored as

\[
 c=\langle t_{\mathrm{op}},\langle i,j\rangle\rangle,
\]

and negation is stored as \(c=\langle t_2,i\rangle\).
Pair existence constructs these sets. Each witness retains its original
operand bounds and semantic clause:

| Operation | Operand bounds | Retained semantic clause |
| --- | --- | --- |
| Equality | i,j in n | `relEq(r,n,A,i,j)` |
| Membership | i,j in n | `relMem(r,n,A,i,j)` |
| Negation | i in k | An earlier value p and `relNeg(r,p,n,A)` |
| Intersection | i,j in k | Earlier values p,q and `relAnd(r,p,q)` |
| Existential projection | i in k and j in n | An earlier value p and `relEx(r,p,n,A,j)` |

The local proof establishes

\[
 \operatorname{entry}(f,k,r,n,A)
 \longrightarrow
 \exists c\;\operatorname{Witness}(c,f,k,r,n,A,\vec t).
\]

A separate checked implication recovers the exact pinned `entry`
formula from a tagged witness. Packing works for arbitrary supplied
tags; distinctness is used when decoding identifies the opcode.

### Finite witness assembly

Define the candidate relation

\[
 \Psi(k,c)\equiv
 \exists r\,
 \bigl(\operatorname{Val}(f,k,r)\land
       \operatorname{Witness}(c,f,k,r,n,A,\vec t)\bigr).
\]

The pinned `validProgram` premise supplies an entry at every row of m.
The local packing theorem therefore gives
\(\forall k\in m\,\exists c\,\Psi(k,c)\).

The ACE-03U finite-selection generator is instantiated with this exact
eight-parameter candidate formula. The parameters are f, n, A and the
five tags. Its proof yields a graph g which chooses a witness at every
row. `Tagged(g,f,m,n,A,vec t)` states that g is the pinned exact graph
on m and that every selected value satisfies the candidate formula.

The complete assembly theorem is

\[
\begin{aligned}
 &\operatorname{Omega}(w)\land m\in w\land
   \operatorname{validProgram}(f,m,n,A)\\
 &\qquad\longrightarrow
   \exists g\;\operatorname{Tagged}(g,f,m,n,A,\vec t).
\end{aligned}
\]

Finite induction supplies the selection. Its new Separation instance
has eight parameters and contains the full instruction-witness formula.
All nine statements in this family pass, with 6,070 kernel visits and
26 rejection controls. The reverse local witness implication and the
empty selection case also pass pure-logic checking.

Sources: [packing and selection proofs](instruction_witnesses.mjs),
[independent replay](instruction_witnesses_replay.mjs),
[receipt](instruction_witnesses_receipt.json).

## 4. Decoding into actual instruction-field sets

For a fixed tag t, the field is specified by exact membership:

\[
\begin{aligned}
 p\in F_t\ \longleftrightarrow\quad
 \exists k\exists d\,[&\operatorname{Pair}(p,k,d)\land\\
 &\exists c\,
   (\operatorname{Val}(g,k,c)\land\operatorname{Pair}(c,t,d))].
\end{aligned}
\]

### A bound for Separation

Let U denote the set-union operation. An entry \(\langle k,c\rangle\)
in g puts both k and c in \(U^2(g)\). The instruction pair
\(c=\langle t,d\rangle\) puts d in \(U^4(g)\). Thus

\[
 B=U^2(g)\cup U^4(g)
\]

contains the coordinates of every field pair \(\langle k,d\rangle\).
Those pairs belong to \(\mathcal P(\mathcal P(B))\), where Separation
constructs the required field. This argument works for any supplied g.
It has no finite-carrier or transitive-domain premise.

### Shape, opcode and semantics

Exact membership ensures that every object in a field has the required
pair form. The `Tagged` condition supplies a valid instruction witness
for its selected code. Pair injectivity identifies the tag and payload.
Distinct tags exclude competing opcodes at the same row; functionality
of g fixes the selected code, and pair injectivity then fixes its
operand tuple.

A selected witness initially supplies the semantic clause for some
value r0 of f at the row. The target `Trace` formula quantifies over
every value r at that row. The premise `Graph(f,m)` proves r=r0, so
equality substitution transports the semantic clause to r. This step
is needed for the exact ACE-03U execution interface.

The decoder concludes

\[
\begin{aligned}
 &\operatorname{Graph}(f,m)\land
  \operatorname{Distinct}(\vec t)\land
  \operatorname{Tagged}(g,f,m,n,A,\vec t)\\
 &\qquad\longrightarrow
  \exists P\,
   \bigl(\operatorname{Syntax}(P,m,n)\land
         \operatorname{Trace}(P,f,m,n,A)\bigr).
\end{aligned}
\]

The composed finite theorem supplies `Graph(f,m)` from `validProgram`,
obtains the distinct tags from w and constructs g with finite selection.

The decoder has 15 proof checks, 26,836 kernel visits and 32 rejection
controls. Fourteen statement conclusions are new to this development.
The remaining check reproves the existing graph-value-domain statement
with a different proof tree. Its replay checks both the identical
conclusion and the different tree. Eleven decoder proofs also pass
pure-logic checking.

Sources: [decoder proofs](instruction_decoding.mjs),
[independent replay](instruction_decoding_replay.mjs),
[receipt](instruction_decoding_receipt.json).

## 5. Exact equivalence with the pinned Def operation

Let

\[
 \operatorname{Decorated}(f,m,n,A)
 \equiv \exists P\,
  (\operatorname{Syntax}(P,m,n)\land
   \operatorname{Trace}(P,f,m,n,A)).
\]

Define \(D_{\mathrm{syn}}(A,X)\) by taking the pinned
`definable(A,X)` formula and replacing its `validProgram(f,m,n,A)`
condition with `Decorated(f,m,n,A)`. Every other part of that formula
is retained, including:

- The separate empty-set branch for X.
- The omega witness w and both membership conditions n in w, m in w.
- The nonempty conditions on the width and program length.
- The original trace f and the complete `lastSlice(f,m,n,A,X)` clause.

In particular, `lastSlice` continues to require its original last row,
zero coordinate and full base tuple. The source formula remains fixed
through the proof of both directions:

\[
 \forall A\forall X\,
 \bigl(\operatorname{definable}(A,X)
       \longleftrightarrow D_{\mathrm{syn}}(A,X)\bigr).
\]

Applying these pointwise implications in the two directions of set
membership yields

\[
 \forall A\forall B\,
 \left[
   \operatorname{Def}(A,B)
   \longleftrightarrow
   \forall X\,
     (X\in B\longleftrightarrow D_{\mathrm{syn}}(A,X))
 \right].
\]

The replay independently reconstructs the decoded formulas. It also
rebuilds the original outer formula with `validProgram` and compares
that tree directly with the pinned `definable`. This checks the exact
scope and placement of the preserved witnesses.

The complete composition family has six checked statements and
53,529 kernel visits:

| Statement | Kernel visits |
| --- | ---: |
| Finite trace admits decoded syntax | 10,456 |
| Finite `validProgram` iff decoded syntax exists | 10,695 |
| Pinned definable implies decoded syntax form | 10,510 |
| Decoded syntax form implies pinned definable | 259 |
| Pointwise definable equivalence | 10,776 |
| Def-set equivalence | 10,833 |

The reverse definable implication also passes pure-logic checking.
Each composed proof includes the complete proof trees for the lemmas it
invokes. The visit counts include repeated visits through those dependencies.

## 6. Verification and reproduction

| Family | Proof checks | New statements | Reproved existing statements | Kernel visits | Rejection controls |
| --- | ---: | ---: | ---: | ---: | ---: |
| Distinct instruction tags | 2 | 2 | 0 | 693 | 9 |
| Entry packing and finite assembly | 9 | 9 | 0 | 6,070 | 26 |
| Exact field decoding | 15 | 14 | 1 | 26,836 | 32 |
| Composed decoration and Def equivalence | 6 | 6 | 0 | 53,529 | 22 |
| Total | 32 | 31 | 1 | 87,128 | 89 |

All 32 conclusions are rebuilt independently. Across the replays,
fourteen proofs additionally pass pure-logic checking. Controls cover
removed premises, altered live Separation predicates, escaped field
variables, illegal instantiation and an attempted Choice axiom import
under ZF.

The set axioms used across these proof trees are Pairing, Union,
Power Set, Separation and Foundation. The omega set is supplied by
the finite theorem's premise or the original `Def` witness.

Run the combined replay from the repository root:

```sh
node research/ace/ace03v_replay.mjs > /tmp/ace03v.json
diff -u research/ace/ace03v_receipt.json /tmp/ace03v.json
```

The runner starts one proof family at a time in a separate process with
a 3,072 MiB JavaScript heap limit and a 300-second timeout. Each output
must match its separately pinned receipt byte for byte. The combined
receipt records the source import closure and checks all 33 original
ACE-03S source hashes plus the 19 source hashes from ACE-03U.

An independent isolated composition replay took 47.262 seconds with
peak resident memory of 1,968,156 KiB, about 1.88 GiB, under the
3,072 MiB heap limit. An earlier overlapping audit attempt exited 137.
The isolated replay completed and reproduced the receipt exactly.
The combined runner uses sequential child processes to keep this
resource use bounded.

The original kernel, `constructible_definition.mjs` and pinned L formula
remain byte-identical to their previous checkpoints. The new CI job
runs the combined command and compares its aggregate receipt.

### ACE-03U CI completed

The previous head `2b3eafa5dd41cb4894d0cc02e71a9615186b525b` passed all
56 jobs in
[ACE run 45635257368](https://github.com/patrickdugan/MathCan/actions/runs/45635257368),
including its new canonical-syntax-trace job and exact receipt diff.
Both jobs in
[mathematical checks run 45635257707](https://github.com/patrickdugan/MathCan/actions/runs/45635257707)
also passed.

The tested merge commit was
`f325c9ddeae7a5fc95947375a1c4ede2df8ece02`, combining that head with
main at `b3eb33ed10485264fe7a593e3b0ace418d9f9a6d`. The JavaScript
CI used Node v22.23.5; the stage-V local replay used Node v24.22.3.
The stage-V commit has its own workflow status on the pull request.

## 7. Remaining coding and constructibility work

The finite reverse-decoration obligation from ACE-03U is discharged,
and the decoded syntax description now has a checked equivalence with
the exact pinned Def operation.

The next coding step must represent the bounded instruction fields
and their finite dimensions by natural numbers, with proved decoding
and scope checks. The existing finite natural-code implementation
provides fixtures for that work. Its finite computations retain their
separate status from a uniform object-language coding theorem.

Total execution existence for arbitrary supplied syntax remains open.
ACE-03U's uniqueness result ensures agreement whenever two executions
of one syntax program exist. The
[ACE-03T least-code theorem](ACE03T_CONSTRUCTIBLE_WELL_ORDER.md)
accepts a partial evaluation relation once its functionality and
coverage are established, so the order construction can proceed
through those interfaces.

The constructible-order proof still needs a canonical transfinite
history, its initial-segment invariant, and a proof that restricted
order sets belong to L. The final Choice theorem must match the exact
relativized source axiom. Unrestricted schema coverage, formal checker
soundness and native Lean/RH translation remain open.

Paid authoring compute: $0.
