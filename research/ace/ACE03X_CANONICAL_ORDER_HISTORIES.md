# ACE-03X: Canonical order histories and the pinned constructible hierarchy

ACE-03X gives each transitive well-ordered stage a uniquely determined successor order. It also constructs an exact limit order from a coherent family, proves that the resulting recursion has a unique history on every ordinal, and projects those packed histories onto the hierarchy in the pinned definition of `L`.

The final proof family establishes an ambient well-order relation for every set in the pinned constructible class. Its relation is a set containing only ordered pairs from the carrier.

The unchanged executable ZF checker accepted the complete final theorem:

\[
\forall x\,\bigl(L(x)\rightarrow
  \exists R\,(\operatorname{WO}(x,R)\land
              \operatorname{PairOnly}(R,x))\bigr).
\]

All fifteen family/part receipts have passed independently. They contain **114 proof checks, 513,363 kernel visits and 422 rejection controls**. The four final-link proofs account for **179,060 visits**; the final theorem itself takes **60,299 visits**, including its complete embedded dependency tree. [Final receipt](constructible_stage_well_order_receipt.json)

The strict combined replay reproduced all fifteen receipts exactly. Its 114 checks comprise 112 new statement checks and two independent reproofs. It records 200 formula-interface comparisons, including repeated checks at the six actual-history boundaries, and 44 checks in pure logic mode. The final expanded goal has SHA-256 `259706765c737f6f264e56a216cc73e1b92a91cda986fd5e16ed6d9c8d7358b5`. [Combined receipt](ace03x_receipt.json)

The dependency ledger records 61 current source/provenance files. It checks 116 earlier source hashes across 80 distinct files and makes 20 prior-receipt hash comparisons. All 137 input files retain their starting hashes after the complete replay. The aggregate receipt has SHA-256 `e57e18551341cf7e9c6fde0196b98467c4606c4443e7016a7efdfb118f2e1f17`.

## 1. The formulas carried through the construction

`Pair(p,a,b)` is the pinned Kuratowski ordered-pair formula. A relation is represented by a set, and

\[
\operatorname{Val}(R,a,b)
\iff \exists p\,(p\in R\land\operatorname{Pair}(p,a,b)).
\]

`Graph(f,d)` gives an exact functional graph on domain `d`. Its membership clause requires every graph member to represent a pair whose first coordinate belongs to `d`. Each index in `d` has a unique value. These are the definitions already used by the constructible hierarchy. [Definition source](constructible_definition.mjs)

The shared `WO(A,R)` formula requires irreflexivity and transitivity on `A`. It also requires comparison of any two distinct members of `A`, together with a least member for every nonempty subset of `A`. The formulas use `Val(R,x,y)` for comparisons. Exact membership specifications accompany every new canonical relation so that Extensionality can identify the relation as a set. [Canonical relation source](canonical_relation.mjs) · [Independent relation replay](canonical_relation_replay.mjs)

A packed order state is a pair \(p=\langle A,R\rangle\). The predicate

\[
\operatorname{Good}(p)
\iff\exists A\,\exists R\,
  \bigl(\operatorname{Pair}(p,A,R)\land
        (\operatorname{Trans}(A)\land\operatorname{WO}(A,R))\bigr)
\]

records the property needed to continue the recursion.

For carriers \(A\subseteq B\), an extension from \((A,R)\) to \((B,S)\) preserves comparisons on `A`:

\[
\forall x,y\in A\,
  \bigl(\operatorname{Val}(S,x,y)\leftrightarrow
        \operatorname{Val}(R,x,y)\bigr).
\]

It also makes `A` an initial segment:

\[
\forall x\in A\,\forall y\in B\,
  \bigl(\operatorname{Val}(S,y,x)\rightarrow y\in A\bigr).
\]

`Embed(p,q)` packages those statements with the two state pairs. The checked helpers prove reflexivity and composition of embeddings. [State source](canonical_stage_order.mjs) · [State replay](canonical_stage_order_replay.mjs)

## 2. A unique successor recipe

The input is a transitive set `A` with a supplied well-order `R`. The next carrier `B` satisfies the exact pinned formula `Def(A,B)`. The construction orders all raw finite descriptions over `A`, evaluates the valid descriptions, and assigns each definable set its least defining description.

The raw description order is specified through thirteen exact set constructions. The order of these steps matters because later products and sequence orders use the earlier outputs.

| Output | Exact construction |
|---|---|
| \(r_\omega\) | Membership order on \(\omega\) |
| \(P\) | \(\omega\times\omega\) |
| \(r_P\) | Lexicographic order on `P` |
| \(I\) | \(\omega\times P\), the instruction alphabet |
| \(r_I\) | Lexicographic order on `I` |
| \(S_g\) | All finite tuples over `I` |
| \(r_g\) | Shortlex order on \(S_g\) |
| \(S_b\) | All finite tuples over `A` |
| \(r_b\) | Shortlex order on \(S_b\) induced by `R` |
| \(Q\) | \(S_g\times S_b\) |
| \(r_Q\) | Lexicographic order on `Q` |
| \(C\) | \(\omega\times Q\), the raw description carrier |
| \(T\) | Lexicographic order on `C` |

Each product has an exact membership contract. The sequence carriers specify their finite tuples, and each relation specifies every member of its underlying set. The uniqueness proof follows these dependencies in order. It identifies all thirteen outputs before closing the existential recipe. Thus the public instruction carrier, description carrier and description order are uniquely determined by \((\omega,A,R)\). [Description recipe](canonical_description_order.mjs) · [Independent replay](canonical_description_order_replay.mjs) · [Receipt](canonical_description_order_receipt.json)

The five instruction tags are the canonical first five finite ordinals. Their checked existence and uniqueness connect the raw code order to the evaluator for the pinned `Def` schema. [Instruction codes](syntax_instruction_codes.mjs) · [Evaluation source](description_evaluation.mjs)

The evaluation graph `F` has the exact membership condition

\[
 p\in F\iff
 \exists c\in C\,\exists X\in B\,
 \bigl(\operatorname{Pair}(p,c,X)\land
       \operatorname{Eval}(c,X,A,\omega,\vec t)\bigr).
\]

Evaluation is partial on the raw carrier. Its checked functionality identifies the output whenever a code evaluates, while its surjectivity supplies a description for every member of `B`. Consequently each \(X\in B\) has a least evaluating code under `T`. Comparing those least codes gives a well-order `U` on `B`. [Def-stage evaluation and order](definable_stage_order.mjs) · [Independent replay](definable_stage_order_replay.mjs)

The successor relation `S` keeps the old `R` comparisons inside `A`. Every member of `A` precedes every member of \(B\setminus A\), whose internal comparisons come from `U`. The established inflation theorem gives \(A\subseteq\operatorname{Def}(A)\) for transitive `A`. This supplies the inclusion needed for the initial-segment conclusion, and the earlier transitivity theorem gives `Trans(B)`.

The new `Core(A,R,B,S)` formula retains the complete recipe. It includes \(\omega\) and the canonical tags, then binds the instruction carrier and description order together with the exact evaluation and induced-order relations. Its final clause specifies the exact membership of `S`.

For two witnesses of `Core`, the proof first identifies their omega sets. Tag uniqueness aligns the evaluator parameters. The thirteen-step recipe then aligns the description data, after which Extensionality identifies the evaluation graph and each derived relation. This proves uniqueness of `S` for fixed `A`, `R` and `B`. The separate `Def` uniqueness theorem identifies the next carrier when comparing complete successor states.

The resulting packed operation satisfies

\[
\operatorname{Good}(p)\rightarrow\exists q\,\operatorname{Next}(p,q),
\]

\[
\operatorname{Next}(p,q)\land\operatorname{Next}(p,q')
\rightarrow q=q'.
\]

Every `Next` witness is good and extends its input as an initial segment. The family checks fifteen modules, including the two uniqueness links and the exact successor existence theorem. [Canonical successor source](canonical_stage_order.mjs) · [Replay](canonical_stage_order_replay.mjs) · [Receipt](canonical_stage_order_receipt.json)

## 3. The exact canonical limit

Let `H` be a set of packed states. The condition `Val(H,A,R)` identifies one of its recorded carrier-order pairs. The limit carrier `B` is specified by

\[
 x\in B\iff
 \exists A\,\exists R\,
   \bigl(\operatorname{Val}(H,A,R)\land x\in A\bigr).
\]

For \(x,y\in B\), define the comparison predicate

\[
\Phi(H,B,x,y)\iff
(x\in B\land y\in B)\land
\exists A\,\exists R\,
\bigl((\operatorname{Val}(H,A,R)\land(x\in A\land y\in A))
      \land\operatorname{Val}(R,x,y)\bigr).
\]

The order set `T` satisfies

\[
 p\in T\iff
 \exists x\,\exists y\,
   \bigl(\operatorname{Pair}(p,x,y)\land\Phi(H,B,x,y)\bigr).
\]

Both exact sets exist for every set `H`. The carrier coordinates lie in \(\bigcup\bigcup H\), so Separation forms their collection and Union forms `B`. The canonical relation construction bounds the required pairs inside \(\mathcal P(\mathcal P(B))\). Extensionality proves uniqueness of both outputs. Packing them gives a total functional operation `Value(H,p)`.

The well-order conclusion uses the following history properties.

| Contract | Required property |
|---|---|
| `Local(H)` | Every recorded `R` well-orders its carrier `A`. |
| `Directed(H)` | Any two recorded carriers are contained in a recorded common carrier. |
| `Extends(H)` | Inclusion between recorded carriers preserves their comparisons and makes the smaller carrier an initial segment. |

A common upper stage transports any comparison between the recorded orders. This proves the exact restriction of the limit order to each stage and its initial-segment property. It also supplies a stage containing the points needed for the order laws.

For the least-element clause, take a nonempty subset `X` of `B` and a stage meeting `X`. Separation forms its intersection with that stage. A local least element of the intersection is least in all of `X`: an earlier element under the limit order would belong to the same stage by initiality. The family also proves `Trans(B)` when all recorded carriers are transitive.

These results include the empty family, which gives the empty carrier and empty comparison relation at the initial stage. [Limit source](canonical_limit_order.mjs) · [Replay](canonical_limit_order_replay.mjs) · [Receipt](canonical_limit_order_receipt.json)

## 4. Uniform recursion and the seeded example

The generic recursion theorem accepts a pure membership-language formula

\[
\operatorname{Step}(f,i,r,\vec a)
\]

with free-variable layout `[history, index, value, ...parameters]`. A history is an exact graph whose value at each index satisfies that step formula. Its theorem keeps the needed contracts explicit.

| Contract | Meaning |
|---|---|
| Totality | Every history on an ordinal admits a next value. |
| Functionality | Two next values for the same history and index are equal. |
| Prefix locality | Agreement of values below an index transports the step formula between histories. |

The proof constructs exact restrictions of histories and proves agreement on overlapping ordinal domains. At a limit, Replacement collects the unique shorter histories; their compatible union supplies the graph. A successor extension adds its newly determined pair. Foundation supports the induction used in the coherence and existence arguments. The generic family proves existence and uniqueness on every ordinal under the displayed contracts. [Uniform recursion source](uniform_history_recursion.mjs) · [Replay](uniform_history_recursion_replay.mjs) · [Receipt](uniform_history_recursion_receipt.json)

A separate instance uses arbitrary seed parameters `a` and `b`:

\[
\operatorname{Seed}(f,i,r,a,b)\iff
\forall z\,
\left(z\in r\leftrightarrow
 \bigl((z=a\lor z=b)\lor
       \exists j\in i\,\operatorname{Val}(f,j,z)\bigr)\right).
\]

Its next value contains the two seeds and every preceding value of the history. Thus the first value is \(\{a,b\}\), and the next contains that first value as an additional member. Replacement supplies the prefix range. Pairing and Union adjoin the seeds, while Extensionality gives uniqueness. Prefix agreement transports the range condition directly.

All recursion contracts are discharged for this instance. Its closed ordinal-history theorem exercises a step that depends on preceding values and carries two arbitrary parameters. Six modules pass, including the complete seeded existence-and-uniqueness theorem. [Seeded instance](uniform_history_example.mjs) · [Replay entry point](uniform_history_recursion_replay.mjs) · [Receipt](uniform_history_example_receipt.json)

## 5. The indexed limit adapter

For an ordinal-indexed graph `f` on `d`, Replacement forms the exact range

\[
 p\in H\iff\exists i\in d\,\operatorname{Val}(f,i,p).
\]

Pointwise good states give local well-orders and transitive carriers in `H`. Forward embeddings between history values supply the remaining limit hypotheses.

Ordinal comparison chooses an index at least as late as either of two recorded states, which proves directedness. Equal indices have equal packed values by graph functionality. Ordered-pair injectivity then identifies their coordinates.

The `Extends(H)` contract quantifies over carrier inclusions. If the index order runs opposite to a supplied inclusion \(A\subseteq B\), forward extension supplies \(B\subseteq A\). The two inclusions allow the recorded restriction equivalence to be read on `A`, and the initiality conclusion follows from membership in `B`. This handles repeated carriers within the indexed history.

The adapter concludes that the canonical packed limit value is good and embeds every preceding value. These are the exact conclusions used by the actual recursion step. [Indexed adapter](indexed_order_family.mjs) · [Replay](indexed_order_family_replay.mjs) · [Receipt](indexed_order_family_receipt.json)

## 6. Discharging the actual history contracts

The actual step requires its output `r` to be good and to contain every earlier value as an initial segment. Its final clause selects the relevant hierarchy equation:

\[
\operatorname{Step}(f,i,r)=
\operatorname{Good}(r)\land
\bigl(\operatorname{Prior}(f,i,r)\land
      (\operatorname{SuccCase}(f,i,r)\lor
       \operatorname{LimitCase}(f,i,r))\bigr).
\]

The successor case obtains the preceding packed value and applies `Next`. The limit case includes the assertion that `i` has no predecessor, then applies `Value` to the exact prefix range. At index zero, that range is empty.

Totality follows from the successor construction and the indexed limit adapter. Embedding composition supplies the `Prior` clause at successors. Functionality uses uniqueness of the predecessor index and of graph values; the canonical successor and limit operations then identify the outputs. The predecessor assertion separates the two cases. Prefix locality follows by transporting graph values and the exact range equation.

With these contracts proved, the generic recursion theorem yields

\[
\forall d\,
\left(\operatorname{Ord}(d)\rightarrow
\exists f\,
 \bigl(\operatorname{Hist}(f,d)\land
       \forall g\,(\operatorname{Hist}(g,d)\rightarrow g=f)\bigr)\right).
\]

The actual-history work is replayed in six parts. Its existence part checks the complete composed proof with the real successor and limit definitions. That endpoint passed with **55,964 kernel visits**. [Actual history source](constructible_order_history.mjs) · [Independent replay](constructible_order_history_replay.mjs) · [Existence receipt](constructible_order_history_existence_receipt.json)

## 7. Exact projection onto the pinned hierarchy

The packed history records both carriers and orders. The projection constructs a graph `g` of carrier coordinates with the agreement

\[
\forall i\in d\,\forall A\,
\left[\operatorname{Val}(g,i,A)\leftrightarrow
 \exists p\,\exists R\,
   \bigl(\operatorname{Val}(f,i,p)\land
         \operatorname{Pair}(p,A,R)\bigr)\right].
\]

Graph functionality and ordered-pair injectivity make the carrier at each index unique. Replacement therefore produces the exact set of pairs \(\langle i,A\rangle\). Its membership contract proves that `g` is a graph on `d` and identifies it uniquely.

The projection then proves the original `stageGraph(g,d)` formula. In a successor branch, the `Next` witness supplies the exact `Def` equation between the two carriers. At a limit, the exact prefix range and the canonical limit carrier equation combine to give

\[
 x\in A_i\iff
 \exists j\in i\,\exists A_j\,
   \bigl(\operatorname{Val}(g,j,A_j)\land x\in A_j\bigr).
\]

Transitivity of the index domain places each needed predecessor index inside the projection domain. The replay independently expands both pinned stage formulas and checks equality with their existing definitions.

For every ordinal `d` and actual packed history `f`, the result is

\[
\exists g\,
 \bigl((\operatorname{Graph}(g,d)\land
        \operatorname{CarrierAgreement}(f,d,g))
       \land\operatorname{stageGraph}(g,d)\bigr).
\]

A further theorem supplies a well-order for every projected carrier and proves that carrier transitive. The projection family uses Pairing and Extensionality together with one exact Replacement instance. [Projection source](carrier_history_projection.mjs) · [Replay](carrier_history_projection_replay.mjs) · [Receipt](carrier_history_projection_receipt.json)

## 8. The final theorem and its relation set

The final family connects the projection to any witness of membership in the pinned `L`. Such a witness supplies an ordinal `alpha`, its successor domain `d`, a pinned stage graph on `d`, and a stage `B` containing the given set `x`.

The canonical history on `d` projects to another pinned stage graph. The existing stage-graph coherence theorem identifies the two carrier values at `alpha`. Hence the supplied `B` is transitive and has an ambient well-order. Since \(x\in B\), transitivity gives \(x\subseteq B\). [Earlier coherence proof](hierarchy_closure.mjs) · [Final link source](constructible_stage_well_order.mjs)

The checked restriction family constructs an exact relation on `x` by Separation:

\[
 p\in S\iff
 p\in R\land
 \exists u\in x\,\exists v\in x\,
   \operatorname{Pair}(p,u,v).
\]

Its comparisons agree with `R` on `x`, so the order laws and least-element property transfer. The output satisfies

\[
\operatorname{PairOnly}(S,x)\iff
\forall p\,
\left(p\in S\rightarrow
 \exists u\,\exists v\,
 ((u\in x\land v\in x)\land\operatorname{Pair}(p,u,v))\right).
\]

This restriction has exact membership and is unique. The seven-module restriction family has passed, with its main existence theorem using Separation. [Restriction source](restricted_well_order.mjs) · [Replay](restricted_well_order_replay.mjs) · [Receipt](restricted_well_order_receipt.json)

The final exported theorem is

\[
\boxed{\forall x\,
 \bigl(L(x)\rightarrow
   \exists R\,(\operatorname{WO}(x,R)\land
               \operatorname{PairOnly}(R,x))\bigr).}
\]

The four-proof final family checks the history projection, agreement with arbitrary pinned stage witnesses, and the resulting relation on each constructible set. Its complete trees passed the final replay. [Final independent replay](constructible_stage_well_order_replay.mjs) · [Final receipt](constructible_stage_well_order_receipt.json)

## 9. Executable verification and source preservation

The checked receipts are:

| Replay family | Checked modules | Kernel visits | Rejection controls | Receipt |
|---|---:|---:|---:|---|
| Canonical description recipe | 4 | 15,303 | 15 | [JSON](canonical_description_order_receipt.json) |
| Canonical limit | 23 | 8,775 | 81 | [JSON](canonical_limit_order_receipt.json) |
| Uniform recursion | 15 | 27,562 | 24 | [JSON](uniform_history_recursion_receipt.json) |
| Seeded recursion instance | 6 | 9,722 | 15 | [JSON](uniform_history_example_receipt.json) |
| Canonical successor stage | 15 | 130,513 | 66 | [JSON](canonical_stage_order_receipt.json) |
| Indexed limit adapter | 14 | 19,700 | 69 | [JSON](indexed_order_family_receipt.json) |
| Actual history: range | 3 | 91 | 9 | [JSON](constructible_order_history_range_receipt.json) |
| Actual history: structure | 4 | 301 | 12 | [JSON](constructible_order_history_structure_receipt.json) |
| Actual history: functionality | 1 | 2,903 | 3 | [JSON](constructible_order_history_functional_receipt.json) |
| Actual history: totality | 1 | 47,881 | 4 | [JSON](constructible_order_history_total_receipt.json) |
| Actual history: coherence | 1 | 3,593 | 4 | [JSON](constructible_order_history_coherence_receipt.json) |
| Actual history: existence | 1 | 55,964 | 4 | [JSON](constructible_order_history_existence_receipt.json) |
| Carrier projection | 15 | 10,626 | 71 | [JSON](carrier_history_projection_receipt.json) |
| Actual restricted relation | 7 | 1,369 | 30 | [JSON](restricted_well_order_receipt.json) |
| Final pinned-class link | 4 | 179,060 | 15 | [JSON](constructible_stage_well_order_receipt.json) |
| **Total** | **114** | **513,363** | **422** | |

Each replay checks its proof conclusions against independently built formulas. Those builders fix quantifier order and conjunction structure, including the exact source-schema expansions at the hierarchy interfaces. The controls exercise invalid proof scope and damaged inference steps. Other controls change a requested contract by omitting a premise or altering a coordinate, then compare it with the conclusion already returned by the kernel. Several receipts report those categories separately. Their sum is the rejection-control count shown above.

The additions preserve the earlier proof modules and their receipt bytes. The kernel and `L_formula.json` retain their pinned contents. The aggregate runner checks the original provenance manifest together with the ACE-03U, ACE-03V and ACE-03W manifests. It also snapshots the current dependency sources, replays every family in a fresh process, compares complete receipt output, and checks the input hashes again afterward. The completed ledger appears in `ace03x_receipt.json`. [Aggregate runner](ace03x_replay.mjs) · [Pinned kernel](zf_interface.mjs) · [Pinned `L` formula](L_formula.json)

Large expanded formulas required care with memory. Closed imported lemmas were moved outside deep existential contexts, and equality transport was narrowed to the clauses being aligned. Selective builders avoid retaining unrelated proof families. The actual-history and final-link processes use a 3,000 MiB heap limit; the other child processes allow 3,072 MiB. Explicit collection clears temporary generation data before the largest checks. Time budgets range from 300 to 1,200 seconds. The exact proof goals and pinned inference rules remain the same. [Aggregate process configuration](ace03x_replay.mjs) · [Actual-history replay](constructible_order_history_replay.mjs)

The local aggregate completed all child processes in approximately 574 seconds in total. Its final family took 238 seconds on that rerun. The registered `canonical-order-history-replay` CI job has a 45-minute budget and compares the complete aggregate output with the committed receipt. CI status for the published commit is recorded in [PR #278](https://github.com/patrickdugan/MathCan/pull/278). [.github/workflows/ace-replay.yml](../../.github/workflows/ace-replay.yml)

To reproduce the strict aggregate:

```sh
ACE_REPLAY_PROGRESS=1 node research/ace/ace03x_replay.mjs > /tmp/ace03x.json
diff -u research/ace/ace03x_receipt.json /tmp/ace03x.json
```

The original kernel and pinned class remain byte-identical to the ACE-03W base commit `cc56d29760c6fbdf90876e5155d14b4b152e8d27`. The pinned `L_formula.json` SHA-256 remains `f6deb563af271469873b44118e8925b30394e1a21ec4c1e9fd8d103d1fdffdc0`.

## 10. Remaining mathematical and verification obligations

The output relation in the final target is an ambient set. A further argument must prove that a suitable well-order relation belongs to `L`. That requires internal control of the construction, including its histories and the relation restrictions used to obtain an order on a particular constructible set.

An exact relativized Choice import also remains to be checked against the source axiom formula. An internal well-ordering statement requires `L(R)` for its order witness. The selector obtained from that order must also belong to `L`, with the quantifier guards required by the source Choice schema. The current replays reject use of the ambient Choice axiom. [Source axiom and translation interface](zf_interface.mjs)

A global class well-order and a unique canonical restricted relation for each arbitrary constructible set would require separately stated theorems. The present final target asserts existence of a suitable relation for each set. Its canonical history and cross-history coherence provide the preceding construction.

The uniform recursion generator accepts pure step formulas with parameters. This work checks the seeded instance as well as the actual canonical order step. A formal adequacy theorem for every admissible formula or every intended schema instance would require its own statement and proof. The earlier unbounded Replacement work likewise retains its stated coverage obligations. [Uniform recursion interface](uniform_history_recursion.mjs) · [Earlier unbounded Replacement report](ACE03S_UNBOUNDED_REPLACEMENT.md)

The executable kernel has accepted the reported proof objects and rejected the recorded corruptions. Formal soundness of that checker remains open. The independent target builders and preservation hashes provide distinct evidence about formula identity and source stability; a soundness theorem must justify the kernel's inference implementation itself. [Kernel source](zf_interface.mjs)
