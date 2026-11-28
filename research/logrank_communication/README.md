# Elementary log-rank lemmas and a finite protocol target

Source motivation: [Cogentic pinned README](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/logrank_conjecture/README.md). Canonical executable finite receipt: https://github.com/MoralityLabAI/LoopedTransformers/tree/6b72a5cf78135c746cefcf444921098d087d691f/experiments/logrank_bpd_01. The new asymptotic proof and announced Lean artifact have not been audited.

Let X,Y be nonempty finite sets and M:X×Y→{0,1}. Consider a finite binary deterministic communication tree; Alice branches only on x, Bob only on y, conditioned on public transcript. At the end Bob outputs a function of y and the leaf. Each leaf induces a rectangle A_l×B_l by induction on depth: a local branch restricts only the corresponding factor. The leaf rectangles partition X×Y. Define u_l=1_{A_l}, v_l(y)=1_{B_l}(y) times Bob's local output at that leaf. Then M=sum_l u_l v_l^T exactly. Each summand has real rank <=1, so rank(M)<=#leaves<=2^d for worst-case depth d. If both players must publicly know the answer, the leaf condition is monochromatic and the same rank bound applies.

One-way exact Bob-output cost equals ceil(log2 t) where t is the number of distinct rows: any two distinct rows need distinct messages; an injective fixed-length row-class identifier suffices. For Index_k, the columns have identity rows as witnesses and hence rank k, while t=2^k. Interactive upper bound is ceil(log2 k)+1. This family explicitly separates one-way from interactive complexity.

## Exact DP

For nonempty A,B, define d(A,B)=0 if all rows of M restricted to A×B agree; otherwise minimize 1+max(child costs) over every nontrivial bipartition of either A or B. Induction on |A|+|B| proves optimality: every nontrivial first communicated bit splits one factor, and combining optimal children constructs a protocol of the stated cost. Constant messages can be removed because they reveal no input-dependent information. This is the Bob-output convention; public-output DP instead requires monochromatic terminal rectangles.

For Index_4, the 3-bit query-and-response protocol is optimal. Suppose depth <=2. If the root belongs to Alice, her two branches must each contain at most two distinct rows, since at most one remaining bit from Alice can separate them, and a last bit from Bob supplies no new information about x. Hence at most four distinct rows overall, contradicting sixteen. If Bob speaks first, each child has at most one remaining bit from Alice; since all x remain possible, a child containing two or more column indices has at least four distinct restricted rows, impossible with one bit. At most two columns can be covered by the two children, contradicting four. A constant root can be eliminated. Therefore D_Bob(Index_4)=3.

## Lean formalization queue

1. Define finite binary protocol tree and local branch functions with a dependent leaf decoder; prove transcript rectangles by induction.
2. Express M over a field via outer-product sum over leaves, using finite indicator vectors; prove rank bound via rank subadditivity and rank-one products.
3. Formalize row-class quotient, injective bit codes, and recurrence optimality on cardinality sum.
4. Formalize Index_k using basis rows and bit-vector cardinality; use Index4 depth-two obstruction as a small regression target.
5. Only after source release, audit Cogentic theorem hypotheses and formal imports, axioms, sorry/admit, and matching constants.

These are written mathematical derivations, not Lean-checked theorems. No claim to resolve the full log-rank conjecture.
