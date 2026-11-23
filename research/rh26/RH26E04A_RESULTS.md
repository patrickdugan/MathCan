# RH-26E-04A: overlap-corrected finite rank capacity

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26E04A_REGISTRATION.md](RH26E04A_REGISTRATION.md), committed at `fb84c0dd966012d06f5125d33f1d49c385a4ac69` before implementation and CI.  
**Implementation:** [RH26E04AOverlapCapacity.lean](lean/RH26E04AOverlapCapacity.lean) at `5810fb9346ced9d5101c76150e895300d575d456`; source plus workflow at `d97efea02711c4f3444de9b18716731abf77213a`.  
**Disposition:** IMPLEMENTED, **FIRST KERNEL RUN FAILED; REPAIR IN PROGRESS**. All ten preregistered theorem names have matching print-axioms commands. No admission tokens or native_decide found by source inspection. Compiler acceptance is not yet confirmed.

## 1. Source connection

[RH26B08_RANK_CERTIFICATE.md](RH26B08_RANK_CERTIFICATE.md) recovers the actual local multiplicity theorem in frozen upstream `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, `GoodPointMultiplicityLeRankProof.lean:50–149`. The source uses localization uniqueness to prevent duplicate row labels, indexed subspace independence for dimension additivity, and theta injection to identify ambient capacity with zero-space rank. The independent module isolates only the finite counting and subspace-rank part, generalizing uniqueness with a duplicate-label correction. No upstream proof text or automorphic definitions are imported.

## 2. Frozen mathematical model

Let I be a finite set of indices, A_i finite sets of labels, U their union, and d(s) a natural weight for each label. Define r(s) as the cardinality of {i∈I : s∈A_i}, T=∑_i∑_{s∈A_i} d(s), and D=∑_{s∈U}(r(s)-1)d(s).

The ten intended proof contracts are:

| Declaration | Contract |
| --- | --- |
| occurrence_positive | s∈U iff r(s)>0 |
| weighted_count | T=∑_{s∈U} r(s)d(s) |
| overlap_identity | T=∑_{s∈U}d(s)+D |
| overlap_zero_of_disjoint | Pairwise disjoint label sets imply D=0 |
| budget_with_overlap | Local counts bounded by local weights and union weight ≤R imply ∑m_i≤R+D |
| independent_union_rank | For an indexed independent subspace family, selected dimensions sum to the dimension of the finite supremum, hence ≤dim V |
| subspace_capacity | Instantiate the previous budget at subspace dimensions |
| rank_nullity_defect | dim W=dim range F+dim ker F for an actual linear map F:W→V |
| duplicate_label_fixture | {0,1},{1,2}, unit weights: T=4, union weight 3, D=1, exact equality and failure of uncorrected count |
| dependent_lines_control | Three explicit rational vectors in Q², each nonzero and every pair has only the zero coefficient relation, but triple has a nonzero relation |

The overlap identity handles empty finite sets and natural subtraction by establishing r(s)>0 on the union. The subspace theorem assumes actual indexed independence, not merely pairwise disjoint subspaces. Rank-nullity is proved for a specified map rather than assuming any particular source decomposition. These assumptions are required for the intended conclusions.

## 3. Interpretation and proposed follow-up

For a certified finite direct sum of distinct selected row spaces, duplicate-label defect is a purely incidence-based overcount. A linear map from that direct sum into an ambient space can separately have a kernel, whose dimension measures lost directions. The sum of these two defects gives an exact accounting when the direct-sum domain and its dimension are specified. The present module proves the two identities separately; a theorem composing them into one certified map construction would be a subsequent extension.

For interpretability, the label assignments should be frozen and measured separately from the subspace dependence. A numerical implementation would need explicit tolerances, singular-value diagnostics and an error bound before claiming exact rank. The duplicate fixture is an exact discrete obstruction; the three-line fixture shows that pairwise independence cannot replace independence of the whole family.

Next E04B: block-scalar transport (exact left-inverse injection, then norm perturbation and conditioning). E04C: weighted capacity dual. Source-only B09 remains queued for the actual admissible-table conversion and generic theta injection supplier.

## 4. Pending verification receipt

- [Run 45285266342](https://github.com/patrickdugan/MathCan/actions/runs/45285266342), job `138079841456`, checked commit `d97efea02711c4f3444de9b18716731abf77213a`.
- Source Git blob `3a15e42b277412f5381117140b6405f480b972e5`, 232 lines; 10 theorem declarations and 10 matching audit commands.
- Last observed checkout and toolchain/registration preflight passed; Lean installation in progress. Full compiler exit, exact ten-name allowlist audit, SHA-256, dependency SHA, timing/RSS and artifact remain pending.
- Isolated Lean 4.35.0 / Mathlib v4.35.0 CPU job, 25-minute timeout. No full Deligne or upstream build, GPU/QPU, paid compute or new upstream source reads.

On resumption inspect this exact run first. Preserve any failed compiler receipts and repair only proof bodies or necessary declaration modifiers without weakening the registered mathematical contracts. Close only after successful compiler and complete axiom gate.

## First-run failure receipt

[Run 45285266342](https://github.com/patrickdugan/MathCan/actions/runs/45285266342), job `138079841456`, completed failure on `d97efea02711c4f3444de9b18716731abf77213a`. Source SHA-256 `97383faa2b867d22e28a1dd060cb61ab7bd1cf410a891b73c8c26b0ee8f7dcdc`. [Failed audit artifact](https://github.com/patrickdugan/MathCan/actions/runs/45285266342/artifacts/14870314640). Checkout, toolchain, Mathlib resolution, and artifact upload succeeded.

Eight registered declarations printed only `propext`, `Classical.choice`, `Quot.sound`, including both exact counterexample fixtures, weighted incidence counting, overlap identity, disjointness, combinatorial capacity and rank-nullity. Two errors in `independent_union_rank`: line 125, the empty finite supremum did not simplify to the bottom subspace; line 134, the simplifier did not eliminate the zero-dimensional intersection in the dimension addition identity. The declarations `independent_union_rank` and dependent `subspace_capacity` had sorryAx from elaboration recovery. The complete registered gate failed. Repair only the dimension proof, retain every mathematical contract, and rerun the original audit.

## Proof-only repair

Commit `90105836caabc86b1711dfcfee1eb3e661f36b21` explicitly proves the empty indexed supremum is bottom and rewrites the zero-dimensional intersection in the dimension identity. All ten theorem statements match the original source. Repaired blob `4d5ebf57ab72055dbc81d1e7b39b1b0c6c2e488d`. Fresh [CPU run 45285673626](https://github.com/patrickdugan/MathCan/actions/runs/45285673626) is queued. Compiler exit and ten-name audit remain pending; first failure retained above.
