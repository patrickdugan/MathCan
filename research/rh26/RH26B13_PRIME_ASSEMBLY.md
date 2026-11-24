# RH-26B-13 — prime-class assembly, conductor log budget and tighter point bound

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26B13_REGISTRATION.md](RH26B13_REGISTRATION.md), commit `efe546ff46b59312dd9279f1fb1a28c2854b95cf` before source reads.  
**Frozen upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`; consolidated main observed `a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1`. No equivalence claim.  
**Disposition:** **SOURCE PASS** for small/ramified prime and global scalar correction suppliers, the exact point_bound contract and its five-mask pointwise and finite-sum majorant, the lamB/lenB definitions and part of the admissible-table pointwise supplier. **PARTIAL** for the remaining point_bound proof after line 1000 and final aux3 / uniform family export. New independent paper refinements below. No new kernel result or realized arithmetic family claim.

## 1. Remaining numerical sum suppliers

Write H=Ub(L,C), g=large2(L)=x^eps, X=f*m*b*g², and C>0. The prior B10–B12 source proofs give H>=m>=2, g>=1, f>=m>=2, and b>=4*10^6*(C+1)^2*H^18. Retain the full source parameter and Large assumptions.

- `U_pow_eighteen_le_b` at [ExportBoundOfAdmissible.lean:769–774](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L769-L774) weakens the last scale bound to H^18<=b.
- `sum_23` at [ExportBoundOfAdmissible.lean:776–795](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L776-L795) bounds the small-prime/3 sum by 8*C*X. It explicitly verifies fm>=1, x^C*g<=b via H²<=H^18<=b, then invokes the previously inventoried SmallSum.sum_row_small_le. The B10 independent factor-2 refinement of that lemma applies with the same inputs, yielding the proposed tighter 2*C*X.
- `log_qd_le` at [ExportBoundOfAdmissible.lean:797–839](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L797-L839) uses the actual conductor hypothesis from ParameterChoice'.condE_le, q,d>=1, QS>=1 and t>=1 to prove log q<=g, log d<=g. The proof weakens the conductor power to condE<=b before taking logs.
- `sum_qd` at [ExportBoundOfAdmissible.lean:841–866](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L841-L866) bounds a finite subset of {q,d} by 4*C*X using the separate logarithm bounds, at most two primes, and g<=g².
- `glob_le` at [ExportBoundOfAdmissible.lean:868–913](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L868-L913) proves the scalar correction bound
```text
G0 = 6 + KStar.nuBudget(D) + log(hE) + log(restRowsFiniteGroupCard)
   <= 20*(C+1)^2*H^18.
```
Its first sub-bound hnu<=12*(C+1)^2*H^18 invokes KStar.nuBudget_le D, uses log(n), log(t), log(r)<=their arguments and the rank bounds n,t<=H, r<=2H. The exact nuBudget_le theorem statement/body is not read in this session. The remaining two logarithm caps are explicit fields of ParametersPolynomiallyBounded: log hE<=C*x^C and log restRowsFiniteGroupCard<=C*x^C*g. Their sum with 6 is bounded by 8*(C+1)^2*H^18. The source uses G0 as a global correction separate from the finite prime-category sum. Do not confuse nuBudget with the separate infinite vvTerm series from aux3.

## 2. Exact priority-ordered prime costs

The precise length/total cost definitions in [MemPrimesOverOfMem.lean:285–311](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L285-L311) are now inventoried. The band indicator bandI is 1 exactly when a real witness meets the two-sided weight interval and the relative-error bound. flatB=(wP+eta3)/l+Sc+g+eta3*bandI; rowBr=hB/(l-1)^(jA+1)+(GP+1)*(jA+1)+g.

The length bound lenB has three branches (297–301): split primes use (2fm+f)*eP; the small inert/high-order case uses 4f*C*r*rowBr; otherwise the flat branch uses 4f*C*r*(hB/l²+flatB)+2f*C*m*eP. bbB=C*f*n*t²*nV*g². The exact lamB (307–311) selects:
1. small or 3: C*f*m*b*log x+C*x^C*g²;
2. q or d: 2*C*f*m*b;
3. large prime outside exception set: zero;
4. otherwise bbB+lenB.

The source `loc_le_lamB` at [MemPrimesOverOfMem.lean:432–500](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L432-L500) proves the actual uniform table cost sumOver(tb.len i)+tb.BB(i)<=lamB(l_i) for twisted non-generator local i with the named row/length/exception/ramification conditions. Small, q/d and zero branches are direct applications of their predicates. The nonzero generic branch uses adm5 for BB, local degree sums and split/inert cases to bound lengths; the split case is complete at 480–496. **The inert case begins at line 499 and continues beyond the window.** The exact lamG declaration is not yet read, but its priority generator branch is confirmed by unfolding it at ExportBoundOfAdmissible:968–972. The original source proof uses this generator-first branch and lamB otherwise.

## 3. Actual point_bound and its finite-sum majorant

The theorem `point_bound` at [ExportBoundOfAdmissible.lean:936–938](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L936-L938) states under the full AdmT table, ParameterChoice', polynomial bound, Large and C>0, and a finite S of prime naturals:

```text
G0 + sum_{l in S} log(l)*lamG(L,tb,C,l) <= 2000*(C+1)^3*X.
```

The source explicitly establishes nonnegativity of the five possible log-weighted summands (940–967). At 948–953 it bounds each selected cost by the sum of five masks:

| k | Raw predicate P_k(l) | Unweighted cost c_k(l) |
| --- | --- | --- |
| 1 | l in gset | C*x^C*etaSz |
| 2 | l in host.small or l=3 | C*f*m*b*log x+C*x^C*g² |
| 3 | l=q or l=d | 2*C*f*m*b |
| 4 | l!=2, l!=3, l<=lStar | bbB+lenB(l) |
| 5 | l in tb.exc, lStar<l | bbB+lenB(l) |

The cases at 968–995 show lamG selects just one of these costs: generator first, small/3 second, q/d third, zero for large nonexceptional, then the relevant generic cutoff/exception mask. If generic, the proof uses two_mem_small and exclusion of 3 to satisfy mask 4 or 5. The source masks are not all mutually exclusive (e.g. a small prime l>=5 within the cutoff may satisfy masks 2 and 4). The nonnegative majorant allows extra active masks. At 996–998 the proof sums this inequality and rewrites the five masks as filtered finite sums; s1=sum_g and s2=sum_23 are instantiated at 999–1000. **The final use of the remaining three sum lemmas and scale absorption has not been read beyond this boundary.** We can already independently combine the proved majorant and all five available source supplier contracts. This is a conditional paper derivation of a stronger point_bound estimate, rather than a claim that the original proof text uses our constants or that aux3 has been recovered.

## 4. Independent E05C refinement: joint conductor logarithm budget

ParameterChoice'.condE_le at [DataParams.lean:186–186](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/LocalRingCardinality/DataParams.lean#L186-L186) is exactly

```text
(QS*q*d)^36 * t^150 <= b^(1/2),
```

with the conductor definition at 63, b=exp(g), and all QS,q,d,t>=1 as used in log_qd_le. Take logs while retaining the original exponents, using positivity:

```text
36*(log QS+log q+log d)+150*log t <= g/2.
```

Therefore

```text
log q+log d <= g/72 - log QS - (25/6)*log t <= g/72.
```

For a finite T subset {q,d}, log primes are nonnegative; even if q=d, the finite set counts it at most once, so sum log(l)<=log q+log d. The refined ramified-prime supplier is

```text
sum_{l in T} log(l)*(2*C*f*m*b)
  <= (C/36)*f*m*b*g <= (C/36)*X.
```

This preserves the lower-order factor g instead of inflating it to g². The nonnegative QS,t logarithms and positive logarithm arguments are required. A sharp scalar fixture for the log budget is QS=t=1, q=exp(g/72), d=1, b=exp(g) with g>0; it saturates the product constraint. This fixture uses positive real variables and is not a claim about allowable arithmetic host ranks or prime inputs. Dropping QS>=1 allows QS to cancel arbitrarily large q,d and invalidates the weakened sum-log bound. The exact coefficient 1/72 is sharp on this scalar domain, not necessarily under all the source's additional natural/prime/rank constraints.

## 5. Independent E05C combined scalar point-bound refinement: 2000 to 105

Use the **actual five-mask upper inequality** already read in Section 3, with the known supplier contracts and the B10/B12/B13 independent refinements. Every candidate replacement is conditional on the recovered source hypotheses; the proposed arithmetic strengthening is not independently kernel verified yet.

| Term | Proposed upper bound |
| --- | --- |
| Generator sum | 2*(C+1)^2*H^18 (unchanged source) |
| Small/3 sum | 2*C*X (B10) |
| Ramified q/d sum | (C/36)*X (Section 4) |
| Generic small-prime sum | 104*(C+1)^3*X (B10 polynomial certificate) |
| Generic exceptional sum | 11020*(C+1)^2*H^18 (B12) |
| Global correction G0 | 20*(C+1)^2*H^18 (unchanged source) |

The five-mask inequality applies these suppliers to their corresponding filters of the original prime set S. The source hRe/hExc ensure the hypotheses of sum_exc; membership and the given primality of S ensure the hypotheses of the other four. Add the bounds and use the existing large-scale inequality 4*10^6*(C+1)^2*H^18<=b<=X (f,m,g>=1):

```text
G0 + sum log(l)*lamG(l)
 <= [104*(C+1)^3 + (73/36)*C + 5521/2000000]*X.
```

Since 4*(C+1)^3 - 27*C = (2*C-1)^2*(C+4)>=0 for C>=0, C<=(4/27)*(C+1)^3. Also 1<=(C+1)^3. Thus the coefficient is <= [104+73/243+5521/2000000]*(C+1)^3 < 105*(C+1)^3. We obtain a clean conditional paper target

```text
G0 + sum log(l)*lamG(l) <= 105*(C+1)^3*X.
```

The inequality is derived from the exact source's finite-sum majorant and supplier bounds; it does not need the as-yet unread algebra after line 1000. It retains the full original scale hypotheses; no claim of a new RH exponent or improved global aux3 constant until that consumer is inspected. The number 105 is a sufficient rounded constant, not asserted minimal for the combined envelope or actual arithmetic costs. All sharper components remain unverified in Lean; E04C alone does not certify this new inequality. The independent theorem can be checked under scalar supplier inequalities, then a separate upstream integration would require the source-compatible strengthened suppliers.

## 6. E05E: exact priority-mask accounting and overlap slack

Let a finite set S carry k=1,...,5 predicates P_k(l), nonnegative log-weighted costs v_k(l), and an actual priority-selected index r(l) (or no index, with cost zero). Suppose selection implies its mask is active. Define Q_k(l) to mean r(l)=k, so Q_k implies P_k and the selected sets are pairwise disjoint. In the source the large nonexceptional zero branch must be applied before the generic selection; mask 5 is the only nonzero generic-large branch.

The coarse and exact sums satisfy the identity

```text
sum_{k} sum_{l in S:P_k(l)} v_k(l)
 = sum_{l in S} selected_cost(l)
   + sum_{k} sum_{l in S:P_k(l), not Q_k(l)} v_k(l).
```

This is pure finite incidence accounting, extending E04A's duplicate-label approach from equal weights to category-specific costs. Proof: split every mask into its selected and non-selected parts, exchange finite sums, and use unique selection. Each redundant-mask term is nonnegative, so the exact priority sum is bounded by the coarse sum. Equality holds iff every active non-selected cost is zero. In this source, the exact selected subsets are contained in the eligibility sets used by the five sum lemmas; one can apply the same universal finite-set estimates to the selected subsets without violating their inclusion hypotheses. The sharper actual costs of those smaller subsets require their finer arithmetic/cardinality/log budgets; dropping overlap terms alone does not justify subtracting them from the **upper envelope** unless the identity and a corresponding lower slack certificate are retained.

A source-style fixture: l=5, inside the small-prime set, below lStar, outside gset/q/d. Masks 2 and 4 both hold. With log-weighted costs v2=2,v4=3, the selected cost is 2, coarse masked sum 5, exact redundancy 3. This is a finite abstract mask model, not an exhibited host. With a negative unselected cost, e.g. v4=-3, the coarse sum is -1 and fails to majorize 2. The nonnegativity hypothesis is essential. A future Lean module should prove the identity for arbitrary finite index/prime sets and any Option selection, then prove zero-slack equality characterization and source-priority fixtures.

## 7. Additional row-d scale refinement

The direct dependency `NEqRZeroMulXPow` window recovers three_le_R_zero completion, n=R0*g, logx_small, o_small (1<=o and 4o²<=g), two_Lw_o_le, the modulus/order inequality and `rowd_sum` at [NEqRZeroMulXPow.lean:800–908](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean#L800-L908). The latter bounds

```text
r * sum_{l in T} log(l)/l² <=4*m*g²
```

for finite T of odd integers l>=2 with ordH(l)<=4Lw. Its actual intermediate result (897–902) is <=4m*(log R0+o). The source derives log R0<=g/2 (887–890), 4o²<=g, and g>=4 (892–896). Keep the square-root gain: o<=sqrt(g)/2<=g/4 for g>=4. Thus

```text
r * sum log(l)/l² <=2*m*(g+sqrt(g)) <=3*m*g.
```

This is an independent paper strengthening of that specific rowd_sum lemma under its source hypotheses, dropping one auxiliary g factor. We have not yet traced the exact consumer's use of this bound in sum_rowd or the final prime sum, so do not substitute it automatically into sum_small. Scalar control g>=4 is used for sqrt(g)<=g/2; for 1<=g<4 this inequality fails. This can join the separate E05C real algebra modules.

## 8. Read receipt and next boundary

Three distinct source files, **750 returned lines**, pinned:

| Path relative to src/ | Window |
| --- | --- |
| `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean` | 751–1000 (250; point_bound proof continues) |
| `Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean` | 701–950 (250; jA_le continues) |
| `Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean` | 251–500 (250; loc_le_lamB inert branch begins at 499) |

The two helpers are the already traced direct and second-hop imports of the registered start file. B10–B12 anchors reused without rereads. No whole source scan/build, imported upstream proof, new independent kernel check, GPU/QPU or paid compute.

**Next B14:** freshly preregister `src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean:1001–1250` to finish point_bound and locate its use in aux3 / family export; `src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean:501–750` to complete loc_le_lamB and locate lamG / prime-wise eta bound if required. E05A coherence, E05B rank/degree-weighted slack, E05C scalar constants, E05D band stability and E05E priority-mask accounting remain separately proposed experiments. The remaining full analytic/family derivation and quantitative global theta-lift multiplicity exponent remain unsourced.
