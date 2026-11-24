# RH-26B-14 — completed valuation export, finite-support strengthening and constant propagation

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26B14_REGISTRATION.md](RH26B14_REGISTRATION.md), `23d691b3df8474dd1fa1faf9eb048cca2c4baa7d`, before upstream reads.  
**Frozen upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`; consolidated main observed `a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1`. No equivalence claim.  
**Disposition:** **SOURCE PASS for the complete point_bound, etaSum_le, export_bound_of_admissible, eventual Large and uniform/family export proofs, and all lamB/lamG pointwise supplier branches.** The entire ExportBoundOfAdmissible.lean has been read over B10–B14. Deeper arithmetic hypotheses, global RH consumer chain and quantitative theta multiplicity exponent remain separate/unresolved. Independent refinements below are paper deductions, not new kernel proofs or upstream edits.

## 1. Complete numerical point bound

Let C>0, H=Ub(L,C), g=large2(L)=x^eps, X=f*m*b*g², and

```text
G0=6+nuBudget(D)+log(hE)+log(restRowsFiniteGroupCard).
```

The original `point_bound` at ExportBoundOfAdmissible.lean:936–1039 was partly read in B13. The continuation at [ExportBoundOfAdmissible.lean:1001–1039](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L1001-L1039) instantiates sum_qd, sum_small, sum_exc and glob_le on the respective filters; combines them with the previously obtained sum_g, sum_23; and uses big_le_b and b<=X. In particular the proof absorbs the full exceptional/generator/global correction by

```text
(20+2+1164000)*(C+1)^2*H^18 <= X
```

at 1023–1027. Its final hK (1029–1036) is the elementary inequality

```text
1000*(C+1)^3*X + 8*C*X + 4*C*X + X
 <= 2000*(C+1)^3*X.
```

Thus the registered B13 five-mask assembly is exactly the supplier path used in the source. No hidden additional multiplicative factor arises here.

## 2. Complete uniform local table and prime envelope

The remaining `loc_le_lamB` proof is completed at [MemPrimesOverOfMem.lean:501–547](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L501-L547). Its high-order inert branch sums per-place costs proportional to nLam+1, using their bound 4f. The other inert branch uses hCc or hD according to lA<=l or low order; flatCD_le transfers the local band contribution to the uniform flatB, and the finite sums of nLam+1 and nLam are bounded by 4f and 2f. This completes all branches of the actual uniform local table cost.

At [MemPrimesOverOfMem.lean:561–602](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L561-L602) the source proves VVr_nonneg, vvTerm_nonneg, vhE_nonneg, defines the exact

```text
lamG(l) = if l in gset D then C*x^C*etaSz else lamB(l)
```

and proves lamB nonnegative for l>=2. This resolves B13's exact declaration boundary.

The theorem `etaSum_le` at [MemPrimesOverOfMem.lean:606–695](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L606-L695) is the complete global arithmetic assembly before point_bound. It requires AdmT, the stated generator-ne-two premise, Summable(vvTerm D), and an eligible j. The proof obtains C>0 from P.CLw_pos and the polynomial parameter bound. Its generator-ne-two argument is named _hg2 and unused in the displayed body; retain it in source-compatible contracts unless deliberately proving a separate stronger theorem.

Set S to the finite image of the twisted support under residue characteristic, R=dZ0(j)>=0. Each l in S is prime. The actual pointwise cost is

```text
sig(l)=nuL(l)+2/l²,
vG(l)=padicValNat(l,restRowsFiniteGroupCard),
U(l)=sig(l)+lamG(l)+VVr(l)+vhE(l)+vG(l).
```

At 626–651, the generator branch uses etaAt_le_g and adds the nonnegative omitted nuL and vG terms; the non-generator branch proves U>=0 and applies etaAt_le, using loc_le_lamB, ArchimedeanSignatureMatching and adm6. Thus etaAt(j,l)<=log(l)*R*U(l). At 653–657 the proof uses etaSum_eq_sum to obtain exactly

```text
etaSum(j) <= R*sum_{l in S} log(l)*U(l).
```

This is the actual source finite-support estimate, prior to discarding any support information. The arithmetic budgets at 660–695 are:

| Component | Actual intermediate use | Source final allowance |
| --- | --- | --- |
| nuL + 2/l² | sum log(l)/l² <=2 and sum nuL(l)log(l)<=nuBudget | 6+nuBudget (4 already follows) |
| lamG | exact finite sum over S | point_bound supplies numerical envelope separately |
| VVr | equality with vvTerm on prime S; Summable.sum_le_tsum using nonnegativity | tsum vvTerm |
| vhE | sum_padicVal_log_le, hE nonzero | log hE |
| vG | sum_padicVal_log_le, finite group cardinal positive | log restRowsFiniteGroupCard |

`NuHost.lean` at [NuHost.lean:57–82](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CyclotomicBounds/CyclotomicOrders/NuHost.lean#L57-L82) gives the exact nuBudget=log QS+log(t*r), nuL zero at generator primes (with l!=2 premise) and q/d, sum_nuL_le, and nuBudget_le<=2log n+log t+log r. The latter proofs invoke UpperTheory.Mu suppliers, which were not recursively audited. `SumLogDivSqModPmOneLe.lean` at [SumLogDivSqModPmOneLe.lean:245–250](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/SumLogDivSqModPmOneLe.lean#L245-L250) starts the actual log/l² theorem (bound 2); its preceding ap_sum proof (201–243) uses a nonnegative finite progression majorant and a telescoping envelope. Its final proof lines and sum_padicVal_log_le declaration lie outside the 250-line window. Their actual uses and conclusions in etaSum_le:660–689 are unambiguous. No separate claim of re-proving the number-theoretic summability or valuation lemmas.

## 3. End-to-end source export and uniformity

The exact theorem `export_bound_of_admissible` at [ExportBoundOfAdmissible.lean:1066–1096](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L1066-L1096) proves

```text
admitted(L,P,C) and Large(x,eps,C)
  imply aux3(L,2000*(|C|+1)^3).
```

It consumes ShaFinOdd to obtain tb and AdmT from admitted. It consumes Summable(vvTerm D) to invoke etaSum_le. C>0 follows from the positive CLw and the polynomial cap, so |C|=C. The finite support S is the same prime image as in etaSum_le. Applying point_bound and multiplying by nonnegative R yields the actual stronger intermediate bound

```text
etaSum(j) <= R*[2000*(C+1)^3*X + tsum_l vvTerm(D,l)].
```

The exact role of the Nc term is at 1043–1049 and 1082–1096: Nc_nonneg proves its nonnegativity from its formula, and the proof **adds** (log x)^2*Nc inside the nonnegative coefficient product to match the aux3 statement. This is not needed by the preceding etaSum estimate. The source Nc expression at 1045–1046 is #T2*k*b*g/(n*(n*x^(-eps))). Its possible use in other downstream estimates is not excluded; the observation concerns this particular export proof.

The family closure is explicit:

- `large_eventually` at [ExportBoundOfAdmissible.lean:1127–1182](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L1127-L1182) proves that for fixed eps>0 and any real input C, there is an x0 such that all x>=x0 satisfy every field of Large. It uses eventual log-versus-rpow domination (1108–1125), eventual rpow growth, and a finite intersection of eventual conditions. The proof does not depend on the eventual output coefficient 2000.
- `stmtU_holds` at [ExportBoundOfAdmissible.lean:1184–1201](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L1184-L1201) proves UniformExportStatement eps. For any input Ca it chooses output C_out=2000*(|Ca|+1)^3 **before** quantifying over Fm, obtains positive eps using a nonempty Ix at 0, and sets the common threshold max(x0,max(Fm.x1+1,xL)). It transports x,eps to each family member and applies export_bound_of_admissible. This is uniform in the family constant, with a threshold depending on the family and eventual Large premise.
- `stmtF_holds` at [ExportBoundOfAdmissible.lean:1203–1203](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L1203-L1203) is exactly stmtF_of_stmtU(stmtU_holds eps). B10 recovered that wrapper in ExportFamilies.lean:62–66. B08's LinkFam.main subsequently combines the admissible family with stmtF_holds using N.linkN_of. This closes the supplier that was left open in B08. The deeper N.linkN_of implementation and how LinkN enters the final analytic argument remain distinct inventory chunks.

No new kernel execution of these upstream statements was performed in this source-inventory session. The result is a complete bounded trace of the existing proof text, not a claim to independently certify the entire upstream repository.

## 4. Independent E05C: a tighter coefficient using only the ORIGINAL numerical suppliers

The complete source assembly yields a new low-risk scalar improvement even without any strengthened B10–B13 arithmetic estimates. Preserve the exact absorption ratio instead of replacing it by 1:

```text
rho = 1164022/4000000,
(1164022)*(C+1)^2*H^18 <= rho*b <= rho*X.
```

The five unmodified sum suppliers and G0 bound therefore give

```text
G0 + sum log(l)*lamG(l)
 <= [1000*(C+1)^3+12*C+rho]*X.
```

For C>=0 the elementary identity

```text
2*(C+1)^3-12*C = 2*C^3+6*(C-1/2)^2+1/2
```

and rho<1/2 imply

```text
G0 + sum log(l)*lamG(l) <= 1002*(C+1)^3*X.
```

This strengthening uses the actual original supplier contracts, the existing big_le_b, b<=X, X>=0 and the exact source five-mask majorant. No sharper local arithmetic lemma is needed. The least integer multiplier of this relaxed assembled coefficient envelope is 1002: at C=1/2 the candidate 1001 leaves only (3/2)^3 to absorb 12C+rho, and (3/2)^3<6. This sharpness control is for the relaxed scalar envelope, not for actual arithmetic families or the full correlated source domain.

The B13 conditional coefficient 105 follows if the separately proposed B10/B12/B13 strengthened suppliers are independently established. Now that the downstream proof has been read, both replacements have an exact propagation target:

```text
point_bound with K*(C+1)^3
 -> export_bound_of_admissible with K*(|C|+1)^3
 -> stmtU_holds / stmtF_holds with the same output constant.
```

All source hypotheses, nonnegative K, and the same eventual Large thresholds are retained. The infinite series keeps its coefficient 1. No improved global RH exponent follows merely from numerical constants. The 1002 and 105 statements are paper targets until separately kernel-verified; the latter also needs the stronger component lemmas. A useful next E05C1 module is the exact original-supplier assembly and the 1002 minimum-integer control, followed by the 105 assembly under frozen stronger supplier contracts.

## 5. Independent E05F: retain finite support and remove the unused padding

The exact finite-support step at etaSum_le:653–657 is obtained before the use of hsumm. The only use of that summability premise in this theorem body is 680, where the finite nonnegative vvTerm sum is extended to the infinite sum. Therefore the same local/rank/weight premises prove the following stronger *finite-support form*, without assuming Summable(vvTerm D):

```text
etaSum(j) <= R*[4+nuBudget + log hE + log groupCard
                   + sum_{l in S} log(l)*lamG(l)
                   + sum_{l in S} vvTerm(D,l)].
```

The constant 4 follows from exactly the source inequalities sum log(l)/l²<=2 and sum nuL(l)log(l)<=nuBudget. All real-valued finite cohomological terms are retained with their existing definitions. To apply this at the family export stage, still retain ShaFinOdd to obtain the admissible table from admitted. No claim that nonsummable cohomology satisfies aux3, whose statement has a separate summability premise.

Combining with the original point_bound gives the paper strengthening

```text
etaSum(j) <= R*[2000*(C+1)^3*X - 2 + sum_{l in S} vvTerm(D,l)].
```

This uses the original numerical point_bound (which includes 6), and R>=0. It does not need the Nc padding, the cohomological infinite-tail extension, or a new arithmetic constant supplier. If hsumm is available, define

```text
Tail(S) = tsum_l vvTerm(D,l)-sum_{l in S} vvTerm(D,l) >= 0.
```

Then, relative to the original aux3 envelope, the exact difference between the old upper envelope and the proposed support-preserving upper envelope is

```text
R*[2 + Tail(S) + 2000*(C+1)^3*(log x)^2*Nc].
```

All terms are nonnegative under the source hypotheses. A smaller coefficient K from Section 4 can be substituted into both sides if separately proved.

Further source-backed slack is available in the generator branch: etaAt_le_g omits vG and nuL, while etaSum_le adds both to make the common U(l). NuHost.nuL_eq_zero_of_g makes the latter zero (with its generator-ne-two premise); the vG contribution on generator primes need not be charged. One may retain the separate generator bounds or subtract the nonnegative quantity R*sum_{l in S intersect gset} log(l)*vG(l) from the common finite upper sum. Likewise one may preserve the exact finite valuation sums instead of immediately enlarging them to the full log cardinalities. Such refinements must not be subtracted from a bound that already used a smaller disjoint-support allowance for the same term. B11's coverage/cap certificate similarly applies to each non-generator prime before the finite sum; the generator alternative stays separate.

**Controls for E05F:** a finite nonnegative sequence v(0)=2,v(1)=3 and zero elsewhere with S={0} has total 5, support sum 2, tail slack 3. If negative omitted mass is allowed (v(1)=-3), total -1 is less than support sum 2, disproving monotonic extension. A nonnegative constant-one sequence has finite support sums but no finite summable total; this separates the finite certificate from the infinite-series statement. R=0 makes every discarded-budget term vanish. These are independent scalar fixtures, not instantiated arithmetic cohomology. A Lean experiment should separately prove the finite aggregation, the summable nonnegative tail identity/inequality, and the exact padding-slack formula; preserve the finite-source premise and the distinct infinite-series theorem.

## 6. Read receipt and source inventory boundary

Four distinct upstream files, **791 returned lines**:

| Path relative to src/ | Window |
| --- | --- |
| `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean` | 1001–1207 (207; EOF) |
| `Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean` | 501–750 (250; cap; Mst_ge continues after 750) |
| `Development/AutomorphicArithmetic/CyclotomicBounds/CyclotomicOrders/NuHost.lean` | 1–84 (84; EOF) |
| `Development/AutomorphicArithmetic/ResidueCharacters/SumLogDivSqModPmOneLe.lean` | 1–250 (250; cap; sum_log_div_sq_le continues) |

The two helper reads are direct imports of MemPrimesOverOfMem. Previous B08–B13 source anchors reused without rereads. No whole source scan/build, copied upstream proof, new independent kernel/GPU/QPU/paid compute. Runtime/RAM unmeasured.

**Next:** the valuation export supplier is complete at source level. Prioritize a bounded E05C1 kernel experiment for the original-supplier 1002 and conditional 105 assemblies, with E05F finite-support/Nc padding and E05B rank/degree coverage certificates next. For source inventory B15, register a fresh targeted trace of the exact N.linkN_of supplier (start from the prior LinkNAlongFamilyOfLocalBounds imports: Formalism/SharpRestriction/GlobalTheoremInputs.lean and LevelLetterCocycles/ThetaScalarFamilyOfEigenvalue.lean, following actual declarations and immediate imports); distinguish the recovered uniform valuation contract from the further LinkN/analytic conversion. Other independent E05A/D/E and C04/D01/V01/F01/S01 remain queued. Global theta-lift multiplicity growth exponent remains UNSOURCED.
