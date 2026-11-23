# RH-26C-03: exact Chebyshev normalization and quantitative exponent closure

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26C03_REGISTRATION.md](RH26C03_REGISTRATION.md), commit `3003d539db52cc74e74f98715e43e3d34c899158` before new source reads.  
**Immutable upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Observed upstream main:** `a78183e11ebfeebab77920b5e976f0a3edf1fc76`; no source-equivalence claim.  
**Disposition:** **PASS (source-level normalization; independently derived paper bound closes the actual scalar exponent).** Exact `ch_core` theorem and call to `proposition_size_bound` located. The latter supplier's full proof body is not inspected in this session; its mathematical conclusion is independently rederived below. New Lean kernel check NOT RUN. A fixed-coefficient, no-power-loss X/m+m theorem for the actual prime observable remains UNSOURCED.

## 1. Close the character-balance source trace

The registered continuation of `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:251–500` ends at line 499. The complete `Deduction.ch_core` declaration and proof are at [ChCore.lean:396–495](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L396-L495). Its exact contract is an eventual bound, with fixed real parameters C, eps, CE, Ko, c, M satisfying C>=0, eps>0 and |c|<=1. It quantifies the finite additive group H, natural m, arithmetic data D, host finite set, character logarithmic-derivative data ell, finite sets TT,T2, weights and real scales after the eventual threshold x1.

Its remaining premises require HostFactsS; positive b and k, nonnegative aE; the upper m-window and xm<=k; SizesA, ThinScales, CostWindows, RestSize; T2 contained in A0; CharsA; and the uniform one-sided gap bound from the previous source session for every u in A0.

The conclusion at [ChCore.lean:400–404](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L400-L404) is

```text
GmA(D,ell,Kp,c,x) <= x^(1/2+(C+3)*eps) + SigA(D,ell,A0,Kp,x).
```

Thus G = GmA - SigA obeys the power bound. This is not an absolute-value estimate on G, and SigA must be retained when translating back to the level observable.

## 2. Exact coefficient, density and correction terms

For the scalar reduction write n=|H|, N=|TT|, P=|T2|, delta=P/n, Q=N*m*b, and B=errorBracketSizeWindows(x,eps,n,N,P,m,b,k,aE). The definition delta2 at [GrowthBoundGivesRiemannHypothesis.lean:80–80](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean#L80-L80) was read in RH-26C-02. The actual coefficient is **Q*delta/2**.

The helper `CharacterBalanceMoves.core` at [ChCore.lean:336–342](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L336-L342) proves

```text
Q*(delta/2)*Y <= Err + 2*Q/x
```

from the host and weighted-size hypotheses, a bound on gapA and the weighted-character lower estimate hY. At [ChCore.lean:349–373](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L349-L373) it uses the two CostWindows clauses to bound the thick/thin replacement by 2b/x per term and sums over N*m terms. At [ChCore.lean:374–391](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L374-L391) it averages over A0 and cancels its positive cardinality; the remaining density factor is delta/2, not an arbitrary normalization choice.

The proof of `ch_core` sets G=GmA-SigA at [ChCore.lean:479–481](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L479-L481). The `one_char` argument ([ChCore.lean:255–334](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L255-L334)) and eventual threshold for the finite-character count/derivative remainder ([ChCore.lean:405–478](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L405-L478)) supply hY for Y=G-4*x^(1/2+eps). The main application at [ChCore.lean:493–495](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L493-L495) combines the core inequality with `proposition_size_bound`. With Err=x^(C*eps)*B this gives the actual source intermediate bound

```text
Q*(delta/2)*(G - 4*x^(1/2+eps))
    <= x^(C*eps)*B + 2*Q/x.
```

This is precisely the hypothesis shape of `GrowthSizeBound` at [GrowthBoundGivesRiemannHypothesis.lean:158–161](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean#L158-L161); `SizeWindows` is defined at [GrowthBoundGivesRiemannHypothesis.lean:148–156](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean#L148-L156). The actual proof constructs its SizeWindows witness using `size_windows_split` ([ChCore.lean:420–423](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L420-L423)). The name `proposition_size_bound` is a verified use-site; this run has not located its full supplying declaration/proof body.

Under the positivity and scalar size constraints, N,m,b,delta are strictly positive. In particular P>0 follows from delta>=x^(-eps)>0, and m>0 follows from its positive lower power bound. Dividing the displayed inequality by Q*delta/2 therefore gives the **exact normalized consequence**

```text
G <= (2/delta)*x^(C*eps)*R + 4/(delta*x) + 4*x^(1/2+eps),
R = B/Q.
```

This establishes where our RH-26C-02 normalization is used and what factors it omitted. The density cost is bounded by 1/delta <= x^eps, with two additive remainders that must survive any compressed derivation.

## 3. Independent paper proof of the source scalar exponent

The C-02 report derived, using the actual scalar size domain,

```text
R = aE/(m*b) + aE*m/(b*k)
      + (2*n/N)*m*x^eps + (P/N)*(k/n^2)*x^(2*eps)
  <= 2*x/m + 2 + 4*m*x^(9*eps/8) + 2*x^(1/2+9*eps/8)
  <= 10*x^(1/2+13*eps/8).
```

The source's own auxiliary estimates now inspected provide independent source corroboration of the four component constants. The helper `nT_bound` at [LipschitzWeightAndMinimum.lean:68–76](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L68-L76) gives n<=2*N*x^(eps/8). The four source lemmas `SZ.T1`, `T2`, `T3`, `T4` at [LipschitzWeightAndMinimum.lean:78–160](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L78-L160) bound the unnormalized bracket components by 2YQ, 2YQ, 4YQ, 2YQ respectively, for Y=x^(1/2+13eps/8) and the applicable size bounds. This confirms the constant 10 and exponent 13/8 at the per-slot normalization boundary. We have not read their final assembly into `proposition_size_bound`.

Here is a separate concise paper derivation of the final scalar bound. Let

```text
Z = x^(1/2+(C+21/8)*eps).
```

Because delta>=x^(-eps),

```text
(2/delta)*x^(C*eps)*R <= 20*Z.
```

Since C>=0, eps>0 and x>=3, x^(1/2+eps)<=Z and x^eps<=Z. Thus the two additive terms satisfy

```text
4*x^(1/2+eps) <= 4*Z,
4/(delta*x) <= 4*x^eps/x <= (4/3)*Z <= 2*Z.
```

It follows that G<=26Z. The actual source threshold in SizeWindows is 26<=x^(3eps/8). Consequently

```text
G <= 26*Z
  <= x^(1/2+(C+3)*eps).
```

This is the same **scalar conclusion** as the formal `GrowthSizeBound` proposition. The derivation uses exactly the scalar constraints and a one-sided input inequality. In particular the 3eps exponent arises through 13eps/8 for the bracket, eps for the density and 3eps/8 for absorption of the fixed constant 26. No assumption of nonnegative G is needed.

The final `core_gm` proof at [CoreGm.lean:64–65](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L64-L65) (prior RH-26C-01) calls `ch_core` with C=max(eD+eL,0)+3. It subsequently establishes eD+eL>=0 and uses the additional SigA term and a final x^eps factor at [CoreGm.lean:89–117](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L89-L117) to produce the observed exponent 1/2+(eD+eL+7)eps. We retain that remaining source step; the paper proof above only replaces the scalar bound conditional on its stated input.

## 4. Precise relation to the proposed two-term heuristic

The earlier normalized envelope R<=x^(13eps/8)*(4*x/m+6*m) now yields the source-compatible **power-loss** envelope

```text
G <= x^((C+21/8)*eps)*(8*x/m+12*m)
     + 4/(delta*x) + 4*x^(1/2+eps).
```

Here x,m and the finite-group cardinalities are still constrained by the actual family. It supplies a defensible interpretation of the two competing scales. The source imposes the square-root window for m; this proof does not construct a family by freely optimizing it. The counterexample in RH-26C-02 rules out a fixed-coefficient no-loss upper bound for the normalized bracket under its scalar restrictions alone, but it says nothing about whether a sharper estimate of an actual G or gap is possible.

## 5. Further source boundary and proposed independent Lean check

**Next RH-26E-03**: preregister an isolated MathCan Lean 4.35 / Mathlib 4.35 scalar proof of this actual error-bound pipeline. Freeze positive denominator and real-power conditions. Verify:

- exact normalization of the bracket and the two density-corrected additive errors;
- componentwise envelope bounds with explicit cardinality and size constraints (including natural m domain if using casts);
- the constant-10 bracket bound and 26Z absorption, with the real-power identities isolated into separate lemmas;
- adversarial controls for a zero density/denominator, omitted density cost, and a scalar family with growing no-loss ratio, or an exact finite parameterized obstruction sufficient to show why the missing factor matters.

A proof may use a factored positive power-scale abstraction (s=x^(1/2), p=x^eps, r=x^(eps/8), etc.) if every equality/ordering needed to derive the actual real-power statement is either kernel-proved in the module or explicitly listed as a hypothesis. Do not report the full real-power theorem as verified if only the algebraic abstraction passes. Use a pinned CPU-only workflow, exact theorem-name/axiom gate, and explicit result receipt.

**Optional separate RH-26C-04 source trace:** inspect `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:251–500` in a fresh bounded session to locate the full `proposition_size_bound` declaration and its assembly. The helper proofs are already located at lines 68–160, but we do not assume the final supplier lies in that next window. The quantitative theta multiplicity theorem remains a separate unsourced target.

## 6. Read receipt and limits

Six upstream source files at the frozen pin, **978 returned lines**. The direct ChCore continuation is complete. Additional scoped file/filename lookups were for the scalar supplier:

| Path relative to src/ | Window / lines |
| --- | --- |
| `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` | 251–499 (249; EOF) |
| `Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean` | 1–103 (103) |
| `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean` | 1–150 (150) |
| `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` | 101–176 (76; EOF) |
| `Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean` | 1–150 (150) |
| `Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean` | 1–250 (250; per-file cap reached) |

The ThickAverage and ChBalance windows corroborate the finite averaging and ramified-prime machinery, but are not additional proofs of the scalar bound. OneLeThresholdMulPowers concerns a separate prime-window parameter construction; it was not used to derive the result. Prior pinned source anchors for B, delta2 and core_gm were reused without another source read. The scoped 34-entry SizeWindowBrackets filename tree was inspected for navigation; no recursive full-repository source scan. No kernel compilation, full upstream build, GPU, QPU, paid compute or runtime/RAM measurements in this session.
