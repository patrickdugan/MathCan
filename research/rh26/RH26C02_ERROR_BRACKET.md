# RH-26C-02 — exact size-window error bracket and normalized two-term envelope

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26C02_REGISTRATION.md](RH26C02_REGISTRATION.md), commit `6bf481c168469a027ee606f14871fa54db3b6f7d` before new source reads.  
**Frozen upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Observed upstream main:** `a78183e11ebfeebab77920b5e976f0a3edf1fc76`. No source-equivalence claim.  
**Disposition:** **FOUND** exact upstream error bracket, size-window domain and a proved gap bound consuming it. **PAPER-ALGEBRA PASS** for an independently derived normalized two-term envelope with an explicit epsilon-dependent power loss. **COUNTEREXAMPLE** to a uniform no-power-loss envelope for the normalized bracket under the displayed scalar domain alone. The originally hypothesized no-loss prime-sum error theorem remains **UNSOURCED**. No new independent Lean check.

## 1. Exact source expression

`Formalism.LFunctionChainParameters.LErr.errorBracketSizeWindows` is defined at [ErrorFormsWeakWindowsFalse.lean:117–119](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean#L117-L119). Let N=nT and P=nT2 denote the two natural-number cardinalities, n the ambient group cardinality, m the natural number of slots, and a=aE. For x>0 and n>0, its mathematical expression simplifies to

```text
B(x,eps,n,N,P,m,b,k,a)
 = N*a*(1+m^2/k)
   + 2*n*m^2*b*x^eps
   + m*P*k*b*x^(2*eps)/n^2.
```

This simplification uses the source denominator n*(n*x^(-eps)) and requires x>0 and n>0. The term involving m^2/k is retained. The source's preliminary bracket is `ErrText(D)=D.nT*D.a*(1+m^2/D.k)+m*(D.B0+D.Nc)` ([ErrorFormsWeakWindowsFalse.lean:62–65](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean#L62-L65)). The exponent `CErr(C)` is eDiv+eLoss+3.

The role of B is exact: `Deduction.ch_top` at [ChTop.lean:84–91](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L84-L91) states

```text
gapA(D,N_arg,ell,TT,a,w,tr(u))
    <= Dd.x^(CErr(C)*Dd.eps) * B(Dd.x,Dd.eps,n,|TT|,|T2|,m,Dd.b,Dd.k,Dd.a).
```

Here N_arg denotes the separate natural-number N in the source `gapA` signature. Its detailed interpretation is outside this read; it is distinct from our shorthand N=|TT|. The theorem requires `IdentU`, `SizeData₂`, `ErrWindows`, `BNBoundsU` and `LargeX` on the actual indexed family. The proof identifies the gap as Dd.ASK−Dd.Main, bounds its internal error by the power-scaled ErrText, then uses the cardinality bounds to compare ErrText to B ([ChTop.lean:92–105](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L92-L105) and [ChTop.lean:159–175](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L159-L175)). This is a **one-sided gap bound**, not an absolute error bound or a statement that B equals the gap. The previously inspected `CoreGm.lean:91–103` consumes this result.

## 2. The actual scalar window

The exact split of the `SizeWindows` domain appears in [SChain.lean:94–109](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/SChain.lean#L94-L109), with the corresponding equivalence proved by `size_windows_split` at [PChain.lean:54–57](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L54-L57). In particular:

```text
x >= 3,  26 <= x^(3*eps/8),  eps>0,  C>=0
n>0, b>0, a>=0, P<=n,
a <= 2*x*b,
N >= n*x^(-eps/8)/2,
P/n >= x^(-eps),
x^(1/2-eps) <= m <= x^(1/2+eps/2),
x*m <= k <= n^2*x^(1/2-eps).
```

In the separate source `ErrWindows0` predicate, [ErrorFormsWeakWindowsFalse.lean:74–87](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean#L74-L87), x>=1, 0<eps<=1, b>=1, x*b<=a, nT>=1, m's upper power bound, and x*m<=k are accompanied by 1<=k<=x^eK and k<=a, plus additional bounds on L, La, b', Xpp, cardinals and constants. `ErrWindows` adds a further inequality for etaBar and eBar at lines 89–91. The `LargeX` threshold at lines 95–98 imposes log x<=x^eps and KBig(K,cHH,eK)<=x^eps. `ConstsBound` at lines 69–72 bounds seven nonnegative coefficient constants by K. These are distinct named interfaces. We use the scalar SizeWindows split for the following independent algebra and retain the full `ch_top` hypotheses for any claim about its actual gap.

The square-root scale for m is already present as a **source-imposed window**. The result has not been shown to follow from freely choosing an integer m to minimize an unconstrained envelope. All family construction and existence obligations still apply.

## 3. New independent paper derivation: normalized envelope

Let R=B/(N*m*b). The scalar hypotheses above imply N>0, m>=1 (a positive natural number), b>0, n>0 and k>0. This normalization is a proposed per-slot scale, **not yet identified as the normalization used by the final Chebyshev consumer**.

For these positive denominators the exact identity is

```text
R = a/(m*b) + a*m/(b*k)
  + (2*n/N)*m*x^eps
  + (P/N)*(k/n^2)*x^(2*eps).
```

Apply the displayed scalar constraints:

1. a/(m*b) <= 2*x/m, since a<=2*x*b.
2. a*m/(b*k) <= 2, since k>=x*m.
3. (2*n/N)*m*x^eps <= 4*m*x^(9*eps/8), using N>=n*x^(-eps/8)/2.
4. (P/N)*(k/n^2)*x^(2*eps) <= 2*x^(1/2+9*eps/8), using P<=n, the same lower bound for N, and k<=n^2*x^(1/2-eps).

Consequently the exact paper upper estimate is

```text
R <= 2*x/m + 2 + 4*m*x^(9*eps/8) + 2*x^(1/2+9*eps/8).
```

The source upper bound on m gives sqrt(x) <= (x/m)*x^(eps/2). Since x>=1 and m>=1, this yields the uniform-coefficient **power-loss** envelope

```text
R <= x^(13*eps/8) * (4*x/m + 6*m).
```

The constants 4 and 6 are absolute; the common power loss x^(13*eps/8) is explicit and cannot be absorbed into a fixed constant at a fixed positive epsilon. This is a new independent paper consequence of the sourced scalar constraints, not a verbatim upstream theorem or a new kernel check.

The actual permitted m interval also yields a direct estimate without optimization:

```text
x/m <= x^(1/2+eps),
m*x^(9*eps/8) <= x^(1/2+13*eps/8),
R <= 10*x^(1/2+13*eps/8).
```

For the same eligible family instance, if all `ch_top` premises and these scalar bounds hold, dividing its one-sided gap bound by the positive N*m*b gives

```text
gapA/(N*m*b) <= x^(CErr(C)*eps)*R
              <= 10*x^(1/2+(CErr(C)+13/8)*eps).
```

No assertion is made that this equals Gm or replaces the original `ch_core` proof. In particular, the proof's character averaging, possible density normalization P/n, signs, remaining errors, and all family feasibility constraints still need to be recovered. If an additional division by P/n occurs, its inverse is bounded above by x^eps on this scalar domain; a direct source trace must establish whether that division actually occurs.

## 4. Concrete falsifier of a uniform no-loss envelope on the scalar window

Fix 0<eps<=1 and let integer t grow sufficiently large. Set

```text
x=t^2, m=t, n=N=P=t^2,
b=t, k=t^3, a=t^3.
```

These choices satisfy all the displayed scalar SizeWindows restrictions once t is sufficiently large: m lies in its power window, xm=k, a=xb, and k=t^3<=t^(5-2*eps)=n^2*x^(1/2-eps). The cardinality share and positivity restrictions hold. The threshold 26<=x^(3*eps/8) holds eventually. The additional scalar k<=x^eK is compatible with eK=3/2.

They are abstract positive scalar assignments, with no claim to realize all host or family data in `ErrWindows`, `SizeData₂`, or `IdentU`.

The nonnegative normalized terms give R>=2*t*x^eps, while x/m=m=t. For any fixed positive A,B0,

```text
R / (A*x/m+B0*m) >= 2*x^eps/(A+B0) -> infinity.
```

Thus the **normalized bracket itself** cannot satisfy a uniform no-power-loss upper bound A*x/m+B0*m from these scalar restrictions alone. This falsifies the proposed unconditional identification at this boundary. It does not falsify a stronger estimate of the actual gap (which may be smaller), a bound under stronger family constraints, or the upstream theorem.

The earlier conditional square-root optimization remains valid for the hypothetical two-term envelope (and for the power-loss envelope if feasible m is freely chosen at fixed x). With the explicit coefficients 4 and 6 the continuous envelope is minimized at sqrt(2*x/3), subject to the allowed domain. No assumption has been justified that such a minimizing m is realized by the actual family.

## 5. Remaining source obligations

- The actual `Deduction.ch_core` theorem and its final normalization have not been read. The current `ChCore.lean:1–250` window gives character-balancing helpers including the weighted thick/thin error at [ChCore.lean:128–134](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L128-L134) and movement estimates at [ChCore.lean:207–232](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L207-L232), but stops before the target declaration.
- The independently derived R estimate does not track all errors in `ch_core`. `CostWindows` at [SChain.lean:91–92](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/SChain.lean#L91-L92) contains explicit x-dependent controls, and [GrowthBoundGivesRiemannHypothesis.lean:89–99](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean#L89-L99) gives the averaged top excess and thin-scale/Lipschitz interfaces. The exact source division and all remaining factors must be located.
- `LevelOfCongruence.lean` and `QuotientSlopeBoundsWith.lean` also expose m²/k and weighted slope terms ([LevelOfCongruence.lean:60–74](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L60-L74), [QuotientSlopeBoundsWith.lean:58–81](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean#L58-L81)). These are subordinate error mechanisms, not separately established two-term prime-sum bounds.
- A genuine fixed-coefficient bound for the prime observable or its exact error, and quantitative theta-lift multiplicity, remain UNSOURCED.

## 6. Acceptance and next task

| Item | Disposition |
| --- | --- |
| Exact B definition | FOUND, ErrorFormsWeakWindowsFalse.lean 117–119 |
| Actual m-domain and scalar size constraints | FOUND, SChain.lean 94–109; equivalence PChain.lean 54–57 |
| Proved one-sided gap bound using B | FOUND, ChTop.lean 84–91, 159–175 |
| Independently derived normalized power-loss two-term bound | PAPER ALGEBRA PASS |
| Uniform no-loss envelope for the normalized bracket from scalar constraints alone | FALSIFIED by explicit scalar family |
| Exact final prime-sum normalization and two-term bound | PARTIAL / UNSOURCED |
| New Lean kernel check | NOT RUN |

**Next RH-26C-03:** preregister a fresh source-only read of `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:251–500`, continuing beyond line 500 in a separate session only if needed. Locate `Deduction.ch_core`, track the exact denominator and the contributions to its final exponent, then compare the independent normalized bound with the actual source inequality. After the source normalization is settled, preregister an independent MathCan Lean 4.35 check of the exact normalization, componentwise bounds, and scalar-family counterexample, with real powers isolated as explicit hypotheses where appropriate.

## 7. Read-budget receipt

Eight distinct frozen upstream Lean files, **1,199 returned source lines** (the cap was 1,200):

| File relative to src/ | Returned window |
| --- | --- |
| `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` | 1–250 (250) |
| `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean` | 1–179 (179) |
| `Formalism/SizeWindowBrackets/SChain.lean` | 1–111 (111) |
| `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean` | 1–180 (180) |
| `Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean` | 1–169 (169) |
| `Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean` | 1–125 (125) |
| `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean` | 1–85 (85) |
| `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` | 1–100 (100) |

The read bounds were selected before fetching each window. No full repository scan, clone, upstream build, new kernel run, GPU/QPU or paid compute. Runtime/RAM unmeasured. Prior report anchors were reused without rereading those source files.
