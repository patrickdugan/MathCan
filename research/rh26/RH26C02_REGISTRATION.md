# RH-26C-02: registered error-bracket extraction

**Date:** 2026-11-24 (Asia/Manila). **Status:** registration before new source reads.
**Immutable upstream:** leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Observed main a78183e11ebfeebab77920b5e976f0a3edf1fc76; no semantic-equivalence claim.
**MathCan:** research/rh26-extraction-rubrics-20261123; draft PR #265.

Question: recover the actual expression errorBracketSizeWindows, its m-domain and its relation to the bounds consumed by core_gm. Does the registered C1 X/m + C2 m envelope follow under the source conditions, with uniform constants and a feasible square-root scale? Null: the expression contains independently varying cardinalities and scales, or the source constrains m differently; a superficial two-term resemblance does not prove the proposed envelope.

Start with src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean and ChTop.lean, then follow direct imports to errorBracketSizeWindows, RestSize and the size-window predicates. Max 8 distinct source files, 250 lines per file, 1200 returned source lines, two further dependency hops. Record exact windows, source links, types, positivity, thresholds, domain, dependencies of constants and one actual use. If the target formula or reduction is not established, label UNSOURCED/PARTIAL and record the next precise anchor. Do not equate an upper bound to an asymptotic equality. Any independent paper-algebra derivation must make its extra assumptions explicit. No new Lean kernel pass without a separately registered CPU check.

Deliverables: research/rh26/RH26C02_ERROR_BRACKET.md, LEDGER.md checkpoint, draft PR update. GitHub source reads only; no upstream clone/build, GPU, QPU, paid compute or copied upstream proof code.
