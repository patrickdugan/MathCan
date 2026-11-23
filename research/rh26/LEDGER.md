# RH-26 run ledger

## RH-26A-01 — 2026-11-23 — static top-level dependency trace

- **Status:** PASS (static source-trace acceptance only). **Not** a new independent Lean verification; deep theta/prime-sum extraction remains OPEN.
- **Upstream:** `leanprover-community/riemann-hypothesis` SHA `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b` (pinned).
- **MathCan work branch:** `research/rh26-extraction-rubrics-20261123`, draft PR [#265](https://github.com/patrickdugan/MathCan/pull/265); source-trace commit `bce04acfc00c8838f99bf527ac5825d80839473b`.
- **Protocol:** [EXPERIMENT_RUBRICS.md](EXPERIMENT_RUBRICS.md).
- **Report:** [RH26A_DEPENDENCIES.md](RH26A_DEPENDENCIES.md), including source hyperlinks and exact line anchors.

### Source-window receipt (8 distinct upstream files)

All relative to upstream `src/` at pinned SHA:

1. `Main.lean`, lines 1–56.
2. `Statements.lean`, lines 1–20.
3. `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`, lines 1–54.
4. `Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`, lines 1–132.
5. `Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`, lines 1–8.
6. `Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean`, lines 1–70.
7. `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, windows 1–230, 231–450, 750–840, plus one-line probes at 600, 700, 800, 850, 900, 950, 1000, 2000, 4000 (approximately 550 source-line requests).
8. `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`, lines 1–44.

**Approximately 934 fetched source-line windows** (empty probes included), comfortably below the 1,200-line budget. Read depth stayed within two direct import edges of `Main.lean`. The intermediate lines of the large theta module were intentionally skipped.

### Established evidence

`FinalTheorems.everyCharacter` feeds the nonvanishing proposition. `Claim.strip` derives critical-line zeros for all Dirichlet characters, and `Claim.zeta` derives RH; the primitive theorem is an immediate specialization. The deep assembly is `FinalTheorems.everyCharacter_of_row` → `LiteratureTheorems.every_character_of_literature_of_vWin` → `Lit.every_character_of_theta_integrals_local_matching`, with explicit package/automorphic-window, matching, published-result, positivity/volume, and local-Langlands inputs. The source-backed elementary analytic leaf is `Claim.factor_ne_zero` for `Re(s)>0` and prime `p`.

### Open obligations / falsifier

- `OpenLiteratureStatements`, `Top.VWin`, and the complete signature of `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` were **not inspected**. The theta-lift multiplicity mechanism remains unresolved.
- No pinned formal `X/m + m` prime-sum inequality was located; classify RH-26C as UNSOURCED pending discovery.
- Null: the theta bridge may be an interface requiring many substantial assumptions, preventing a compact replacement. A proposed extraction fails if an analytic, automorphic, volume, or local-global hypothesis is silently dropped.
- No upstream or MathCan build, CI run, new theorem, hardware experiment, or independent kernel check performed. Connector-only read; local CPU/GPU and QPU cost = none. Wall time / RAM use not measured.

### Precise resume point

Start with **only** this ledger and [RH26A_DEPENDENCIES.md](RH26A_DEPENDENCIES.md). Pin upstream SHA afresh; compare any change to `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`. Next run RH-26A-02 (or RH-26B discovery gate): locate the declaration of `UpperTheory.Lit.every_character_of_theta_integrals_local_matching`, which is called at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:833-839`. Inspect its exact signature, then only the definitions of `OpenLiteratureStatements` and `Top.VWin`. Cap at eight files / 1,200 lines / two further hops; write the next checkpoint, commit, and stop.
