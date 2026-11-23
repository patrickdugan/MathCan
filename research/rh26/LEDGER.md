# RH-26 run ledger

## RH-26B-02 — 2026-11-23 — Weil-theta integration / quotient structure

- **Status:** PARTIAL SOURCE PASS for operator and quotient definitions; **BLOCKED** on locating the *original* `WeilTensorModels.ThetaIntegralsAgree` and `WeilTensorModels.LocalMatching` declarations. No Lean kernel verification.
- **Pinned upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, with upstream `main` checked unchanged.
- **MathCan:** `research/rh26-extraction-rubrics-20261123` / [draft PR #265](https://github.com/patrickdugan/MathCan/pull/265). Source report [RH26B02_WEIL_QUOTIENTS.md](RH26B02_WEIL_QUOTIENTS.md), committed as `1338cbe040c3e8f61c533e8974208ae16246cef6`.
- **Read receipt:** **one upstream file**, 250 lines total: `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:251-500`. This follows lines 1–250 already inspected in RH-26B-01, with a separate session budget. No wider source scan.
- **Exact declarations reached:** `Rep` (251–253), `Model.IsGood` (273–279), `theta` (324), `Model.I` (326–327), `Model.Conv` (329–330), `Geo.IsGood` (398–408), `RealMaps` / `FinMaps` (434–455), `RealQuot` (463–469), `IsRealMaps` (471–484), `IsZetaAt` (486–494), partial `IsFinMaps` (496–500).
- **Mathematical information:** `theta` applies `thetaSum` to the Weil representation acting on `Φ`; `Model.I` integrates `theta` over a Haar fundamental domain, and `Model.Conv` requires integrability for each second-group argument. `RealQuot` demands full image of the polynomial submodule, Lie-derived vectors in the kernel, and invariance under specified compact actions. `IsRealMaps` imposes matched Lie/compact actions on the two maps, nontrivial common image, and irreducibility. `IsZetaAt` equates local quotient-image matching with equality of two local transforms, under additional standard-vacuum constraints.
- **Independent mathematical candidate (not run):** under a kernel containment `K ≤ ker p`, a linear map `p` descends uniquely to `S/K`. To apply this to theta integrals, one must prove the actual integrals annihilate the chosen action-generated subspace under convergence conditions. Label this as proposed RH-26E toy, with no extrapolation to RH.
- **Competing interpretation and falsifier:** a scalar theta-integral identity can hold while the proposed quotient fails compatibility with the Lie or compact action, or lacks a correct common irreducible image. Failure of any such requirement blocks operator-level compression.
- **Still unknown:** original `WeilTensorModels` premise signatures, exact theta multiplicity bound, `X/m+m` formula, full `IsFinMaps` structure, independent kernel audit.
- **Resource receipt:** read-only GitHub access. No local pretrained inference, GPU/QPU/cloud compute, Lean build, or CI. RAM and elapsed wall-clock not measured.
- **Next session RH-26B-03:** read the *same* pinned `WeilTensorModels.lean:501-750` as a single <=250-line window and record whether the two premise definitions appear, before any broader dependency scan.

## RH-26B-01 — 2026-11-23 — theta quotient comparison and two/three-prime local bound

- **Disposition:** SOURCE DISCOVERY PASS; elementary tensor-factorization **TOY PASS** (paper derivation only); quantitative theta-lift multiplicity **BLOCKED / UNSOURCED**; independent Lean kernel **NOT RUN**.
- **Upstream pinned:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, confirmed upstream main unchanged at session start.
- **MathCan:** branch `research/rh26-extraction-rubrics-20261123`, [draft PR #265](https://github.com/patrickdugan/MathCan/pull/265); research report committed `1df11ab97546c6665048b7735c275422398df017`.
- **Report:** [RH26B_THETA_LIFTS.md](RH26B_THETA_LIFTS.md). Read it for source links and complete theorem quantifiers before resuming.
- **Eight source files, 956 lines:** `LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean:1-90` (90); `LocalTypeDictionary/TwistedSquareLocalMatching.lean:1-127` (127); `ThirdPlaceSeries/BoundAtTwoThreeFamilyFon.lean:1-68` (68); `Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/ThetaIntegralsAgree.lean:1-84` (84); `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean:1-177` (177); `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoAndThreeForFamily.lean:1-78` (78); `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:1-250` (250); `LocalTypeDictionary/TripleExistsMatching.lean:1-82` (82). The unqualified `LocalTypeDictionary/` and `ThirdPlaceSeries/` names are under `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/`; other paths are under `src/`.
- **Theta source output:** `GlobalTheory.SquareSt.ThetaIntegralsAgree` (statement lines 73–80) gives a nonzero scalar comparing integrals modulo finite relations with convergence. `GlobalTheory.SquareSt.LocalMatching` (lines 60–71) gives surjective polynomial quotients and a compatible tensor-product factorization. `twisted_theta_integrals_agree` uses a seesaw matching and nonzero scalar product; `twisted_square_local_matching` uses an irreducibility/commutant step, finite Fock submodules, and `productForm`.
- **Arithmetic:** `BoundAtTwoThreeFamilyFonAlt` (bound file lines 62–65) is an eventual **conditional** family statement; `SetupAlt` requires rank/large/split constraints and a finite-Sha hypothesis. `BoundAtTwoThree` (definitions file lines 87–88) bounds `vcc` by `sPi` plus `midF`, `VVr`, `vhE`, `epsL` at selected twisted places 2 or 3. `midF(L,C)=C·f·m·b·log x+C·x^C·(large₂(L))²` (lines 68–69). No `X/m+m` bound was identified.
- **Critical type distinction:** the **upstream** predicates `WeilTensorModels.ThetaIntegralsAgree` and `.LocalMatching` were passed as premises; the inspected definitions are **outputs** in namespace `SquareSt`. The original premise signatures were not read in this session. First 250 lines of `WeilTensorModels.lean` only supplied background definitions.
- **Toy derivation:** over `ℂ`, identity quotient maps plus `e : ℂ ⊗ ℂ ≃ ℂ` and nonzero `c` yield scalar-matched bilinear evaluations on equal quotient representatives. Algebraically checked on paper; no automorphic content.
- **Null/falsifier:** theta-integral scalar agreement alone may fail to construct the common quotient, matching, or definite-side `HypsAlt` witness; an abstraction that discards these constraints fails the intended replacement test.
- **Next exact target:** fresh RH-26B-02 bounded session on the original declarations in `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean`, starting **after line 250**. Read at most 250 lines of that file this next session and record whether `.ThetaIntegralsAgree` / `.LocalMatching` appear. Expand to direct immediately named definitions only if found; continue under 8-file/1,200-line caps. Source-attribute all mathematical claims.
- **Resources:** read-only remote metadata + targeted source file requests; no full upstream build, CI, Lean kernel check, local CPU/GPU run, cloud pod, or QPU job. RAM and wall time unmeasured.

## RH-26A-02 — 2026-11-23 — theta/window interface gate

- **Status:** PASS (bounded static interface discovery); RH-26B multiplicity extraction **BLOCKED / UNSOURCED** until operator definitions and quantitative lemma are located.
- **Upstream:** `leanprover-community/riemann-hypothesis` SHA `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, checked against upstream main at session start.
- **MathCan work:** branch `research/rh26-extraction-rubrics-20261123`; [draft PR #265](https://github.com/patrickdugan/MathCan/pull/265); report committed as `aa919d19f7b3109d20b5fa367a273a1243464552`.
- **Report:** [RH26A02_THETA_INTERFACE.md](RH26A02_THETA_INTERFACE.md), with pinned source links, exact theorem signatures and a minimal cut diagram.
- **Eight upstream files read (708 total source lines):** `EveryCharacterOfLiteratureOfVWin.lean:220-322` (103), `SiegelEisensteinSecondTermHypotheses.lean:1-108` (108), `ExistsPageN.lean:1-124` (124), `TopPlug.lean:1-57` (57), `SupplyChi.lean:1-54` (54), `ZeroFreeAllOfTopG.lean:1-78` (78), `Hyps.lean:1-125` (125), `At23OfAll.lean:1-59` (59). Directory name metadata and exact Git refs were read, with no recursive full-repository scan.
- **Exact target:** `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` takes `P : UnitaryGroupThirdPlaceHypotheses`, `F : ThetaLocalInputs`, `hA : ThetaIntegralsAgree`, `hM : LocalMatching`, `hX : CovolumeBoundOfX`, `hL : RecTExists`, `hV : VWin` and concludes `UpperTheory.EveryCharacter`. The source is `SiegelEisensteinSecondTermHypotheses.lean:101-105`.
- **Intermediate witness:** `nonempty_hyps_definite_side_of_closed_bound` constructs `Nonempty HypsAlt` at `SiegelEisensteinSecondTermHypotheses.lean:76-100`. It uses matching/integals to build Fourier/test-vector grid witnesses, combines grid thresholds with `max CF0 CF1`, and consumes the covolume and linked local bounds. `HypsAlt` is a long dependent family structure. `At23OfAll.lean:55-57` supplies a linked predicate from a two/three-prime hypothesis.
- **Coherent window:** `OpenLiteratureStatements` at `EveryCharacterOfLiteratureOfVWin.lean:220-223` has two Galois-row fields and one local-Langlands field. `VWin := ∀ ψ, VWinAt ψ 401` (`ExistsPageN.lean:92`). It packages windows with `0<ε<1/52`, `[Y,Y²]` bounds, Tate–Shafarevich lengths, and an `x^401` cutoff. `TopPlug.lean:50-56` fixes window-width parameter `3/2`, then uses `supplyChi` and `imprimitive`.
- **Competing explanation/falsifier:** theta-integral and local-matching identities may be too weak to construct a compatible `HypsAlt` witness once the grid, volume, linked-bundle, and cohomological constraints are imposed. A proposed operator compression must provide this witness or explicitly retain it as a hypothesis.
- **Not yet established:** an explicit theta-lift multiplicity bound; definitions/normalizations of `ThetaIntegralsAgree` and `LocalMatching`; numerical meaning of `BoundAtTwoThreeFamilyFonAlt`; a `X/m+m` prime-sum theorem; independent Lean checks.
- **Compute receipt:** read-only GitHub and pinpoint web discovery, no local or cloud build, GPU/QPU run, CI job, or independent kernel check; wall time / RAM not measured.
- **Next fresh bounded run:** RH-26B source discovery: begin with `LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean` and `LocalTypeDictionary/TwistedSquareLocalMatching.lean`, and `ThirdPlaceSeries/BoundAtTwoThreeFamilyFon.lean`, all under `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/`. Extract the operator and matching definitions, their quantifiers and one exact inequality. Keep 8-file / 1,200-line cap, commit a separate receipt, stop.

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
