# RH-26 proof chunk inventory

Updated 2026-11-24. This is a navigable research index, not an exhaustive inventory of the upstream 175k-file proof. Preserve the frozen source pin c900e67c2fcd1fdb041685820bbd2b867fbc5a4b for the existing sequence. Observed consolidated upstream main: f38c099ec6017a3ce839cba4e06857eda6c9a057. Future source refreshes need explicit per-chunk pins and delta receipts. Each source session follows [EXPERIMENT_RUBRICS.md](EXPERIMENT_RUBRICS.md), max 8 files / 250 returned lines per file / 1200 lines aggregate / 2 dependency hops.

## Mapped chunks and independent math

| Chunk | Source boundary | Report | Mathematical opportunity / status |
| --- | --- | --- | --- |
| A: Final nonvanishing | Main.lean → everyCharacter → character boxes | [A](RH26A_DEPENDENCIES.md), [A02](RH26A02_THETA_INTERFACE.md) | Conditional dependency graph; independent analytic closure open |
| B: Theta representation comparison | WeilTensorModels, TheoremKOfMod, CtSmallCone | [B01](RH26B_THETA_LIFTS.md), [B03](RH26B03_ORIGINAL_PREMISES.md), [B04](RH26B04_SUPPLIERS.md), [B05](RH26B05_ENDGAME.md), [B06](RH26B06_RANK_STEP_PROOFS.md) | Two oriented rank-step identities, nonzero witness cancellation, well-founded rank descent. [E01](RH26E01_RESULTS.md) 6/6 and [E02](RH26E02_RESULTS.md) 16/16 kernel checks pass |
| C: Quantitative character balancing | ChTop, ErrorFormsWeakWindowsFalse, ChCore, SizeWindows | [C01](RH26C_PRIME_SUMS.md), [C02](RH26C02_ERROR_BRACKET.md), [C03](RH26C03_NORMALIZATION.md) | Density-normalized power-loss envelope and obstruction to a uniform no-loss envelope on scalar domain. [E03](RH26E03_RESULTS.md) 14/14 kernel pass |
| B-multiplicity: Local zero-space rank capacity | GoodPointMultiplicityLeRankProof.multLe_of_rank, LinkFam.main | [B07](RH26B07_LOCAL_CAPACITY.md), [B08](RH26B08_RANK_CERTIFICATE.md) | Exact MultLe proof and ConclF-to-LinkN consumer found. [E04A](RH26E04A_RESULTS.md): overlap accounting and both controls have clean first-run axiom reports; finite-supremum repair pending; E04B: scalar injection stability; E04C: weighted allocation dual |
| T: Level and coefficient transfer | MultiplicityBoundOfLocalComponents, LocalMultiplicityFamily | [B07](RH26B07_LOCAL_CAPACITY.md) | MoveToBase and localized MtFam preservation; inspect transfer domains and certificate composition |
| R: Local rank/containment | RankAtPlacesRec | [B07](RH26B07_LOCAL_CAPACITY.md) | Theta-lattice finite generation, eigenspace containment, paired local comparison; exact RankAtPlaces type and quantitative link open |
| I: Block-scalar theta injection | NandDIVb.theta_injective_of_scalars, At.Conclusion42 | [B08](RH26B08_RANK_CERTIFICATE.md) | Positive blockwise scalar composition gives injectivity under internal decomposition. Generic proof body still queued; candidate perturbation threshold and conditioning control |
| D: Arithmetic holonomy | matched quotient / rank-step transport versus finite-dimensional path operator | proposed D01 | Investigate compatible common fibers, normalization, nontrivial loops, and explicit obstruction; no claim that QPU verifies analytic result |
| V: Cohomological window budget | CharacterBoxes/ExistsPageN.VVle and VWin | [A02](RH26A02_THETA_INTERFACE.md) | Monotone cutoff/budget, finite prime-weighted local lengths, dyadic scale windows; investigate independent budget allocation inequalities |
| F: Character Fourier averaging | ChCore.sum_A, sum_Th, core; subgroup restrictions | [C03](RH26C03_NORMALIZATION.md) | Finite Fourier projector and multiplicity capacity; investigate perturbation bounds and false independence controls |
| S: Slope / thick-tail errors | QuotientSlopeBoundsWith, LevelOfCongruence, ErrWindows | [C02](RH26C02_ERROR_BRACKET.md) | Weighted slope gap, dimension-dependent error budgets; robust mean inequalities and exact counterexamples |

## Research queue

Next: inspect E04A repair run 45285673626, then close or repair under the frozen ten-declaration rubric. E04B block-scalar injection/robustness and E04C weighted allocation dual remain queued. Source inventory B09: inspect AdmittedStatementsOfLocalBoundsConclusion.lean (admissible table) and NandDIVa.lean (generic injection lead) in bounded chunks. E04A first audit failed on two dimension-proof errors; repaired theorem contracts unchanged, final gate pending. Other proposals remain paper mathematics. Other chunks: C04 exact proposition_size_bound supplier, D01 matched quotient operators, V01 cohomological budget, F01 Fourier projection, S01 slope bound. Each entry distinguishes source theorem, independent paper consequence, candidate experiment and kernel result. Never infer an entire theorem from a symbol name. Keep the quantitative theta-lift multiplicity exponent UNSOURCED until an actual source derivation and connection are found.

The latest run receipt and precise resume path live in [LEDGER.md](LEDGER.md).
