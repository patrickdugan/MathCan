# RH26B17: VWin-to-HypV supply and global divisibility assembly

Date 2026-11-24 Asia/Manila. Registration 97c11db1a29dcc0340d224b3ac8e8ba2637a0688. Frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. **SOURCE PASS for the VWin-to-HypV adapter chain and the top-level LinkDIVt consumer.** Actual SmallLevelRankEq supplier and LinkDIVt internals remain open.

## 1. Cohomology window and arithmetic host

Reuse B16's exact VWinAt/VVle definitions from ExistsPageN:55–108. VWinAt supplies a character-field cohomology bound at cutoff floor(x^401) and B=sqrt(exp(x^eps)) on a common window. It is a substantive input, not derived by the adapter.

[SupplyChi.lean:46–54](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean#L46-L54) proves supplyChi: VWinAt psi 401 -> HostExW (3/2) (GChi psi).req, consuming admissibleClassesTwistedChar. [HostOfField.lean:50–65](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean#L50-L65) specializes supplyOfAdmOf with hostOfField, itself obtained from shortNorm and smallOne. Preserve the full host, rank, prime-pair, field-row and admitted premises in these suppliers.

[ShortNorms/supplyOfAdmOf.lean:55–177](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean#L55-L177) gives the actual proof:
- 66–98: fieldChi supplies c,e0; winPairs takes VWinAt and QH.pairEx, returning J and a common win; C0 dominates J, order and 8*psi.N. hSup, hAdm, eventually_rank_le_rpow_of_lt_one_div_fiftytwo supply x0A,x0B,x0T. K=5+4*psi.N, A=K^(5/eps); threshold x1 dominates these three thresholds, A^J and c*2^e0 strictly.
- 99–151: choose window data Y,q,d,e, force Y>=A, obtain pair hypotheses, q!=3, e>=e0, floor(Y^(eps/5))>=4*psi.N; construct field and frame with fieldChi and rank with hAdm, verify QS<=C0*n.
- 152–170: use hostOfField and retain explicit shares, admissibility, prime divisibility, and boundedTw. These yield the EAtH component with constant 4.
- 171–177: identify H.E as IsChiField psi e q d via isChiField and exact equality of e,q,d; hW.bound H.E hCF supplies VVle at floor(x^401). Apply VVle.mono, using t<=floor(x^401) via the eventual rank theorem. The final equality unfolds Scale.b, Scale.L and s.eps=eps. Thus **VVle H.E R.t (sqrt s.b)** retains the original budget without inflation. The body of winPairs and rank bound lemma are still uninspected in this pass.

The parameter 401 is a cutoff exponent. This source path supplies no new theta-lift multiplicity exponent.

## 2. Family transfer

[Supply.lean:50–83](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean#L50-L83) defines GChi psi as the conjunction of EAtH with constant 4 and VVle H.E t (sqrt b). The family class G.cls la includes the window property and G.At at every index above Fm.x1. FReq.at_of_from transports the host condition using field equality and finite-set image injectivity.

[ZeroFreeAllOfTopG.lean:52–74](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean#L52-L74) defines TopG. hypV_of_cls at 56–57 chooses threshold Fm.x1+1 and projects the second conjunct of GChi. eFamC_of_cls chooses coefficient 4 and the same threshold and transports scale x,eps. zeroFreeAll_of_topG uses TopG to obtain a connected family for each psi, pairs eFamC with windows and ChainTied, and invokes zeroFreeOn_of_tiedWin_cyc. This recovers the actual family adapter and direct terminal criterion; the deeper proof of that criterion remains separate.

## 3. Actual global consumer

[DesWin.lean:50–70](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean#L50-L70) proves topDesWin, conditional on nine Closed contracts (LinkN, LinkDIVt with TuSize/DGamSize, LinkEta, LinkIRR, SmallLevelRankEq, NuFullF and J.MuRank from ChosenE, LinkG, LinkS with TuSize, LinkGLOBAL with TuSize/DGamSize), DesignExists, and family-class transfer hypotheses. It takes the intersection via Closed.and, chooses a common epsilon cap min(eps1,eps3), one transported design bound K before choosing Fm, then obtains the nine properties from the same Fm and CH. The actual line 68 consumes exactly
    hD := aD hT hDG aE (divinN_of_hypV Fm h0 (hV Fm (h2 Fm hc.1.1)) aN aZ).
Thus SmallLevelRankEq aZ is essential to B16, and LinkDIVt supplies LinkDIV using LinkEta and DIVinN. Lines 69–70 pass LinkG, LinkS, LinkIRR, LinkDIV and LinkMu into LinkGLOBAL, with LinkMu itself supplied by J.linkMu_of_linkDIV using rank/fullness and mu-size premises. FamilyClassConnected returns the resulting eventual ChainTied witnesses.

This is a coefficient-existential boundary: replacing a numeric witness of DIVinN with a smaller witness does not change its Prop. To establish a quantitative downstream improvement one must inspect the actual LinkDIVt proof, preserving or exposing the witness dependency. No numerical gain past that boundary claimed.

## 4. Independent opportunities

E06A's retained sqrt(b) hypothesis is now connected from VWin through the family construction. The scalar result still needs successful CI and arithmetic integration. A future finite-budget adapter experiment can formalize monotone restriction of an exponent-indexed nonnegative prime/degree table: if finite prime-set sums through tMax are <=B, then every t<=tMax obeys the same B. Keep finiteness (non-top) distinct from the nonnegative sum bound. A stronger budget B' requires a certified omitted-tail lower bound, not just t<tMax. A concrete scalar control has all mass concentrated below t, so cutoff restriction leaves the total unchanged. No new executable module in this source pass.

## Receipt and next

Eight distinct upstream files, approximately 920 distinct returned lines (250 EveryCharacterOfLiteratureOfVWin, 74 DesWin, 135 DesignS, 87 Supply, 78 ZeroFreeAllOfTopG, 54 SupplyChi, 65 HostOfField, 177 supplyOfAdmOf); repeated focused windows add 105 lines, within 1200. DesignS declaration inspected as host/design boundary; no full source scan/build. No independent upstream kernel execution.

B18: inspect winPairs and eventually_rank_le_rpow_of_lt_one_div_fiftytwo for exact degree bound; alternatively prioritize actual SmallLevelRankEq supplier and LinkDIVt internals via TopG proof imports. B17 already recovered their exact consumer but not their proofs. E06A repair audit run 45365756795 remains pending. E05C4 arithmetic realization outstanding.
