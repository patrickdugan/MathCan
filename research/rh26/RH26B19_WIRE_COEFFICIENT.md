# RH26B19: quantitative wire and remaining divisibility bounds

Date 2026-11-24 Asia/Manila. Registration 7844db233ef9a842cdad349c73c79b20ace8653f. Frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. **SOURCE PASS for the explicit DIVinN coefficient consumer wire4F_alt; PARTIAL for closed_linkDIVt_of_closed_bridge_kernel and its final numerical envelope.**

## Actual explicit numerical consumer

[WireSel.lean:51–81](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/WireSel.lean#L51-L81) proves wire_sel_alt with Cabs=2, obtains DivRows3 via all tuple usage, DcPt3 via primitive realization, and exact base D0 rank equality via indefinite_realisation_base_rank_eq. It calls wire4F_alt with shared selected primitive realization data.

[Wire4F.lean:56–127](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Wire4F.lean#L56-L127) gives the actual wire proof. At 72–76 it extracts Ce,x3,hCe from DIVinN, Cd,x4,hFDG from DGamSize, C>=0,x1,row proof from hRows, x2 from hOne. Let c0=c0F(Fm.Csz,Fm.Cc,Fm.CYL,Fm.Ct), dg=2+9*max(Cd,0), E=ceF(C,Ce,dg,c0). At 77–81 it selects
    Cwire = max(0,max(50*c0+10,60*E))
    xwire = max(max(x1,x2),max(max(x3,x4),x0F(eps,Fm.Ct,Fm.Cc,CH,E))).
At 92 the proof also feeds hN itself to onto and fun0 row hypotheses; consequently numeric changes can interact with row suppliers and must not be treated as independent without holding their witness C fixed. At 98–110 gamma-size estimates and scale transport lead to arithClause_rec, explicitly consuming Ce and dg. At 113–127 it constructs the tied point via ptK_of_real_alt and inpAt_of_alt; the latter receives Ce and hCe(x,i). The larger constant and threshold are genuine proof witnesses. The precise meanings and formulae of c0F, ceF and x0F remain to be recovered from ArithClauseRec and its imports. No numerical monotonicity assumed here.

## Parallel use of DIVinN

[LinkBrest.lean:48–67](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkBrest.lean#L48-L67) supplies RemainingDivisionBounds via bRest_all_alt with Cabs=2.
[BrestFinalAll.lean:58–91](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BrestFinalAll.lean#L58-L91) constructs a closed FrameNumberBoundFamily implication from ComplementTwoFamily and DIVinN. It obtains CF0,hL,he from closed_funSharp_thr_alt and consumes he(hN) in hh_of_lvl along with local rank/fullness and mu-size suppliers. It combines this hh with buRat/rrFull and la_of into RemainingDivisionBounds. This is an independent use of the DIVinN predicate. Thus the arithmetic wire is a specific consumer, not a complete global bound; future numerical integration must inspect this branch as well.
[LinkTied.lean:89–105](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/GlobalSchurBounds/LinkTied.lean#L89-L105) transports the real-place second-layer condition to volume ties, tCVTies, and concrete forms with thresholds a, max(max(a,b),Fm.x1+1), max(a,b). RecBridgeWire:56–60 supplies eventual nonnegativity of La and ZeroAbove at Fm.x1+1. LinkDefN:61–66 defines zero_le_logWeight and TieTwRec, whose twisted-place support and mu!=mu0 conditions are explicit. DivisionAdmissibleFamilyOfData:56–76 supplies one_le_b, one_le_a, La_nonneg from the real scale and SizeQD; it contains no target closed_linkDIVt proof.

## New scalar opportunity

Once E(Ce) is known to be nondecreasing, for fixed c0,C,Cd and all other data, Cwire is nondecreasing. For Ce0>=Ce1 and E0>=E1, Cwire0-Cwire1 lies between 0 and 60*(E0-E1). More exactly let M=max(0,50*c0+10). Then Cwire=M+max(60*E-M,0), so the gain is max(60*E0-M,0)-max(60*E1-M,0). Both wires above the floor give the full gain, both below give zero gain, crossing gives 60*E0-M. For an abstract fixture M=100, E0=2,E1=1, the gain is 20 (not 60). This is a pure scalar conditional identity, not an upstream theorem or proof that the actual ceF is monotone. Threshold gain requires a separate x0F monotonicity certificate. No global exponent claim.

## Receipt and next

Eight distinct source files, 730 lines: LinkBrest 67, WireSel 82, LinkTied 109, BrestFinalAll 94, Wire4F 130, RecBridgeWire 64, LinkDefN 90, DivisionAdmissibleFamilyOfData 94. No full scan/build. B20: follow ArithClauseRec (direct Wire4F import) and its immediate imports for exact ceF/c0F/x0F and their numerical witness dependence. Continue locating the final family bridge and he(hN) branch separately. No source-compatible upstream E05C4 integration yet.
