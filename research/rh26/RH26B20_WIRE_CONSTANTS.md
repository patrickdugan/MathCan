# RH26B20: exact arithmetic wire constants and threshold

Date 2026-11-24 Asia/Manila. Registration 5790dcd544f5ee9c9d4fda1c21a2497609fa87df. Upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. **SOURCE PASS for the exact c0F, ceF, x0F formulae and arithmetic consumer.** The final family bridge remains uninspected.

[ArithClauseRec.lean:49–56](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/LocalToGlobal/Divisibility/ArithClauseRec.lean#L49-L56) gives, with C0=c0F,
    C0=max(28,max(2*(1+abs(Cc))+1,max(1,Ch*(3+2*CYL+(max(Ct,5)+3))))).
    E=ceF(C,Ce,cD,C0)=max(C0,2*C+Ce+cD+3).
    x0F=max(max(16,(48*(max(Ct,5)+3)/eps+6/eps+2)^(6/eps)),
             max(3+abs(Cc),max(max(9,272+2*E),
               max(factorial(ceilNat((9*(max(Ct,5)+3)+2)/eps)),
                   factorial(ceilNat((max(CH,0)+1)/eps)))))).
At [60–100](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/LocalToGlobal/Divisibility/ArithClauseRec.lean#L60-L100), arithClause_rec needs the specified SizesAt, Del and etaSz identities, parameter/definition ties, finite T, DGamSize, C>=0, Ch>=0, and x>=x0F. Its conclusion passes E and C0 into NumFacts and RecNums, and Ce into divSize L Ce. The proof establishes C0>=28 and E>=C0, E>=2*C+Ce+cD+3; uses all individual threshold branches and calls numFacts_rec and arithAt_rec. These are real consumers of the input witness, not merely labels. Their internals remain a later bounded trace.

## Source-specific scalar simplification

By B19, Cwire=max(0,max(50*C0+10,60*E)). Because E>=C0>=28, 60*E>=50*C0+10 and 60*E>=0. Therefore Cwire=60*E exactly, for every source-valid C0, regardless of the signs of the other constants.

Fix C,cD,C0 and all other family data. For Ce_hi>=Ce_lo define A=2*C+cD+3 and T=C0-A. Then
    Cwire_hi-Cwire_lo
      =60*(max(Ce_hi-T,0)-max(Ce_lo-T,0)).
The gain lies in [0,60*(Ce_hi-Ce_lo)]; full gain when Ce_lo>=T, zero gain when Ce_hi<=T. A crossing gains 60*(Ce_hi-T). This is conditional on fixing the row witness C, DGam witness Cd (cD=2+9*max(Cd,0)), C0 and other data, since wire4F_alt also consumes the whole DIVinN predicate at other row premises.

For original and refined LinkN coefficients with input C_a>=0, use B16's actual source conversion:
    Ce_hi=2000*(C_a+1)^3+1
    Ce_lo=105*(C_a+1)^3+1.
Full possible wire improvement is 113700*(C_a+1)^3. A floor can reduce it to zero. If the E06A same-delta refinement is applied to both, their difference is unchanged. No upper ratio improvement is uniform independently of C0 and A.

Write Q for the maximum of all x0F terms other than 272+2*E. The exact threshold is max(Q,272+2*E); both E and x0F are monotone in Ce. Threshold reduction is at most 2*(E_hi-E_lo); this can vanish when factorial or rpow terms dominate. The full family threshold has additional maxima x1..x4 and can likewise mask the improvement. The coefficient improvement does not lower those terms by itself.

Scalar fixture: C=0,cD=2,C0=100,Ce_hi=100,Ce_lo=1 yields E_hi=105,E_lo=100 and wire gain 300, while raw Ce difference 99 would allow 5940. With C0=28,C=0,cD=2,Ce_hi=100,Ce_lo=40, both active and gain=3600. If Q=1000 in this last fixture, x0F does not change. These are abstract numerical controls; no actual host constructed.

## Receipt

One pinned source file, ArithClauseRec.lean:1–104, 104 returned lines. No new kernel execution or upstream edits. E06B: independent exact max-floor wire identity, monotonicity, sharp gain and threshold controls. Next B21: locate closed_linkDIVt_of_closed_bridge_kernel itself and the downstream divSize, remaining frame bound and global consumer. Rank inner theorem and zL still queued. Global theta exponent unsourced.
