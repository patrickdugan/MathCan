# RH26E06G registration

Date 2026-11-24. Parent B30 aa315ff30424425267d2023b634924c3ff1c0238. Frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b, LipschitzWeightAndMinimum:64–162,282–367; E06F exact source hash 03c8568a09c43536fe7b502e4f059cd40da5a352263175af9e852daf3c959b2f and 10/10 receipt. Register before implementation. Mathlib plus audited E06F module only. Directly adapt original SZ suppliers and proposition_size_bound with original size hypotheses except remove hbig (26<=x^(3eps/8)); preserve actual bracket and growth inequality. Ten public declarations:
1. growth_unabsorbed: exact size premises with arbitrary C>=0, Err<=x^(C*eps)*bracket and original growth inequality give G<=26*x^(1/2+(C+21/8)*eps).
2. growth_margin: original size premises and 26<=x^(beta*eps), beta>0, yield G<=x^(1/2+(C+21/8+beta)*eps).
3. bracket_nonneg: original size premises imply bracket>=0.
4. split_size: with exact original size premises except Err cap replaced by E06F envelope H*V*bracket, H>=0, H<=x^(alpha*eps), alpha>0, eD,eL>=0, supply original size contract with C=max(eD,2,1+eL)+alpha using E06F.split_absorb.
5. composed_growth: split_size and growth_margin yield G<=x^(1/2+(max(eD,2,1+eL)+alpha+21/8+beta)*eps), preserving the original growth inequality.
6. composed_character: add independent Sig<=4o*x^(1/2+eps), Gm<=G+Sig, o>=0 and 1+4o<=x^(gamma*eps), gamma>0, obtain Gm<=x^(1/2+(max(eD,2,1+eL)+alpha+21/8+beta+gamma)*eps).
7. all_thresholds: explicit sufficient maximum of 3, max(1,H)^(1/(alpha*eps)), 26^(1/(beta*eps)), (1+4o)^(1/(gamma*eps)) guarantees the three caps for x at least that maximum, using E06F.explicit_threshold.
8. split_bracket_transport: abstract four-term bracket cap with Q>0,d>0, P>=0, x>0, terms <=2XQ,2Q,4YQ,2dZQ and Err<=P*sum, original scalar growth inequality implies G<=4X+(4PX+4P+8PY+4/x)/d+4PZ.
9. source_parameter_controls: max(2,2,1+0)=2, original coefficient 9, new margins (1,3/8,1) give 7, (1/8,1/8,1/8) give 5.
10. strict_margin_control: explicit x=1 with positive coefficient cap >1 cannot absorb that cap by a power; preserve threshold condition.
Accept exact ten public axiom reports plus recheck all ten E06F names in the same pinned toolchain. No sorryAx, only propext/Classical.choice/Quot.sound. Lean4.35/Mathlib v4.35.0, CPU CI. Separate source model/host obligations from scalar transport. No upstream edits or global theta exponent claim.
