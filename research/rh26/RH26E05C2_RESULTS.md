# RH-26E-05C2: small-prime and joint conductor certificates

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26E05C2_REGISTRATION.md](RH26E05C2_REGISTRATION.md), `beaf0e9306271adfca892d635bf66b9fbd50274c`, frozen before executable proof.  
**Implementation:** [RH26E05C2SmallRamified.lean](lean/RH26E05C2SmallRamified.lean), `af4b46414642a2a05c309a92258bfa2a099d65dc`; source/workflow `c4af3d063391b5174f849b5c5efc4d7287c2c9e1`.  
**Disposition:** IMPLEMENTED; **KERNEL RESULT PENDING**. Twelve public theorem names match the twelve audit commands. No admission/native_decide tokens found. E05B independently passed 12/12 on its original implementation before this registration.

## Scope and exact small-prime envelope

The source contracts are from B10/B13: frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b, ExportBoundOfAdmissible.lean:61–122,776–866; SmallSum.lean:106–158; DataParams.lean:63,186. The module independently implements the scalar consequences with source arithmetic component estimates as explicit premises. No new upstream reads/imports.

The six original small-prime component bounds have coefficients
```text
P(C) = C + 11*C*(3+2*C) + 80*C + 64*C + 32*C
       + 4*C*(102+4*(2*C+1)^2).
```
The module registers the expansion P(C)=64C³+86C²+634C and the exact identity
```text
104*(C+1)^3-P(C)
 = 40*(C-3/5)^2*(C+6/5) + 226*(C-697/1130)^2 + 4159/5650.
```
With C>=0 each right-side term is nonnegative. The least integer multiplier for this polynomial envelope is 104 (C=3/5 disproves 103). This claim concerns the relaxed scalar envelope, not actual attained arithmetic costs. For X>=0 and Y upper bounded by the six supplied original components, small_assembly proves Y<=104(C+1)^3 X.

## Factor-two small/3 row estimate

Let w_i be the logarithmic weights over a finite set, y=log x, A=x^C, g=large2, fm=f*m, and retain C,y,A>=0, fm,g>=1, (C+3)^2(1+y)^2<=g, A*g<=b, sum w<=2Cy+2. These are scalar counterparts of the source assumptions. The source prime-factor logarithm budget remains a premise. Setting B=2Cy+2, prove B(1+y)<=g, B<=g, B*y<=g² and B*A<=b. Then the two products of the constant per-prime cost with B are each bounded by C*fm*b*g². Hence
```text
sum_i w_i*(C*fm*b*y + C*A*g²) <= 2*C*fm*b*g².
```
This is the registered finite sum refinement of the source factor 8, including its intermediate scalar hypotheses.

## Joint conductor bound

Retain the original product inequality for real Q,q,d,t,b>=1:
```text
(Q*q*d)^36*t^150 <= b^(1/2), log b=g.
```
The proof applies the monotonicity of Real.log, log_mul, log_pow and log_rpow to derive the exact logarithmic budget
```text
36*(log Q+log q+log d)+150*log t <= g/2.
```
Thus log q+log d<=g/72-log Q-(25/6)log t<=g/72. A finite set of naturals with each element equal to q or d has log sum <=log q+log d, including when q=d. With the source scalar sign premises and g>=1, the ramified supplier becomes
```text
sum_l log(l)*(2*C*fm*b) <= (C/36)*fm*b*g
                        <= (C/36)*fm*b*g².
```
The relaxed real sharpness fixture takes Q=d=t=1,q=exp(g/72),b=exp(g),g>0. The missing-Q-factor control uses Q=1/2,q=2,d=t=b=1; it satisfies the product inequality but violates log q+log d<=log b/72. Neither fixture claims an arithmetic host realization.

## Twelve registered declarations

| Declaration | Target |
| --- | --- |
| small_polynomial_expand | Exact source envelope expansion |
| small_gap_identity | Sum-of-nonnegative-terms polynomial certificate |
| small_envelope | Coefficient 104 |
| small_integer_minimum | Least integer multiplier on scalar envelope |
| small_assembly | Six supplied component bounds imply 104 |
| row23_assembly | Factor-two finite weighted row bound |
| conductor_log_budget | Full product-power logarithm budget |
| conductor_pair_budget | Joint q,d logarithmic bound |
| pair_support_log_bound | Finite pair support, including coincident entries |
| ramified_assembly | Finite weighted ramified contribution |
| conductor_sharp_fixture | Exact relaxed scalar saturation |
| missing_conductor_factor_control | Necessary log Q sign control |

## Pending verification receipt

- [Run 45342577776](https://github.com/patrickdugan/MathCan/actions/runs/45342577776), job 138269479691, checks `c4af3d063391b5174f849b5c5efc4d7287c2c9e1`.
- Source blob `2df0aab209f9cb5e9cb3c2d0d17241eb09af9bdc`, 230 lines. All twelve theorem names match the audit list. Runner allocated, checkout in progress at latest observation.
- Require compiler exit zero, exact twelve-name axiom audit with only propext/Classical.choice/Quot.sound, source/compiler/Mathlib hashes, elapsed/RSS and artifact.
- Isolated CPU Lean 4.35.0 / Mathlib v4.35.0 job, 25-minute cap; no full upstream/Deligne build, GPU/QPU or paid compute.

Next inspect this exact audit. Preserve failures and repair within frozen contracts. E05C3 will separately register the exceptional-prime pointwise, count, mixed-power and finite-sum certificates required for the 11020 supplier. The already kernel-verified E05C1 conditional 105 assembly takes those stronger supplier bounds as premises. Even after independent component proofs, source-compatible integration and arithmetic realization are separate tasks. B15 N.linkN_of source inventory remains queued.
