# RH-26E-05C3: exceptional-prime numerical supplier

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26E05C3_REGISTRATION.md](RH26E05C3_REGISTRATION.md), `ba70096624a91e81e12db93a182685836874bd39`, frozen before executable proof.  
**Implementation:** [RH26E05C3Exceptional.lean](lean/RH26E05C3Exceptional.lean), `5e3d7882b16176eb743564944074688974dacf81`; source/workflow `2fe4079de5801949ac474c9c5be9771eecb61300`.  
**Disposition:** **KERNEL PASS (18/18)** on original implementation.

## 1. Source connection and scope

B11/B12 recover the exact exceptional-prime formulas and their scalar supplier estimates at frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b: NEqRZeroMulXPow.lean:257–321, ExportBoundOfAdmissible.lean:236–262,391–523,619–692, MemPrimesOverOfMem.lean:285–311, TwistedPlaces.lean:234–240. The independent module explicitly assumes the scalar counterparts of the recovered rank, cutoff, weight, logarithm and source count inequalities. No upstream definitions or proof modules are imported, no new upstream source reads or arithmetic realization.

Use H=Ub, g=large2, s=lStar, D=cutoff denominator and m the rank multiplicity parameter. The source provides s*D=m*b, s>0, m>=2, H>=m and D<=4H^7+6H^4. From H>=1 derive D<=10H^7. Preserve the exact ratio b/s=D/m.

## 2. Pointwise certificate

For l>=8 and l>=s, hB>=0 and hB<=2b, the cutoff relation yields

```text
hB/l <= hB/s <= 2*b/s = 2*D/m <= 10H^7,
hB/l² <= (5/4)H^7.
```

Using the source-supplied base-l logarithm estimate logb(l,hB)<=H+1 gives eP=C*(1+hB/l+logb(l,hB))<=13CH^7. The flat-length estimate follows from w<=9l (the source wP+eta3 bound and b'<l), Sc<=4H, g<=H, eta3<=4H and bandI<=1, eta3>=0:

```text
w/l + Sc + g + eta3*bandI <= 18H^7.
```

Using the source rank caps f,r<=2H, m,n,t,g<=H, nV<=4H² and nonnegative product factors, the original formulas give

```text
bbB=C*f*n*t²*nV*g² <= 8CH^9,
split lenB=(2fm+f)eP <= 78CH^9,
inert flat lenB=4f*(C*r*(hB/l²+flatB))+2f*(C*m*eP)
             <= (308C+52C²)H^9.
```

The original proof excludes the high-order small-prime branch for l>lStar via lA<lStar. That branch-selection fact is a supplied source premise here; pointwise_assembly takes the disjunction of the two appropriate length bounds. The polynomial P=316C+52C² gives the exact identity

```text
95(C+1)^2-P = 43(C-63/43)^2+116/43.
```

The least integer multiplier of the relaxed polynomial envelope is 95; C=3/2 falsifies 94. The combined pointwise estimate is bbB+lenB<=95(C+1)²H^9.

## 3. Count and finite weighted sum

The original exceptional count formula and cap assumptions supply

```text
#exc <= (#TT+2)*(Sc+3etaSz+t+8b/s+9).
```

With m>=2, exact b/s=D/m and the mixed-power D bound, the new count bound is

```text
#exc <= (2H+2)*(8H+16H^7+24H^4+9).
```

For H>=2, the two factors are bounded by 3H and (2457/128)H^7, respectively. Hence count<=(7371/128)H^8<=58H^8. This explicitly retains the H>=2 premise that follows from the source rank caps.

For positive l<=3b with log b<=H, H>=2, taking logarithms and using log 3<=2 gives log l<=2H. For finite T of natural numbers satisfying these positivity, size, count and nonnegative cost premises, and cost(l)<=95(C+1)²H^9, the exceptional_sum theorem gives

```text
sum_{l in T} log(l)*cost(l)
 <= 58*190*(C+1)^2*H^18
 = 11020*(C+1)^2*H^18.
```

The source big_le_b premise 4000000(C+1)²H^18<=b absorbs this term into (551/200000)b, as certified separately. No change of exponent is claimed.

## 4. Frozen declarations and controls

| Name | Target |
| --- | --- |
| cutoff_ratio | Exact b/s=D/m identity |
| denominator_envelope | Mixed-power bound implies 10H^7 |
| exceptional_divisions | Improved linear and quadratic denominator bounds |
| ep_bound | 13CH^7 |
| flat_bound | 18H^7 |
| bb_bound | 8CH^9 |
| split_length | 78CH^9 |
| inert_length | (308C+52C²)H^9 |
| exceptional_gap_identity | Exact square identity |
| exceptional_envelope | 95(C+1)² |
| exceptional_integer_minimum | Least integer multiplier 95 |
| pointwise_assembly | Combined pointwise 95 certificate |
| count_mixed_bound | Exact mixed-power count majorant |
| count_envelope | 58H^8 |
| prime_log_bound | log(l)<=2H |
| exceptional_sum | 11020(C+1)²H^18 |
| exceptional_absorption | (551/200000)b |
| missing_scale_controls | Counterexamples for missing H>=2 and m>=2 |

The count expression at H=1 is 228, exceeding 58. The other control uses H=2,m=1,s=8,l=9,D=1280,b=10240,hB=20480, retaining the remaining exceptional_divisions premises while violating its linear bound. The controls concern the relaxed scalar inequalities, not an arithmetic host.

## 5. Pending verification receipt

- [Run 45357956904](https://github.com/patrickdugan/MathCan/actions/runs/45357956904), job 138320417729, checked `2fe4079de5801949ac474c9c5be9771eecb61300`.
- Source blob `abc2d6556cfd03a5da0bbee5d98f15e5d1ccf4b2`, 293 lines; all eighteen theorem names match their axiom-print names. Checkout and registration/pin checks passed; Lean installation in progress at latest observation.
- Require successful compiler exit, exact eighteen-name axiom audit with only propext/Classical.choice/Quot.sound, compiler/dependency/source hashes, elapsed/RSS and artifact. Preserve failures before proof-only repairs.
- Isolated CPU Lean 4.35.0 / Mathlib v4.35.0 job, 25-minute cap; no full upstream/Deligne build, GPU/QPU or paid compute.

Next inspect the E05C3 run, preserve any failures and repair without changing frozen contracts. If passed, all three stronger numerical supplier groups for the independently verified E05C1 coefficient 105 have independent scalar certificates. A separate integration experiment must compose their exact contracts with the source five-mask assembly, and a source-compatible upstream theorem must still discharge the actual arithmetic premises. B15 N.linkN_of source inventory remains queued.

## Final kernel receipt

[Run 45357956904](https://github.com/patrickdugan/MathCan/actions/runs/45357956904), job 138320417729, success on original `2fe4079de5801949ac474c9c5be9771eecb61300`. [Artifact 14901969875](https://github.com/patrickdugan/MathCan/actions/runs/45357956904/artifacts/14901969875). Lean 4.35.0 compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source SHA-256 `5c9906aa42bcabd22d25c0f19654ceb4c992077a2df3c4c150eaabc4fc783b81`. Isolated Lean elapsed 7.75 s, user 8.43 s, system 2.94 s, max RSS 7,008,428 kB. Compiler exit and exact eighteen-name audit passed without repair. Earlier pending language is historical.

```text
'RH26E05C3.cutoff_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.denominator_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.exceptional_divisions' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.ep_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.flat_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.bb_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.split_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.inert_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.exceptional_gap_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.exceptional_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.exceptional_integer_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.pointwise_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.count_mixed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.count_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.prime_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.exceptional_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.exceptional_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C3.missing_scale_controls' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exceptional 95 pointwise, 58 cardinality and 11020 weighted-sum numerical certificates are independently verified under their registered scalar premises. All stronger numerical supplier groups for E05C1's conditional 105 assembly have corresponding independent kernel-verified modules (E05C2 and E05C3). A single composition across module contracts and source-compatible realization are separate tasks; no upstream theorem or improved global exponent is claimed. Next preregister the composition or B15 source trace.
