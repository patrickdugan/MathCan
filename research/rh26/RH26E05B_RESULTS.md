# RH-26E-05B: degree-weighted local rank and capacity slack

**Date:** 2026-11-24.  
**Registration:** [RH26E05B_REGISTRATION.md](RH26E05B_REGISTRATION.md), `1cd3ad275f4e76262403a959e56013272126123f`, before proof implementation.  
**Implementation:** [RH26E05BDegreeCapacity.lean](lean/RH26E05BDegreeCapacity.lean), `bd892f5c92467616ec64c4419bba5e7585454696`; source/workflow commit `5f3dc4471bdd28d9129e7b8ff1dea6f4a1cfe702`.  
**Disposition:** IMPLEMENTED; **KERNEL RESULT PENDING**. All twelve public names and axiom-print names match the registration. No admission or native_decide tokens found.

## Source connection and mathematical contract

B08/B10/B11 recovered the source local multiplicity caps, etaLoc inequality, etaJ aggregation and degree-normalized place weights. This independent module uses the corresponding nested finite sets as explicit premises rather than importing arithmetic source. It rederives the E04C weak dual inequality for arbitrary finite sets.

At each place w, let A(w) be its finite local index set and J(w,i) its finite good-point set. Define M(w,i)=sum_J m(w,i,p), with nonnegative m and valuation coefficient q<=E(w,i). The supplied pointwise premise etaLoc(w,i)<=sum_J m*q gives etaLoc<=M*E. Local caps M<=d and total rank budget sum_A M<=R produce the per-place bound

```text
B_w = lambda_w*R + sum_A d(w,i)*max(E(w,i)-lambda_w,0)
```

for lambda_w>=0. A common coefficient E<=U, U>=0 also gives etaJ(w)=sum_A etaLoc<=B=R*U, independently of the local caps.

The degree model uses L>=0, D>0, z_w>=0 and sum_W z_w<=D, corresponding to log(prime), field degree and ramification-inertia product. With alpha=sum_W z_w/D and a_w=L*z_w/D, the actual scalar weight normalization is sum_W a_w=L*alpha. The nested export target is

```text
sum_W a_w*etaJ(w)
 <= L*B - L*(1-alpha)*B - sum_W a_w*max(B-B_w,0).
```

This follows by using min(B,B_w) at each place and preserving the exact hinge identity. Both subtracted terms are nonnegative. The first is degree coverage slack; the second is local capacity slack. The local valuation coefficients may be signed; the common uniform upper bound U and multiplicities remain nonnegative. No arithmetic realization of these finite sets or weights is claimed.

## Registered declarations

| Name | Contract |
| --- | --- |
| local_mass_bound | Good-point weighted estimate to local mass bound |
| finite_dual_bound | Arbitrary finite capped allocation dual |
| place_capacity | Aggregate the nested good-point/local data to the per-place capped bound |
| uniform_place_bound | Independent source-style common coefficient bound |
| degree_coverage | Coverage in [0,1] under the degree budget |
| weight_normalization | Exact weighted degree normalization |
| coverage_slack_identity | Min-envelope exact two-slack identity |
| degree_weighted_bound | Weighted bound and nonnegative slack |
| nested_export | Full nested capacity/degree certificate |
| exact_fixture | One-place two-index example, bound attained |
| missing_cap_control | Mass shifted to high coefficient violates the capped bound without local cap |
| excess_coverage_control | Degree budget violation breaks uniform bound |

The fixture sets L=1, D=4, one place of degree mass 2, R=2, U=9, local caps (1,3), masses (1,1), coefficients (9,2), lambda=2. It has original envelope 18, actual capped weighted value 11/2, coverage slack 9 and cap slack 7/2. Both the feasibility and exact numerical equalities are registered. Without the first cap, masses (2,0) yield 18 against a local dual allowance of 11. A singleton z=2 with D=1 gives coverage 2 and violates the degree bound. These are scalar controls rather than exhibited arithmetic families.

## Pending verification receipt

- [Run 45340215014](https://github.com/patrickdugan/MathCan/actions/runs/45340215014), job 138261787386, checked `5f3dc4471bdd28d9129e7b8ff1dea6f4a1cfe702`.
- Source blob `d2065b5d031ca2715d3b297ca68ded0e93997cd7`, 245 lines; twelve exact registered theorem/axiom-print names. Checkout and pin/registration checks passed, Lean installation in progress at observation.
- Require successful compiler exit and exact twelve-name axiom allowlist, only propext/Classical.choice/Quot.sound; compiler, dependency and source hashes; elapsed time/RSS and artifact. Preserve failures before proof-only repairs.
- Isolated CPU Lean 4.35.0 / Mathlib v4.35.0 job, 25-minute timeout; no new upstream reads, full upstream/Deligne build, GPU/QPU or paid compute.

E05F separately passed its twelve-declaration audit during this session. Next inspect the E05B run; after its closure, choose B15 source inventory of N.linkN_of or separate stronger numerical supplier modules (E05C2). No improved RH or theta multiplicity exponent claim.
