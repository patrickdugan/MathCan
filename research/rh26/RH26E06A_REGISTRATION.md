# RH26E06A registration: analytic conversion with retained cohomology

2026-11-24. Parent B16 148835a3678c1b19259dc6828688c2e28b118be6. Freeze before proof. Independent Mathlib-only scalar module. B16 source: DivinNOfHypV.lean:51–175, pinned c900e67c2fcd1fdb041685820bbd2b867fbc5a4b.

Let F>=1, q>=1, g>=1, b=q² (q=sqrt b), B0=F*q²*g, W=g*(B0+Nc), Nc>=0, z in [0,g], R>=0. Source rank equality has already substituted R=D0. Hypothesis eta<=R*(K*(g*B0+z*Nc)+V), V<=q.

Freeze eight declarations in RH26E06A:
1. exact_slack: eta<=R*(|K|*W+q-|K|*(g-z)*Nc).
2. cohomology_budget: q<=(1/(F*g²*q))*W.
3. refined_conversion: eta<=R*((|K|+1/(F*g²*q))*W).
4. delta_budget: if δ>=0 and 1<=δ*g² then q<=δ*W.
5. delta_conversion: same δ assumptions give eta<=R*((|K|+δ)*W).
6. eventual_delta: for eps,δ>0 there exists x0>=1 such that every x>=x0 has 1<=δ*(x^eps)². Use explicit x0=max(1,(max(1,1/δ))^(1/eps)). 
7. zero_extra_if_slack: if q<=|K|*(g-z)*Nc then eta<=R*(|K|*W).
8. zero_extra_control: explicit F=q=g=R=K=V=1,Nc=z=0,eta=2 witnesses failure of the exact K coefficient even though remaining scalar hypotheses hold.

The scalar certificate is conditional on rank, scale and cohomology assumptions. It neither realizes an arithmetic family nor proves any RH exponent. Require eight exact axiom reports (propext/Classical.choice/Quot.sound), Lean 4.35.0 Mathlib v4.35.0, CPU-only 25min isolated CI, preserve failed proof before repair. 
