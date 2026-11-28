# RH26E06D registration: signed rounding and DGam coefficient

Date 2026-11-24 Asia/Manila. Parent B25 db6b28109c4908efc481106de3cc3ed94d714f1d. Source SumLogPrimeFactorsLe:430–479, 636–730, 778–833 at upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Mathlib-only conditional scalar module, preregister before implementation.

Let S be a finite set, a_i>=0 for i in S, y_i real, gap(y)=y-floor(y), err=sum a_i*(floor(y_i)-y_i), active=S.filter(gap(y_i)!=0). Freeze ten public declarations:
1. floor_gap: 0<=gap(y)<1 for arbitrary real y.
2. signed_identity: err=-sum a_i*gap(y_i).
3. signed_bounds: err<=0 and -sum a_i<=err, under nonnegative weights.
4. active_support_bound: abs(err)<=sum over active a_i, using exact fractional part support.
5. integral_zero: if all y_i equal their floor on S, err=0.
6. strict_active_bound: with an active index of positive weight, abs(err)<sum over active a_i.
7. dg_product_8: n,N,X,x,l>=0, N<=X, l<=4*x implies 2*n*N*l<=8*(X*x*n). This mirrors source f=2n and log cap l.
8. dgam_log_8: for logGamma<=C*P, 0<=P<=8*Xpp, conclude logGamma<=8*abs(C)*Xpp. Preserve possibility C negative.
9. mu_gain: with fixed CT=2, Kold=2*(log4+5+10*abs(C)), Knew=2*(log4+5+8*abs(C)), exact difference 4*abs(C)>=0. This is the explicit LinkMu witness, not SlopesNF or K.
10. rounding_controls: singleton y=-1/4, weight 2, err=-3/2; integer y=-1 gives zero; y=3/4, weight 2 gives same signed loss -3/2. (Nonzero integrality and negative argument controls.)

Acceptance: ten exact axiom reports; propext/Classical.choice/Quot.sound only, no sorryAx, Lean 4.35.0 and Mathlib v4.35.0 CPU CI. Preserve any failed receipt and repair only proof syntax/bodies. No claim of arithmetic family realization or global theta exponent.
