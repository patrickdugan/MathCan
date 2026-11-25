# A short-cycle family excluded by the slope band

For every integer a>=2, set d=2^a-3. Then d>0, d=1 modulo4 and gcd(d,6)=1.
At the odd seed1 the branch numerator is3+d=2^a. Removing its powers of two
returns1, so F_d has a fixed point with

\[
(r,u,A)=(1,1,a),\qquad P=a+1.
\]

For a>=11, `(A-6u)^2=(a-6)^2>=25>22u`. The COL-03 candidate band therefore
excludes this actual unit-cycle pair at every such parameter. This is an
explicit infinite family of exclusions. Its short cycle is compatible with
the exact lattice, since `2^a=3 mod d`.

The theorem establishes a limitation of the heuristic selection rule. The
target in the pilot is the median period across all unit cycles. Determining
that median still requires the separate census. At the inspected d=4093
(a=12), the census gives median16 and the selected pair predicts5,176.

`pilot_diagnostics.py` recomputes error tails directly from the complete CSV,
enumerates the unit branch families at this worst case, and replays the fixed
point identities for2<=a<=20. The general argument is the displayed identity.
Its receipt labels this analysis as a diagnostic added after the first pilot.

COL-03B should include this arithmetic family when freezing fresh parameters
and report both typical and tail errors. The primary rule remains unchanged
so the original successes and failures remain reproducible.
