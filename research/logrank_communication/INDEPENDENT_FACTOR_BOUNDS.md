# Independent parity-factor bounds and likelihood-weighted matroid selection

Source and finite checks: https://github.com/MoralityLabAI/LoopedTransformers/tree/4ba236bb3d79fd1d4ee62063998a6f501afe382c/experiments/logrank_bpd_15.

Let a prefix cell fix d out of R uniform binary quotient coordinates. For each nonzero residual parity mask a, group the remaining factors with that mask, incorporating the fixed-prefix sign into each observed label. Write g_a(0),g_a(1)>0 for the two group likelihood weights and F for fixed-factor weight. For an independent set I of residual masks, the linear map to their joint parity vector is surjective and each fiber has size 2^(R-d-|I|). Consequently the exact cell weight lies between

F * 2^(R-d-|I|) * product_{a in I}(g_a(0)+g_a(1)) * product_{a outside I} min(g_a(0),g_a(1))

and the analogous expression with max for all a outside I. This follows by pointwise bounding those factors and summing the independent factors over equal-size fibers. Grouped-factor bounds follow by taking I empty.

For homogeneous BSC noise u/(u+v), 0<u<=v, and adjusted counts n0,n1, the ratio of the smaller to larger likelihood is (u/v)^|n0-n1|. The multiplicative upper tightening from adding a factor to I is (1+(u/v)^|n0-n1|)/2; lower tightening is (1+(v/u)^|n0-n1|)/2. Maximizing the sum of log tightening weights on a linear matroid is solved by greedy in descending imbalance. Both objectives induce the same ordering, so this choice optimizes both bounds within this product-bound family. This says nothing about the globally best tree, arbitrary inference methods or time-matched superiority.

A disjoint prefix partition bounds omitted weight between L and U; visited weight W yields retained mass in [W/(W+U),W/(W+L)]. Bound event and complement weights separately to obtain L_A/(L_A+U_notA)<=P(A)<=U_A/(U_A+L_notA). Intersect this with the visited-weight interval. These are exact posterior guarantees conditional on the specified likelihood and prior; they are not per-instance correctness guarantees.

15 tested 3888 exhaustive fixture cells, with independent replay of 282552 primary and 94184 adaptive weighted cell bounds. Every audited weighted cell dominated the fixed independent-group bound. At width 48 and 15% noise, mean retained lower bound rises from .207754 to .233368, and the weighted search certifies .916667 target weight on one of four worlds. All high-noise conditions abstain. Four roots/width, adaptive 15B, no statistical superiority or Lean compilation. Next: factor-subgraph exact integration and mini-bucket bounds.
