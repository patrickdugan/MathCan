# Retained posterior mass and certified repair

Source and measured finite controls: https://github.com/MoralityLabAI/LoopedTransformers/tree/5c37c52532a5799f1c54e1279b532f8904e983ee/experiments/logrank_bpd_14.

Let H be a finite state space, L(h)>=0 an unnormalized posterior weight including prior, C a visited set with W=sum_{h in C} L(h)>0, P the full posterior, Q=P(.|C). Write alpha=P(C). On C, Q(h)=P(h)/alpha; outside C, Q(h)=0. Summing absolute differences gives ||P-Q||_TV=1-alpha. Consequently |P(A)-Q(A)|<=1-alpha for every Boolean event A. This is a conditional-likelihood truncation theorem, independent of which decoder proposed C.

A conservative upper bound U on the omitted weight produces alpha>=W/(W+U). If W_A=sum_{h in C intersect A}L(h), then

W_A/(W+U) <= P(A) <= (W_A+U)/(W+U).

Proof: write T for total omitted weight and T_A for omitted event weight. Then 0<=T_A<=T<=U. P(A)=(W_A+T_A)/(W+T). Minimize with T_A=0 and T=U; maximize with T_A=T and T=U. This provides a confidence interval without relying on consensus or residual size.

For a uniform finite binary quotient and independent noisy parity factors, a disjoint partition of the omitted states into prefix cells gives an admissible U by summing each cell cardinality times the product of its factorwise likelihood upper bounds (include the constant prior if it was included in W). Fixed factors use their known likelihood; unresolved factors use the larger likelihood. The bound may be loose. Split cells without double counting and keep their upper bound sum alongside exact scored states. Stop only when a requested probability interval or resource cap is reached. At present this is a mathematical design, not an implemented or tested bound, and no Lean compilation is claimed.

14 finite controls: at d=11, .15 noise, eight-frame repair retained mean .999994 posterior mass. At .35 it retained mean .935077; single-frame repair retained only .438225. Large dimensions have no measured exact omitted mass. The confidence gate cannot be certified from frame agreement alone.
