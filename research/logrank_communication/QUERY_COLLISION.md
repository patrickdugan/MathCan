# LOGRANK-BPD-03: exact address-collision ceiling

Companion to MoralityLabAI/LoopedTransformers PR #404. Mathematical derivation, not Lean-checked.

For Index_k with uniformly independent binary memory coordinates, consider a deterministic Bob-output protocol whose first q bits are Bob-only and whose final bit is Alice-only. The hard query map partitions the k query coordinates into nonempty groups of sizes s_i. The Alice response can depend on all memory coordinates and the code, but cannot distinguish coordinates in one group by any additional query message.

For each group of s coordinates, Bob has two fixed reconstruction vectors u,v in {0,1}^s (the answer for each coordinate at the two possible final bits). Conditional on any memory vector, even an unrestricted Alice response cannot exceed the maximum of the two Hamming-match counts. Uniform memory makes the coordinates where u=v contribute (s-d)/2 in expectation, where d is their Hamming distance. The remaining d coordinates contribute d/2 + E|R_1+...+R_d|/2 for independent uniform Rademacher variables R_i. Thus the optimum for this pair of reconstructions is s/2+E|S_d|/2. Because E(|S_d+R| | S_d)>=|S_d| by convexity, E|S_d| is nondecreasing in d, and the optimum is reached by antipodal u,v at d=s. Alice's response can select the closer reconstruction, breaking ties deterministically. Therefore

F(s)=s/2+2^(-s-1) sum_{i=0}^s binom(s,i)|s-2i|.

A_max=(sum_i F(s_i))/k.

This is exact for the stated uniform task and communication schedule, allowing unbounded local computation. A neural protocol can lie strictly below this ceiling because of response/decoder errors. Group sizes refer to actual deterministic codes, not soft training distributions. It is not an accuracy bound for arbitrary nonuniform verifier matrices.

For s=1..8, exact maximum correct counts over all 2^s memory vectors are 2,6,18,44,110,252,588,1304. An independent exhaustive enumeration checked all possible distances d=0..s and all 2^s local memory vectors. Translation symmetry reduces every reconstruction pair to (0, a mask of Hamming weight d). No statistical inference involved.

Formalization queue: Rademacher expectation monotonicity by the two-term triangle inequality; two-reconstruction Hamming matches; finite uniform group averaging; construction of the optimal response map. Preserve Bob-only output semantics.
