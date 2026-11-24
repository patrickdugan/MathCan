# VPVNP-02I exact rank-one audit

Registration and 02H repairs: 3d90e38564fb0c6edb4b29f772a110328a0e4705.

Independent integer evaluation over all dual matrices n=0..4 found no violations. Outer products of nonzero vectors were enumerated and checked one-to-one against independently ranked actual matrices. Every character sum was evaluated directly, with a kernel-cardinality check on all n<=3 matrices and each n=4 diagonal representative.

| n | dual matrices | rank-one increments | kernel counts checked | signed sums by dual rank |
|---:|---:|---:|---:|---|
| 0 | 1 | 0 | 1 | 0 |
| 1 | 2 | 1 | 2 | 1,-1 |
| 2 | 16 | 9 | 16 | 9,1,-3 |
| 3 | 512 | 49 | 512 | 49,17,1,-7 |
| 4 | 65536 | 225 | 5 | 225,97,33,1,-15 |
| total | 66067 | | 536 | |

All agree with qZ-2q+1 where q=2^n, Z=2^(n-k). For n=0 the signed count is zero and the normalized rank-one probability is undefined; the Lean formula explicitly assumes n>0.

RankOneCharacter.lean proposes native declarations for unique outer products, rank-nullity kernel cardinality, signed count and odd parity probability. Native proof and Python regression CI pending. This phase does not yet certify the full sharp observer bound; 02J must compose these results with the Walsh energy identities.
