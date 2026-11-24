# QBTC-01: quantum authorization in Cryptomania

2026-11-24. Prospective study; no deployable Bitcoin primitive. QOBS-01/02 native-proof and exact-phase succeeded on f2bf1d14eb3978dd7b5433e0eee5eba24da3f119, Actions run 45395936583, jobs 138451598407 and 138451598855. QBTC-01 local execution: 19 named controls, 288 prefix-search cases, 4 exact discrimination cases. Independent replay pending.

## Public classical verification barrier (written conditional lemma)

Let pk, m and any public ledger context c be classical strings. Let V^O(pk,c,m,s) be a deterministic classical polynomial-time predicate, with candidate authorization evidence s of length bounded by a known polynomial L in the public input length/security parameter. Let the honest signing algorithm be arbitrary (including quantum or using private quantum states). Suppose for a fresh, signable m in a valid public context there exists accepted evidence. Assume P^O=NP^O, for precisely the classical oracle-access model in which V runs. Then accepted evidence is recoverable in deterministic polynomial time.

Proof: encode witnesses of length at most L at a fixed polynomial length by including their length and padding, and check canonical padding in the relation. Given a prefix p, the language of instances with an accepted witness extending p is in NP^O (guess completion, evaluate V). Under the collapse this language is in P^O. Test existence for the empty prefix; if yes, query whether the current prefix extended by 0 has an accepted completion. Choose 0 if yes, otherwise 1, preserving existence. After the fixed witness length ell, the resulting string is accepted. This uses at most ell+1 decisions and polynomial time. Completeness supplies existence for the target message; no signing query for that message or access to the private state is required. A ledger accepting this witness cannot distinguish its provenance using V. The statement is conditional on existence for a fresh valid message, public context, a polynomial bound and deterministic classical verification. It does not apply to secret verification keys, quantum verification states, quantum evidence, or an oracle whose needed verification access is outside the classical collapse model.

Source context: Kretschmer, Qian, Tal, "Quantum-Computable One-Way Functions without One-Way Functions" (STOC 2025), https://arxiv.org/abs/2411.02554. Their oracle separation permits quantum-computable cryptography with classical communication when classical P=NP. Classical messages alone do not entail classical algorithms for verification. This lemma concerns the stricter classical verification requirement.

## Authorization game

Public parameters: domain/version, network identifier, outpoint, authorization key identifier, sighash policy, transaction digest. The game assumes a fresh valid spend context (UTXO ownership and availability). The adversary may request signing for other messages, observe classical evidence and public ledger state, and submit a fresh-message witness. Distinguish ordinary message forgery, conflicting spend, same-ledger replay, same-network fork replay, and signing-resource exhaustion. Spending a UTXO invalidates further spends in the same ledger state; a competing fork sharing that UTXO may accept the same evidence. A validator does not learn the physical origin of an accepted classical witness. A signing budget is a liveness/resource assumption, not unforgeability.

The executable model uses a canonical JSON array of strings with strict schema, a PUBLIC finite acceptance table of 8-bit witnesses, and an ideal signing counter. The table deliberately exposes the complete relation; this is neither a signature scheme, a Bitcoin wire format, nor a model of quantum measurement. The digest is an opaque toy field. Signer exhaustion, domain binding and ledger checks are semantic controls only. A prefix-existence oracle recovers accepted evidence for fresh messages in nine queries on each satisfiable 8-bit example. It recovers a witness for an unspent outpoint even after the toy signer has exhausted its budget. The test makes no assumption that real-world P=NP or that an actual NP decision oracle exists.

## Discrimination bridge: exact countermodels

Let X be uniform in M_n(F2), independent of A uniform over rank r. Given only the shifted state rho_(X+A), its ensemble average equals the unshifted average for any encoding and any shift law independent of X, by translation invariance. This holds also when the entire observed object consists of k copies of that shifted state. Thus the single-ensemble rank-class discrimination advantage is zero even for a perfectly readable encoding.

For the phase family with uniform weights on all n^2-bit frequencies, the states form a full orthonormal Walsh basis indexed by X. A measurement identifies X with certainty. For any nonzero shift, squared HS energy is 2; the full/rank-one ratio is 1. When n>=2, given one state at X and one at X+A, measure both and recover A; the rank-class distributions have disjoint support and TV=1. This is a direct counterexample to deriving cryptographic hiding or rank-class indistinguishability from the observer ratio alone.

For uniform frequencies supported on one fixed row, Walsh states identify that row of X. Given the reference and shifted state, measure both rows; their XOR identifies the row of A. For full-rank A the row is uniformly nonzero by right GL_n invariance. For rank-one A=uv^T, with u,v uniform nonzero binary vectors, that row is zero with probability z=(2^(n-1)-1)/(2^n-1), and otherwise uniform nonzero. The binary factorization is unique. The two observed distributions have TV=z, and the squared HS energy ratio is 1/(1-z)=2(1-2^-n), i.e. sharp saturation despite perfect recovery of the encoded row. The joint averaged states commute in the relevant Walsh product basis, so this classical TV also equals their trace distance. Equal prior rank discrimination success is (1+TV)/2. Here n>=2 so the rank hypotheses differ.

Exact results:

| n | family | hidden single TV | reference-pair TV | HS energy ratio |
|---|---|---|---|---|
| 2 | full orthogonal | 0 | 1 | 1 |
| 2 | common row | 0 | 1/3 | 3/2 |
| 3 | full orthogonal | 0 | 1 | 1 |
| 3 | common row | 0 | 3/7 | 7/4 |

The checks enumerate actual rank-one and full-rank matrices. They compare exact rational TV and energies by integer cross-products. They prove neither oracle block-insensitivity nor the security of a quantum wallet.

## Next gate QBTC-02

Define separate authorization interfaces for (A) classical public verification with a retained computational hardness assumption (Shor-capable world), (B) classical evidence and quantum-computable public verification (Cryptomania oracle world), (C) quantum verification keys or quantum evidence. For each specify exactly what a node can reproduce, how a fork/reorg works, verification error, synchronization, key refresh, state availability and theft. Analyze proof wrappers: any universally sound, polynomial-length classical witness with a public deterministic polynomial-time verifier is itself subject to the above barrier in the collapse model, irrespective of whether it certifies a quantum computation. Treat honest-but-random quantum verification, QCMA/promise gaps, and witness extraction as separate proof obligations. Existing Bitcoin consensus, BitVM3 challenges and Nova commitments require independent assumption audits. No quantum security reduction is claimed. 
