# Lean companions in Metamath: CF-01

Explicit uncompressed proof certificates against pinned set.mm at 806509385370b29fe8b1723804777ac21b1ce194. Only scoped essential hypotheses and proved statements; no new axioms. Lean types are interpreted as sets and functions as set-coded graphs. Set-valued translations preserve the logical implication under that interpretation. Pointwise translations specialize universal premises; supporting lemmas and countermodel certificates are not complete ports. The manifest binds source blobs, exact premises, conclusions, proof sizes, and human statement mappings. The independent C/Python gate verifies certificates and source provenance, not automatic semantic equivalence of Lean and Metamath. Cryptographic binding remains a premise.

Reproduce: `python formal/metamath/verify.py /path/to/set.mm /path/to/mmverify.py /path/to/metamath /tmp/mm-ports --negative`. Both verifiers must accept the full database with the extension and explicitly reject the mutated final proof. C errors override any generic success footer. No existing Lean files changed.

Next: full ambiguity and authenticated-session proofs, then finite lists, arithmetic and recursive functions. CI pending at registration.
