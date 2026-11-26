# DETFACT-04: exact relation lattice, bordered elimination and target multipliers

Status: independent conditional integer-lattice results; finite replay passed. Neither the full number-field relation producer nor effective coverage has been verified.

Sources: [Cogentic pinned theorem statements](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/README.md), [independent finite-certificate Lean file](https://github.com/lluiseriksson/cogentic-deterministic-factoring-certificates/blob/main/lean/CogenticDetFactoring.lean) (Theorems 14 and 15, the 2x2 bordered identity and the two-field sign cancellation). The following is independent elementary algebra, not a claim of novelty or a reconstruction of the inaccessible upstream PDF.

## 1. Relation matrix semantics

Let N>2 and u=(u_1,...,u_n) be units modulo N. Work in the abelian group G=(Z/NZ)^*/{+1,-1}, and let phi:Z^n -> G send a vector x to the class of prod_i u_i^x_i. Negative exponents require unit inverses. Let A be an integer matrix whose columns are *verified* relations, i.e., each maps to the identity under phi. Its column lattice L is contained in ker(phi).

For any integer witness w satisfying Aw=m e_i with m>0, u_i^m is a global sign modulo N, so u_i^(2m)=1 mod N. This is true for arbitrary rectangular A and does not require full rank. The final congruence can be checked directly. Merely having a full-rank integer matrix supplies no relation certificate. Local signs at different prime divisors need not constitute a global sign; one can work in the quotient by the full subgroup of square roots of unity instead, provided every relation is verified in that subgroup and its exponent-two property is justified. The present implementation uses global signs.

## 2. Minimal target multiplier in a square pivot lattice

Suppose B is an n-by-n full-rank submatrix of verified columns, D=det B, and c=adj(B)e_i. Then Bc=D e_i. Let g=gcd(|D|,c_1,...,c_n). Define m=|D|/g, w=sgn(D)c/g. Then B w=m e_i, yielding u_i^(2m)=1 mod N.

Moreover m is the smallest positive multiplier for which m e_i belongs to this *pivot* lattice. Proof: Bx=t e_i iff x=t c/D. Integrality is equivalent to |D| dividing every t c_j. For each prime q dividing |D|, the least necessary q-adic valuation of t is max(0, v_q(D)-min_j v_q(c_j)), with v_q(0)=infinity. This equals v_q(D/g). Thus the positive multipliers are precisely positive multiples of |D|/g. Equivalently m is the order of the class e_i in Z^n/BZ^n.

If B is a basis of the full relation lattice, this is the exact minimum for that lattice. If B is only a selected pivot submatrix, the full lattice can give a smaller multiplier. Even the full verified relation lattice need not equal ker(phi), so the multiplier need not be the actual signed unit order. The square pivot certificate is a sufficient relation witness.

Independent replay checks Bareiss determinants against recursive cofactor expansion, checks the adjugate identity, uses Cramer's rule with independent cofactor determinants for lattice membership, and tests minimality by rejecting m/q for every prime divisor q of m. Rejecting these suffices because the set of integer multipliers is a subgroup of Z.

## 3. General bordered Schur elimination

Write a verified square relation matrix in blocks

    A = [ B  u ]
        [ r  a ]

where B is k-by-k nonsingular, u a column and r a row. Set d=det B, v=adj(B)u and Delta=d*a-r*v=det A. Then

    A * (-v,d)^T = (0,...,0,Delta)^T.

Proof: Bv=d*u, so the nuisance coordinates cancel; the final coordinate is Delta. This generalizes the 2x2 identity in the independent certificate repository. If Delta=0, this construction gives a zero target multiplier and proves no nontrivial target certificate. If Delta!=0, divide the vector by its content g=gcd(|d|,v_1,...,v_k) and change sign if necessary. The positive multiplier becomes |Delta|/g. This is precisely the target-specific square-pivot multiplier of Section 2: the last column of adj(A) is (-v,d)^T, and g divides Delta by the displayed identity.

The identity alone does not construct the verified columns. The number-field step must justify each relation (including denominator localization, maps from the two fields, unit signs and rank); determinant algebra only eliminates already valid relations. A full rank test is an adequate algebraic gate after validation, but is stronger than necessary for any individual target. The rank-deficient matrix with columns (4,0) and (8,0) over units (2,7) modulo 15 isolates the first coordinate, while it cannot isolate the second.

For the two-field cancellation interface from the secondary verifier: if ell^E P=s1 mod N and P=s2 mod N with global signs s_i, then ell^E=s1*s2 mod N and ell^(2E)=1 mod N. The shared nuisance product must be *the same unit* in both congruences; matching coefficient vectors without justified common evaluation is insufficient.

## 4. Combining witnesses and controlling bit width

If several verified pivot certificates produce multipliers m_j for one target, gcd_j(m_j) is a valid signed annihilator. Bezout combines integer witnesses in the full column lattice, with zero coefficients for unused columns. This can improve on every individual pivot, though a gcd of selected pivots need not recover the minimum of the full lattice. Compute the gcd of positive multipliers before applying the factor two.

If |B_ij|<=A0, A0>=1, Hadamard gives |D| <= (sqrt(n)*A0)^n. Each adjugate entry has the corresponding (n-1)-dimensional bound. Hence the bit length of the determinant, cofactors and target multipliers is O(n(log n+log A0)). Bareiss fraction-free elimination (with nonzero pivot swaps) computes determinants in polynomial bit work in these parameters; computing n^2 cofactors by separate determinant calls remains polynomial. Modular validation of the original columns and final positive exponent also takes polynomial bit work in the explicit matrix and modulus sizes. The recursive cofactor implementation is solely an independent tiny-fixture oracle, not the claimed efficient method.

To feed DETFACT-02, emit the positive even exponent 2m per target prime, check ell^(2m)=1 mod N, and aggregate by lcm. Count distinct prime labels rather than pivots. The determinant bounds apply only once actual relation entries and dimensions are bounded. They do not settle how many matrices must be tried or how their columns are obtained.

## 5. Replay

Run node lattice_audit.mjs. Synthetic units over small odd composite moduli are used. The signed unit orders are exhaustively enumerated to seed valid columns, and random-but-deterministically-generated integer combinations form the pivot matrices. This oracle is not a relation discovery algorithm. Test dimensions are 2 through 4. The same function ran in the authoring JS runtime, generating lattice_receipt.json; Node was not separately invoked. It checks matrix validation, determinant replay, adjugate identities, Cramer membership, target multiplier minimality, bordered identity and gcd aggregation. Controls cover nonunits, false relations, singularity, nonglobal signs, rank deficiency and the distinction between a lattice multiplier and the actual group order.

## 6. Pending gates and handoff

DETFACT-05 should formalize and audit the abstract localization-to-relation map, with typed domains for integer exponent vectors, denominators, algebraic-unit relations and the common modular evaluation. Separate total modular witness checks from discovery. A certificate checker must reject a nonunit denominator or surface a proper divisor when gcd reveals one, reject incompatible evaluations and require nonzero target multipliers.

No upstream PDF or Lean companion has been retrieved. Lean is not installed in the current runtime, and no kernel-checked theorem is claimed. A formalization can start with the general bordered block identity and integral witness lemma, then add Cramer's minimality and bit bounds separately. For a reasoning gym use small synthetic, exact-verifier fixtures with unseen matrix sizes and rank profiles; do not use oracle relations as evidence of efficient discovery.
