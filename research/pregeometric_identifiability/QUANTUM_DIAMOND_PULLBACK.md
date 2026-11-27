# Quantum diamond: operational source blindness

Evidence: finite Pauli-support identities in MathCan/Pregeometry/QuantumDiamond.lean;
operator derivation below; no new QPU data. The proof is independent of Q3 curl.

Let U = CX(b,t) CX(a,t) CX(s,b) CX(s,a), with operators applied right to left.
CNOT conjugation maps X on its control to X on both wires, and Z on its
target to Z on both wires. Hence

    U† X_t U = X_t
    U† Z_t U = Z_a Z_b Z_t
    U† Y_t U = Z_a Z_b Y_t.

In particular U† (I_sab ⊗ O_t) U = I_s ⊗ B_abt for every target operator O_t,
by linearity and the single-qubit Pauli basis. If E_s is any local CPTP
map applied before U, its adjoint is unital. Therefore

    Tr[O_t Tr_sab(U (E_s ⊗ id)(rho) U†)]
      = Tr[(E_s† ⊗ id)(I_s ⊗ B_abt) rho]
      = Tr[(I_s ⊗ B_abt) rho].

This holds for every density operator rho, including initially correlated
states, and yields equality of reduced target states. It does not apply
to postselected, trace-decreasing source operations, or interventions
inside the circuit. The supplied Lean theorem checks the finite binary
Pauli-support pullback; the general operator/CPTP step above is a
mathematical derivation, not yet a Lean theorem.

## GHZ witness correction

For the unconditional reduced sab state, P = rho_000,000 + rho_111,111
and X = <XXX>, the two-setting lower bound is

    F_GHZ+ >= max(0, P + (X - 1)/2).

Proof: XXX swaps each bitstring with its complement. Let Q be the
projector onto span{000,111}; [Q,XXX]=0. The expectation of XXX on
the complementary block is at most 1-P. Thus
X <= 2 Re(rho_000,111) + 1-P; substituting in
F = P/2 + Re(rho_000,111) gives the inequality.
The old (P+X)/2 expression can certify the biseparable
state |+> ⊗ |Phi+> incorrectly (P=1/2, X=1).
Use valid confidence bounds and a detector model for noisy hardware.
The exact ideal state remains GHZ+ ⊗ |0>.

## Generalization target

For a connected finite cell complex, curl is the integer coboundary d1
on edges, with d1 d0 = 0. Over the reals, its residual unobservable
gauge-quotient dimension is dim H^1(X;R). On a phase torus the kernel
also depends on the integer invariant factors; Smith normal form
separates continuous null directions and finite phase aliases.
Q3's unimodular chord minors supply a torsion-free fixture.
The general SNF and operator-algebra theorems are future formal work.
