# AHR-QPU-04: routed non-Abelian holonomy order memory

This pilot follows the Q3 gauge-precision investigation. It is conditional, simulator-first, and uses no QPU allocation now.

Encode cube position on three spatial qubits (prime coordinates 2,3,5) and one internal mode on a fourth qubit. Use two square routes from vertex 0:
A = (0,1,3,2,0), B = (0,1,5,4,0).
On a directed link u→v use the unitary
T_uv(U) = |v><u|⊗U + |u><v|⊗U† + (I−|u><u|−|v><v|)⊗I.
It is a Hermitian involution on the full 16-dimensional space. The reverse traversal applies U†. Put exp(i αX) on 1→3 and exp(i βZ) on 1→5, with all other links identity.

The return to the base vertex is deterministic ideally. Starting the internal qubit at |0>, route order A then B applies W_B W_A, while B then A applies W_A W_B. For these Wilson operators,
D(ψ_AB,ψ_BA)=|sin(2α)sin β|.
At α=π/4 and β=π/2, the internal states are orthogonal with Y expectations −1 and +1, respectively. The offline verifier also tests reverse-route inverses and 20 seeded random angle pairs.

## Registered circuit study

- Establish an internal-only single-qubit comparator; this is a known noncommuting-gate effect. For the primary routed version, preserve eight explicit edge-link operations and the shared position state; no collapsing the route into one terminal qubit gate. Verify operator semantics and both paths at each step in simulation.
- Synthesize controlled link permutations/rotations on a connected four-qubit physical layout. Compare exact edge-block synthesis, decomposed conditional swaps and rotations, and any optimized layout. Measure spatial return, internal Y, and conditional order accuracy. Count failures to return in a joint endpoint rather than discarding leakage. Log native gate depth and duration, match or pad control sequences, and avoid reporting hardware efficiency from the shortcut.
- Use randomized balanced labels, equal circuit shot budgets, AB/BA, commuting same-axis control, identity, reversed loops, and inverse cancellation. Include same-link/no-flux controls, preparation/readout calibration, and a direct internal-only reference. Audit compiler removal of identity gates and compare actual depth/noise; do not assume perfect matched error.
- Use a blind held-out angle set and dwell-time sweep, and compare to a matched classical/order-register or direct gate baseline. The state is a single internal two-level memory with a finite operational readout. It is not evidence of consciousness or a complexity-class separation.
- Register proposed primary gate in simulation: mean joint correct-order-and-return probability ≥0.80 for the orthogonal fixture, Wilson/route sign correct, commuting control order difference consistent with zero, and robust intervals under independent held-out noise stress. Report spatial return separately and compare both label-conditioned probabilities. Use 95% binomial intervals and independent calibration/systematic allowance.

Hardware gate: HOLD. Compile and simulate using a verified current free-plan calibration and record a fresh exact manifest, including all controls, before asking for separate execution approval. No paid fallback. Do not infer a resource cap from the previous Q2/Q3 workload.
