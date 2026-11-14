# OVC-01: finite ordered-probe kernel bridge

Date: 2026-11-14. Companion to [Compactification Theory PR #133](https://github.com/MoralityLabAI/Compactification-Theory/pull/133).

The source pair is OpenAI Mathematics #116, rational matrix hitting points for bounded-size noncommutative formulas, and #135, homogeneous depth-five lower bounds for iterated matrix multiplication. The main campaign derives a conditional verification/compilation consequence and implements exact finite operator-order probes.

## Kernel-checked statements

MathCan/OrderedJet.lean imports Init. It verifies scalar multiplication commutativity and the generic integer cancellation

    (w*b+(w-1)*a) - (w*a+(w-1)*b) = b-a.

After multiplication by positive common denominators, this is the numerator used by the adjacent-swap Taylor coefficient proof. Unequal symbols give a nonzero signed difference. The full rational induction for arbitrary words is supplied in the companion THEORY.md and independently checked by exact Python across 3,282 cases.

The file also defines the explicit 4-by-4 integer matrices 24*T_1 and 24*T_2 from source #116. Lean checks that their commutator first column vanishes in rows 0,1,2 and equals -24 in row 3. Dividing the product by 24^2 gives the exact rational witness -1/24. A separate theorem checks that the commutator trace is zero. This exhibits a scalar observation that loses an error visible in the full first column.

Finally the module checks the numerical source formula dimensions 324 and 1014 used in the executed Python examples.

## Workflow and boundaries

The dedicated ovc01-ordered-jet.yml workflow builds the original MathCan library, directly kernel-checks this standalone file, and rejects sorryAx or ofReduceBool in its transitive axiom output. The main import file and the previous NHB branch are unchanged.

The source #116 completeness theorem, source #135 asymptotic gate lower bound, the general coefficient-rank proof and a trained neural compiler are outside this Init-only formalization. The Python campaign supplies exact finite certificates; its mathematical note states the stronger general deductions and their assumptions. No source theorem is represented as proved merely by this finite bridge.
