# DETFACT-16 kernel verification receipt

The standalone Lean source at a9a61ebabea3d0169c3373ca8bdc7a0ee7c70c45 (blob 069679eb218625f0807423cac3d93f560af95280) passed the pinned Lean 4.35.0 kernel and axiom-marker gate. [CI run 45933185558](https://github.com/patrickdugan/MathCan/actions/runs/45933185558) also passed the independent Python roster replay.

The abstract theorem proves that a valid, unique and complete roster of maximal prime powers has product equal to the interval LCM. It derives prime-divisor existence and prime-power divisibility detection by elementary strong induction, then uses coprimality and the lcm universal property. It also verifies the subgroup-index saturation implication. Combined mathematically with DETFACT-15's independently verified product-preserving execution theorem, this supplies an exact specification of the full saturation stream. The odd-part filtering and two-adic splitting composition remain to be connected in a single Lean theorem.

Roster completeness is a semantic premise of the kernel theorem. The independent trial-division checker and segmented enumeration passed finite tests; the native C sieve is not formally verified. The full original Cogentic relation-generation theorem and its complexity guarantee remain unverified by this work. The source report's authoring-time candidate status is superseded by this receipt.

Next: formalize the unique maximal exponent and explicit odd-part/valuation composition, then return to the actual upstream number-field relation production argument when the source is available.
