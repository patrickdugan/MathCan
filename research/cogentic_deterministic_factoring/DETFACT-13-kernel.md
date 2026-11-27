# DETFACT-13 kernel verification addendum

The original DETFACT-13 report and cost_summary.json are retained byte-for-byte. Their uncompiled status describes the local execution environment at the time of the experiment.

GitHub Actions subsequently compiled MathCan/DETFACT13Arena.lean with the repository's pinned Lean 4.35.0 toolchain. The standalone PR run [45920661534](https://github.com/patrickdugan/MathCan/actions/runs/45920661534) completed successfully, including the kernel compilation and axiom-marker check. The corresponding push run [45920655416](https://github.com/patrickdugan/MathCan/actions/runs/45920655416) and the original aggregate MathCan checks [45920661577](https://github.com/patrickdugan/MathCan/actions/runs/45920661577) also passed. The verified source blob is ac2a7c40ce43c826e7f3e5055f3f4d365fe5bb75 at commit 77afb14eecbf2e78987b90ca300bb7f88db18ce9.

The standalone workflow prints selected transitive axioms and fails if the specified admitted-proof or native-reduction markers are present. Run metadata confirms that step succeeded; this addendum does not independently assert a complete axiom dependency list.

The abstract module establishes the word count, conditional slice/access bounds, disjointness of adjacent slices, allocation endpoints, monotonicity in segment size, feasibility completeness of a minimum segment configuration, maximum domain arena bound, and 64-bit multiply-add bound. The subsequent integration imports this unchanged, checked module into MathCan.lean for ordinary aggregate builds. That integration requires its own CI result.

The scope is mathematical natural-number arithmetic under explicitly stated premises. The verified module does not establish the parser premises for arbitrary C inputs, C pointer safety, the complete Montgomery implementation, whole-process memory usage, or the original Cogentic relation-generation and complexity theorem.

The cost experiment remains a feasibility PASS and a speed FAIL. The selected structural scheduler always chose the 32-slot/16-bit configuration, so a prospectively tested static 16-bit tie-break is the appropriate next comparator. Keep the original measurements and frozen decisions unchanged.
