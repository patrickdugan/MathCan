# NOR-20: width-aware verifier bounds and cross-host performance interpretation

Companion pure mathematics for [NOR-20](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor20-crosshost-wide-coefficients-20261116/research/nor20_crosshost).

The applied benchmark replaces the original narrow RRC25 public input sources with four independent coefficient-width tiers (nominal 4, 8, 12, 16 bits) across dense, sparse, late-onset and rational families. It measures exact streaming, eager caching, native verification and four-output chunking on the same byte-identical public fixture on Ubuntu 24.04 and Windows Server 2025 x86-64.

A finite formal-series reciprocal recurrence may produce intermediate integers far wider than the nominal input coefficient bound. That makes a CPU resource estimate based only on the nominal generator width unreliable. The [MathCan/NOR20BigintWidthBounds.lean](../../MathCan/NOR20BigintWidthBounds.lean) theorem records a bound that uses the **maximum actually observed multiplication operand bit width** B in a finite inversion execution. For P multiplication sites, if each operand has at most B positive bit-length units, the sum of operand-bitwidth products is bounded above by P times B squared. The proof makes no claim that the nominal source width itself bounds all inverse coefficients.

The streaming verifier's four cached unary arrays are an abstract fixed workspace. Full eager caching can retain 32 extra public candidate-output arrays, while the pointwise implementation retains none. Under an idealized packed representation with n coefficients and at most b bits per coefficient, removing those 32 arrays saves exactly 32*n*b packed coefficient bits. The theorem proves that the saving grows monotonically with the actual coefficient size b; this quantity excludes Python object headers, query predictions, native allocations and allocator behavior.

Lean also confirms coefficient-by-coefficient equality against public finite lists is exact for arbitrarily large integers. The finite coefficient comparison semantics are independent of the coefficient magnitude. The earlier NOR-16/17 generator-family soundness premises remain necessary for a verified prediction to imply a true target future.

## First applied outcome

The new common fixture contains 64 exact public cases, sixteen for each nominal bit-width and family, generated under the source-only seed offset 94120000, source hash SHA-256:

    de7ed801e0e8708afebdbe3699d9074375b156795b40372eb77e2a4a13218c19

The first Linux x86-64 host measured a median native-to-streamed full CPU speedup of **4.382×** and median streamed/eager-cached peak Python allocation ratio **0.55063** across the 64 cases, with streaming using less traced temporary memory on all 64. The Windows x86-64 host obtained **4.331×** speedup and **0.55061** peak ratio, again lower memory for all 64. All five algorithms reproduced their own native full public acceptance mask and output-unanimity certificate for every case; both machines passed the preregistered ≥2× speedup, ≤0.80 memory ratio and 48/64 memory-win thresholds.

The wide_rational source family generated source inputs whose median maximum public-input bit width was about 2194 bits. Streaming remained advantageous under this distinct exact integer-width distribution. CPU runs on two operating systems do not prove independence of underlying CPU microarchitecture or generality to other machines. Per-host times and Python memory profiles are empirical evidence in Compactification-Theory, not kernel theorems.
