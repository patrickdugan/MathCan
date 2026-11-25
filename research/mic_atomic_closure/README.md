# MIC atomic closure: formal proof candidate

Source: [EvalMath MIC-05 draft #88](https://github.com/MoralityLabAI/EvalMath/pull/88).

The standalone Init-only module states and supplies proof terms for monotone support preservation, preservation across parallel deletion passes, greatest feasibility at stability, existence of a greatest block, and the integer maximum-gap row inequality.

For a feasible integer certificate 10p >= 10b+Mp with nonnegative M and row sums <= 9, if q <= p is feasible and q != p, let D = max_i(p_i-q_i) and S be the coordinates attaining D. The row lemma yields slack_i + sum_{j in S} M_ij >= 10 for each i in S. Since p_i >= D >= 1, S is a feasible unit decrement. Thus empty maximal unit closure is a minimality certificate once the finite least-point and row-to-block connection are established. The module proves the abstract deletion lemma and row arithmetic separately. Finite maximum selection, finite least-point existence, concrete matrix/list instantiation, finite termination and queue runtime are not yet kernel-formalized.

Scope: candidate Lean source, no local Lean executable and no network access to install it. Dedicated CI invokes the kernel and checks the reported axioms. The module remains outside the root import until kernel validation; this avoids triggering unrelated full-repository workflows. No claim of a compiled proof or of formalized time complexity.

Replay: lake env lean MathCan/MICAtomicClosure.lean
