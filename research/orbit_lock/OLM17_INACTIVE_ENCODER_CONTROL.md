# OLM-17: Feasibility and residual bounds for inactive-SAE-matched causal controls

November 16, 2026. Companion to [SMC-16](https://github.com/MoralityLabAI/Compactification-Theory/pull/177), building on the selective kill and tangent-sham geometry in [OLM-16](https://github.com/patrickdugan/MathCan/pull/97). The motivating measured SMC-16 result passes 3/4 registered primary comparisons, with its B501 SAE89 30-hole coverage failure retained. The mathematics below was written after that result and supplies prospective constraints for a separate SMC-17 experiment.

## 0. Exact-rational low-dimensional obstruction checks

Before the general proofs, the attached oracle tests dimensions at most six. Take d=5, protected four-row encoder A=(e1,e2,e3,e4), target covector a=e4, kill delta=e4, and tangent space T=span(e5). If the inactive matrix B contains e4, its clean-to-kill displacement is one and every tangent sham has zero displacement there: exact inactive matching is impossible. With B=I5, the squared best *unconstrained* inactive residual is 1; every equal-norm tangent sham s=±e5 has squared residual 2. For B consisting only of the row e4+e5, s=e5 matches both the inactive preactivation displacement and the physical norm. For B=e5, the zero sham exactly matches the inactive displacement but is the only feasible one, so equality of nonzero physical doses is impossible. With d=6 and B=e5, the extra e6 direction permits equal-dose exact matching. All statements are checked with Fraction arithmetic.

## 1. Feasibility of matching every inactive preactivation

Let A in R^(k×d) have full row rank and contain the target SAE covector a among the k active rows. A selective kill delta has protected other-row displacement zero and a·delta=q>0. A fully active-preserving sham s obeys As=0. The inactive physical encoder covectors form the matrix B in R^(m×d). The goal of an inactive-matched sham is

\[
 As=0,\qquad Bs=B\delta.
\]

Set T=ker A and b=B delta.

**Theorem OLM-17A (exact feasibility).** An inactive-matched sham exists if and only if b belongs to the subspace B(T). Equivalently, b is orthogonal to every vector in ker((B|T)^T). If B has full column rank, no such sham exists for any selective kill with a·delta=q>0.

**Proof.** The first condition forces s∈T; the second is the equation B|T(s)=b. This equation is solvable exactly for b in the image. If B is injective, Bs=Bdelta implies s=delta, contradicting a·s=0 and a·delta=q. QED.

Define the unavoidable inactive displacement discrepancy

\[
 \rho=\inf_{s\in T}\|B(\delta-s)\|
      =\|(I-\Pi_{B(T)})B\delta\|.
\]

**Theorem OLM-17B (sharp residual floor).** The displayed expression is the exact minimum over all active-preserving shams, including those with arbitrary physical dose. Every norm-matched sham has inactive residual at least rho. The floor is attained by a least-squares tangent sham. If B has smallest singular value σ_min(B)>0, then

\[
 \rho\ge\sigma_{\min}(B)\,\operatorname{dist}(\delta,T).
\]

**Proof.** Orthogonal projection onto the finite-dimensional subspace B(T) solves the Euclidean least-squares problem. For the last bound, use ||B(δ-s)||≥σ_min(B)||δ-s|| and minimize over s∈T. QED.

Consequently the entire 96-dimensional encoder preactivation displacement generally cannot be held fixed while selectively extinguishing just one naturally active coefficient. A minimax causal control has to report its residual inactive disturbance and feasibility conditions.

## 2. Exact inactive match with equal physical dose

Suppose an exact solution exists. Let s0 be its unique minimum-norm solution to As=0, Bs=b, and set K=ker A ∩ ker B. Every other exact inactive-matched sham has form s0+t with t∈K, and s0⊥K.

**Theorem OLM-17C (dose-matching criterion).** For prescribed dose r=||delta||, an exact inactive-matched, equal-norm sham exists if and only if

\[
 r^2=\|s_0\|^2
 \quad\text{or}\quad
 (r^2>\|s_0\|^2\ \text{and}\ \dim K>0).
\]

**Proof.** Squared orthogonal norms give ||s0+t||²=||s0||²+||t||². Nonzero K supports every nonnegative value of ||t||² by rescaling. If K=0 the exact solution is unique. QED.

The exact-rational oracle computes both feasibility and this dose criterion by solving independent row constraints and auditing the original full constraint system.

## 3. Quantitative causal attribution under incomplete matching

Let m be the receiving recurrent model's fixed-clean-rival output margin. Let the kill delta and tangent sham s have equal norm r, and suppose the Hessian operator norm of m is bounded by M on the two intervention segments. At the clean hidden state assume a specified first-order decomposition

\[
 \nabla m(h)=\alpha a+B^\top c+O^\top d+e,
\]
where O contains the other three protected active encoder rows, ||c||≤G, and ||e||≤E. The coefficient α represents a target-row contribution **only relative to this chosen decomposition**; it is not automatically unique when encoder rows are linearly dependent.

Let ε=||B(delta−s)|| and D=m(h−s)−m(h−delta).

**Theorem OLM-17D (nuisance-residual bound).**

\[
 \boxed{|D-\alpha q|\le G\varepsilon+2Er+Mr^2.}
\]

**Proof.** Two second-order Taylor expansions give D=∇m(h)·(delta−s)+R with |R|≤Mr², by OLM-16C. Since a·(delta−s)=q and O(delta−s)=0, the B-row contribution is bounded by ||c|| ||B(delta−s)|| and the residual gradient by ||e|| ||delta−s||≤2Er. QED.

This inequality makes the outstanding causal ambiguity measurable. An inactive-distance matched control alone provides ε; turning its positive output effect into a target-feature mechanism claim additionally requires defensible G, E, M bounds and identification of α. With a full-column-rank inactive B, the residual cannot vanish for a nonzero selective kill.

## 4. Implications for the next source-locked experiment

SMC-17 should archive all 96 physical encoder preactivation changes and the pre-outcome active/inactive feature partitions; report the exact least-squares residual floor rho alongside each actual equal-dose tangent sham's ε. A reproducible control may select a smallest-inactive-residual sham using *only* frozen encoder data, with the same original full-SAE reencoding guards. The search budget and any calibration procedure must be frozen before new Sudoku solutions are scored. Follow the earlier 64-puzzle cluster-bootstrap and coverage reporting without modifying SMC-16's gates.

Theorems A through C are finite-dimensional linear algebra, with exact rational d≤6 witnesses. Theorem D uses elementary Taylor calculus. **Lean scope:** A, C and the rational feasibility oracle admit straightforward finite matrix formalization; B needs orthogonal projection and singular-value inequalities; D needs real C² Hessian bounds. This note contains written proofs and executable Fraction regression witnesses, not Lean kernel certificates.
