# NRF-02: graph-directed numerical-range contractions and guarded memory fibers

Date: 2026-11-15. Status: derived application theorem with human-readable proofs and exact-rational experiments. Global priority is not established.

## Inputs and prior art

- OpenAI math family #325, *A direct proof of the complete Crouzeix inequality* (2026-09-26), https://github.com/openai/math/tree/main/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026. The claimed complete Crouzeix constant-two inequality is used as a stated input. The Jordan witness admits an independent elementary proof.
- OpenAI math family #328, *Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces* (2026-09-24), https://github.com/openai/math/tree/main/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026. Motivates the nonexpansive backbone. A fixed period's unregularized nonexpansive composition has a periodic orbit under that paper's hypotheses; the regularized finite-dimensional theorem uses Banach contraction directly.
- R. D. Mauldin and S. C. Williams, *Hausdorff dimension in graph directed constructions*, Trans. AMS 309 (1988), 811–829. Graph cycle criteria, graph-directed attractors and dimensions are established subjects; path-complete Lyapunov methods also predate this result. The contribution here is a reproducible synthesis with numerical-range polynomial certificates and strict routing guards.

## NRF-02A. Rational graph-potential equivalence

Let G=(V,E) be a finite directed multigraph with nonnegative rational edge rates r_e, and choose a rational 0<alpha<1. The following are equivalent:

1. On every directed cycle gamma, product_{e in gamma} r_e <= alpha^{length(gamma)}.
2. There are positive rational vertex weights w_v such that r_e*w_source <= alpha*w_target for every directed edge.

Checking simple directed cycles suffices. Exact rational max-product Bellman-Ford produces a witness in at most |V|-1 synchronous relaxations initialized at w_v=1; the final edge comparison detects infeasibility.

**Proof.** Multiply the edge comparisons around a cycle, then cancel positive w_v to prove (1). Conversely set a_e=r_e/alpha and define w_v as the largest product over all simple directed paths ending at v, also including the empty path with product 1. For any edge e:u->v with positive a_e, append e to a maximizing path to u. Any repeated-vertex cycle has product <=1, so deleting it weakly increases the resulting product. The simplified path to v has product at least a_e*w_u, giving w_v>=a_e*w_u. If a_e=0 the inequality is immediate. Each simple path has at most |V|-1 edges; synchronous max-product relaxation finds exactly these maxima. Nonsimple cycles decompose into simple cycles, establishing the test reduction.

## NRF-02B. Nonnormal operator and disturbance transport

For a closed convex bounded C in finite-dimensional Hilbert space, each edge has a nonexpansive F_e:C->C, a nonexpansive G_e:H->C, a bias b_e, eta_e in [0,1] and the matrix-valued polynomial

    L_e = sum_k A_e^k tensor B_ek

with an independently certified q_e >= max_{z in W(A_e)} ||sum_k z^k B_ek||.

Set K_e(x) = (1-eta_e)F_e(x) + eta_e G_e(L_e x+b_e) and r_e=1-eta_e+2 eta_e q_e. The complete Crouzeix bound yields Lip(K_e)<=r_e. For any admissible path e_0,...,e_(T-1), NRF-02A gives

    ||x_T-y_T|| <= alpha^T (w_(v_T)/w_(v_0)) ||x_0-y_0||.

For per-step disturbances ||d_t||<=delta_t and initial error epsilon_0,

    epsilon_(t+1) = r_(e_t)*epsilon_t+delta_t

is a valid pathwise error certificate. In the weighted coordinate z_t=epsilon_t/w_(v_t),

    z_T <= alpha^T*z_0 + sum_{j=0}^{T-1} alpha^(T-1-j)*delta_j/w_(v_(j+1)).

**Proof.** Nonexpansiveness of F_e and G_e, with the Crouzeix bound, gives the local Lipschitz factor. Multiply edge potential inequalities along an admissible path and telescope vertex weights. The error recurrence follows from the triangle inequality. Divide it by the destination weight, apply local potential inequalities, and expand by induction.

### Exact guard theorem

Suppose a controller chooses between two outgoing edges by the sign of a linear guard s(x)=ell(x)-theta, with a fixed tie-breaking rule. If the nominal trace x_t is known and at *every* routing decision

    s(x_t)^2 > ||ell||^2 * epsilon_t^2,

then every perturbed trace satisfying the initial and stepwise error budgets selects the same edges through that decision horizon. The strict inequality is checkable with rational arithmetic.

**Proof.** Cauchy-Schwarz gives |ell(x_t)-ell(xhat_t)|<=||ell|| epsilon_t. Strict guard clearance preserves the sign, and thus the selected edge. The usual edge Lipschitz bound inductively supplies the next epsilon_t.

**Branch-flip counterexample.** For the app's idle/probe/audit graph, alpha=3/4 and weights (1,2,4/3) certify all shared-route paths, even with a sampling edge whose bound is 3/2. The nearby initial states (1/1000,1/2) and (-1/1000,1/2) select different edges at the sign guard. Their one-step squared-distance amplification is exactly 20527009/144. A graph certificate alone therefore gives no incremental continuity for a state-selected policy with ambiguous guards.

## NRF-02C. Memory-fiber covering envelope

Assume additionally that C is compact in R^d, that every edge map takes C into itself, and that a positive potential exists. Put D=diam(C), kappa=max_v w_v/min_v w_v, and B=max_v(outdegree(v))>=1. Every length-k admissible path maps C into an image of diameter at most D*kappa*alpha^k. There are at most |V|*B^k such images. For every infinite admissible *past* history, the images of C under its longer and longer suffix compositions are nested, nonempty compact sets with diameter tending to zero, so their intersection contains a single point. Let A be the set of all these history-coded points. If A is nonempty, its upper box dimension obeys

    upper_dim_B(A) <= min(d, log(B)/(-log(alpha))).

**Proof.** The path Lipschitz inequality gives the image diameters. A longer past suffix supplies an additional selfmap of C at the innermost end, so the images are nested. Their diameters vanish and compactness gives a singleton intersection. Count starting vertices and outgoing choices to cover all coded points by <=|V| B^k suffix images. Compare the logarithms of covering counts and diameter scales as k increases, and include the ambient dimension bound. This is a graph-directed IFS-type result, not a novel standalone dimension theorem.

## Exact audits and limits

The independent oracle is research/compactification/graph_switching.py. Six unittest methods test 256 two-node and 729 three-node graphs by independent simple-cycle enumeration, exhaustive weighted path comparisons, 1,296 perturbation recurrences, strict hyperplane equality, and cover counts. MathCan/GraphSwitching.lean proves the cross-multiplied **two-edge arithmetic lemma** using only Init. Its kernel checking does not formalize the full graph equivalence or analytic norm bound.

The paired application is in MoralityLabAI/LoopedTransformers PR #56. It uses rational 2x2 Jordan matrices with exact numerical-range disks. Native neural weight bounds, guard provenance, and improvement in benchmark capability remain open experimental questions. Published global novelty remains subject to literature audit.


## NRF-02D. Barycentric graph fixed points and smooth selection

This section uses both selected OpenAI papers directly. Its fixed-point existence claim is **conditional on** the general reflexive-space theorem of OpenAI family 328; it also follows classically in our finite-dimensional toy by Brouwer. The rest is an independently proved conditional comparison theorem.

Let X be a real reflexive Banach space, C a nonempty closed bounded convex subset, and V a finite nonempty vertex set. For every directed edge e:u->v choose a nonexpansive backbone F_e:C->C. Fix nonnegative incoming probabilities pi_(v,e) that sum to one across all edges terminating at v. On the finite product C^V with its sup norm, define

    (T0(x))_v = sum_(e:u->v) pi_(v,e) F_e(x_u).

Each coordinate is a convex combination of points in C, so T0 maps C^V into itself. Its sup-norm Lipschitz constant is at most one, because the F_e are nonexpansive and the probabilities are row-stochastic. Finite products of reflexive Banach spaces remain reflexive under the sup norm. Hence the theorem claimed in OpenAI family 328 supplies a fixed point of T0. This is a **barycentric network equilibrium**: it need not satisfy the stronger edge-by-edge simultaneous consistency equations, which can be incompatible.

### Crouzeix regularization and exact Perron witness

Replace each F_e by K_e=(1-eta_e)F_e+eta_e G_e(L_e x+b_e), with the same Crouzeix-certified rates r_e as NRF-02B, and define the nonnegative comparison matrix

    M_(v,u) = sum_(e:u->v) pi_(v,e)*r_e.

For any x,y, the componentwise distances obey d(Tx,Ty) <= M*d(x,y). If positive w satisfies Mw <= alpha*w for some alpha<1, T contracts in the weighted product norm ||x||_w=max_v ||x_v||/w_v. Therefore T has a unique fixed point and globally convergent iterates.

For **nonnegative rational M**, the following are equivalent:

- its spectral radius rho(M) is strictly smaller than one;
- there is a positive rational w with Mw<w;
- (I-M)w=1 has the positive solution w=(I-M)^(-1)1.

For rho(M)<1, the Neumann series ensures w>=1, and Mw=w-1<w. Conversely Mw<w yields alpha=max_v (Mw)_v/w_v<1, and the weighted norm bounds the spectral radius by alpha. Gaussian elimination over Q gives a checkable rational witness. This is a standard positive-matrix criterion, incorporated here as a certificate for nonnormal recurrent polynomial updates.

**Exact example.** A single vertex has two self-loops, with rates 3/2 and 1/4. An arbitrary hard schedule repeatedly taking the first edge is not pathwise contractive. Their fixed-probability mixture pi=(1/4,3/4) has M=(9/16), so the averaged map is a contraction with rate at most 9/16. This statement concerns the *averaged operator*, not arbitrary stochastic sample paths.

### State-dependent soft routing

Suppose each target v chooses incoming weights pi_(v,e)(x) that remain nonnegative and sum to one, with

    ||pi_v(x)-pi_v(y)||_1 <= L_v ||x-y||_w.

Let D=diam(C), and assume a uniform comparison bound

    sup_x sum_(e:u->v) pi_(v,e)(x)*r_e*w_u <= R_v*w_v.

Then the resulting soft-routed T has weighted Lipschitz constant at most

    max_v [R_v + D*L_v/(2*w_v)].

**Proof.** Expand T_v(x)-T_v(y) into the changes of K_e at fixed pi(x) plus changes in pi at fixed K_e(y). The first term is bounded by R_v*w_v*||x-y||_w. For the latter term, the coefficient differences sum to zero. Their positive and negative masses are each exactly half their L1 sum. Those two normalized convex combinations of points in C are at distance at most D. The route-change norm is therefore bounded by (D/2)*L_v*||x-y||_w. Division by w_v and a maximum over vertices finishes the result. If the stated bound is below one, Banach contraction gives a unique globally attracting soft-routed fixed point. Hard sign guards lack a finite global routing-Lipschitz constant at their decision boundary, as NRF-02B demonstrates.

**Exact smooth example.** In C=[-1,1]^2, use high-gain 3/2, repair-gain 1/4, and p_high(x)=1/4+x_0/16. Then 3/16<=p_high<=5/16, and the two-component probability vector has L1 Lipschitz constant 1/8. Since D=2 sqrt(2)<=3, the uniform certificate is

    (5/16)*(3/2) + (11/16)*(1/4) + (3/2)*(1/8)
      = 41/64 + 12/64 = 53/64 < 1.

The toy applies the exact rational mixture to the same two Jordan polynomial updates as the graph campaign. This supplies a *global* guarantee for state-dependent **smooth** routing, extending the finite trace guarantee under strict hard-guard margins.

The independent rational oracle and 625-matrix Perron grid are in research/compactification/barycentric_fixedpoints.py and tests/test_barycentric_fixedpoints.py. Its analytic claims are proved above; Lean's NRF-02 module remains restricted to its two-edge cross-multiplication lemma. Rapid rational numerator growth in repeated nonlinear mixtures motivates short exact runs and interval-certified higher-depth experiments.
