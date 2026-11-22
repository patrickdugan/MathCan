# DEL-01: independent trace-sign audit of Hexagon 2611.00789v1

**Date:** 2026-11-22  
**Target:** [A short proof of Deligne's bound for Frobenius eigenvalues, after Alpoege](https://hexagonmath.org/2611.00789v1), version 1, 21 November 2026.  
**Original ideas:** L. Alpoege; the deposited exposition is AI-generated.  
**Primary Lefschetz source:** N. Katz, *Affine Cohomological Transforms, Perversity, and Monodromy*, JAMS 6 (1993), Appendix A.3-A.5, pp. 219-221; [author-hosted PDF](https://web.math.princeton.edu/~nmk/old/ACT.pdf).

## Audit status

| Claim | Independent evidence | Current status |
| --- | --- | --- |
| Lemma 2, positive power sums | Pole argument checked symbolically; negative-multiplicity and finite-window mutants | **Paper proof reviewed; not formalized in Lean** |
| Lemma 3, finite Fourier path bound | Exact \(\mathbb Z[\zeta_p]\) tests at \(p=2,3\), multiple dimensions and path lengths | **Finite instances verified; general theorem pending** |
| Proposition 4, signs | Independent Gysin degree bookkeeping; Lean abstract cancellation; concrete hyperbola counts | **Sign algebra verified; geometry supplied as hypotheses** |
| Lemma 8, weak Lefschetz input | Compared directly with Katz A.5, p. 220, including A.3-A.4 | **Source hypotheses matched; application not formally verified** |
| Theorem 1, Deligne bounds | Follows only after all geometric/cohomological prerequisites | **Not certified by this audit** |

## 1. Power sums and what positivity buys

For a genuine finite-dimensional Frobenius module, each eigenvalue contributes an integer algebraic multiplicity \(m_j>0\). For distinct nonzero complex eigenvalues, the generating series
\[
\sum_{n\ge 1}\operatorname{Tr}(F^n)z^n
=\sum_j m_j\frac{\lambda_j z}{1-\lambda_j z}
\]
has a pole at each \(z=1/\lambda_j\). A growth bound \(|\operatorname{Tr}(F^n)|\le C B^n\) for **all** positive integers \(n\) therefore bounds each \(|\lambda_j|\le B\).

The full Lemma 2 raises this conclusion through tensor powers: if a trace identity holds for infinitely many \(k\) and the exponent error \(c_k/k\to0\), then each eigenvalue of \(V\) has modulus at most \(q^a\). The auxiliary module \(K_k\) may vary with \(k\) because the positive direct-sum trace still exposes every pole.

Mutation DEL-VIRTUAL deliberately replaces a positive direct-sum trace with \(\lambda^n-\lambda^n=0\). Mutation DEL-ONE-N checks only \(n=1\) for eigenvalues 7 and -7, hiding their even-power growth. Both show why the hypotheses are essential.

## 2. Exact finite Fourier verification

For nondegenerate \(b\), the matrix \(K(x,y)=\psi(hb(x,y))\) satisfies \(KK^*=Q^dI\). The operator norm is therefore \(Q^{d/2}\). Combining the two endpoint vector norms and intermediate diagonal norms gives
\[
|S_k| \le T^k Q^{d(k+1)/2}.
\]

The included Python module computes cyclotomic sums without floating point. At \(p=2\), a coefficient pair \((c_0,c_1)\) has squared modulus \((c_0-c_1)^2\). At \(p=3\), write \(a=c_0-c_2\), \(b=c_1-c_2\). Its squared modulus is \(a^2-ab+b^2\). The tests compare this integer with \(T^{2k}p^{d(k+1)}\), and separately verify the full Fourier row orthogonality for \(d=1,2\).

The zero-bilinear mutation in \(\mathbb F_2\), \(d=1,k=3\), with unit weights produces \(|S|=8\) versus the putative bound 4. Its norm squares are 64 and 16. This is an expected counterexample to a theorem with nondegeneracy removed.

## 3. Proposition 4: trace and sign ledger

Set \(D=kd\), \(X=U^k\), and \(Y\subset X\) a smooth affine hypersurface. Duality translates weak Lefschetz into Gysin maps
\[
H_c^{D-1+a}(Y,\mathcal F_k)(-1)
\longrightarrow H_c^{D+1+a}(X,\mathcal F_k).
\]
The map is surjective for \(a=0\) and an isomorphism for \(a\ge1\). It is Frobenius-equivariant.

The trace formula, including the extra \(r^n\) on \(N_n\), gives
\[
(-1)^{D-1}R_n
=\operatorname{Tr}(Y_{D-1}(-1))
-\operatorname{Tr}(X_{D+1})
+\operatorname{Tr}(X_D)
+\sum_{a\ge1}(-1)^a
  [\operatorname{Tr}(Y_{D-1+a}(-1))
    -\operatorname{Tr}(X_{D+1+a})].
\]
The final sum vanishes term by term. Frobenius-equivariant exactness gives
\(\operatorname{Tr}(Y_{D-1}(-1))-\operatorname{Tr}(X_{D+1})=\operatorname{Tr}(K)\).
Kunneth and Artin vanishing identify \(X_D=H_c^d(U,\mathcal F)^{\otimes k}\). This establishes the claimed **algebraic sign identity under the geometric hypotheses**.

Concrete test: \(U=\mathbb A^1\), \(X=\mathbb A^2\), \(k=2\), \(Y:xy+ax+by+c=0\) with \(ab\ne c\). Over \(\mathbb F_p\), \(M=p\), \(N=p-1\), \(R=-p\), so \((-1)^{D-1}R=p\), consistent with the single twisted kernel eigenvalue. The mutation \(c=ab\) produces two crossing lines, violating smoothness and the example's numerical identity.

## 4. Katz A.5 and the fixed bilinear coefficient

Direct source audit:

- Katz A.3 starts from a separated finite-type map \(f:X\to\mathbb P^M\). A.5 requires \(f\) quasi-finite and \(K\) perverse on \(X\), then gives restriction isomorphisms in degree \(i<-1\) and injection in degree \(i=-1\) for generic projective hyperplanes.
- In Lemma 8, take \(f=\Gamma:V\hookrightarrow\mathbb A^M\subset\mathbb P^M\), a closed immersion, and the perverse sheaf \(\mathcal G[D]\) for smooth pure-dimensional \(V\). The shift converts Katz's cutoffs into \(a<D-1\) and \(a=D-1\).
- Smoothness is a separate generic hyperplane fact: the incidence space of hyperplanes containing a prescribed embedded tangent space has dimension at most \(M-1\). Thus its image is a proper closed subset of the \(M\)-dimensional hyperplane parameter space.
- The hyperplanes with nonzero coefficient on the last coordinate form an open dense chart. Intersecting it with the two good dense opens and normalizing that coefficient to 1 preserves genericity. Over a finite field, a geometric generic point of this chart descends to some finite extension \(\mathbb F_{q^e}\), which is permitted by Lemma 2.

Watch for accidental **strengthening** in a formalization: there need only exist a suitable finite extension for each \(k\); one extension independent of all \(k\) is unnecessary. The manuscript states this correctly.

## 5. What Lean certifies here

The repository has Lean 4.35, Init and no Mathlib dependency. `MathCan/DeligneSignAudit.lean` proves an abstract Gysin trace cancellation, explicit F2 Fourier matrix orthogonality, all 81 weighted two-point character sums with weights in {-1,0,1}, and the hyperbola remainder arithmetic. It prints each theorem's axioms. These proofs are narrowly scoped and contain no etale geometry or unproved theorem disguised as a Lean declaration.

The CI workflow runs that file through the Lean kernel and executes the independent integer-arithmetic checks. Local Python test execution passed 5 tests on 2026-11-22; GitHub CI is the authority for the repository's Lean build.

## 6. Next substantive formal milestones

1. In a **separate Mathlib-enabled experiment**, formalize the general complex power-sum pole lemma with algebraic multiplicities and uniform bounds over all \(n\). Preserve the varying \(e_k,K_k,c_k\) quantifiers.
2. Formalize the nondegenerate finite-character orthogonality and operator-norm proof over arbitrary finite fields and dimensions. This closes general Lemma 3 without sheaf infrastructure.
3. Introduce an explicit abstract cohomology/Gysin interface, with Frobenius-equivariance, Tate twists and Kunneth as hypotheses. Prove Proposition 4 from that interface, including all grading and signs.
4. Audit the source-level implementation of Katz A.5 against its exact perverse-sheaf and quasi-finite hypotheses. Formalizing Katz itself would require substantial etale/perverse-sheaf libraries.

## DataGoblin / Lean-CGRT use

Create verifier-grounded synth examples by mutating **one** hypothesis at a time: nondegeneracy, smoothness, positive multiplicity, all-powers quantification, Tate twist, coefficient-chart restriction, finite-extension quantifier, or the exact Gysin degree. Score each by an executable finite oracle where available; geometry-specific questions should be labeled *source-review* until an actual formal checker exists. This division prevents a model from learning that a passed finite shadow certifies the full Deligne theorem.
