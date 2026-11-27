/-!
# SCCG-10: conditional stale-observer admission (finite exact lemmas)

Integers stand in for exactly scaled rationals. A cached target derivative
`a` and protected rows `C` are reused at a newer checkpoint with live
derivatives `a'`, `C'`. Nothing here concerns real-valued norms or native
transformer outputs.
-/

namespace MathCan.SCCG10Admission

/-- Integer dot product over `Fin n`, defined by recursion on `n`. -/
def dot : {n : Nat} → (Fin n → Int) → (Fin n → Int) → Int
  | 0, _, _ => 0
  | _ + 1, x, y => x 0 * y 0 + dot (fun i => x i.succ) (fun i => y i.succ)

/-- 1. Stale target derivative: lower bound on the live realized change. -/
theorem stale_target_lower {n : Nat} (a a' u : Fin n → Int)
    (f0 f1 r R E : Int)
    (hf : f1 - f0 = dot a' u + r) (hr : -R ≤ r ∧ r ≤ R)
    (hE : -E ≤ dot a' u - dot a u ∧ dot a' u - dot a u ≤ E) :
    f1 - f0 ≥ dot a u - (E + R) := by
  omega

/-- 2. Stale protected rows: l-infinity admission. -/
theorem stale_protected_linf {m : Nat} (g0 g1 Cu C'u : Fin m → Int)
    (r R E : Fin m → Int) (eta : Int)
    (hg : ∀ i, g1 i - g0 i = C'u i + r i)
    (hr : ∀ i, -R i ≤ r i ∧ r i ≤ R i)
    (hE : ∀ i, -E i ≤ C'u i - Cu i ∧ C'u i - Cu i ≤ E i)
    (hadm : ∀ i, Int.natAbs (Cu i) + E i + R i ≤ eta) :
    ∀ i, Int.natAbs (g1 i - g0 i) ≤ eta := by
  intro i
  have := hg i; have := hr i; have := hE i; have := hadm i
  omega

/-- 3. Refresh value is at most `U - L`. -/
theorem refresh_value_le_gap {α : Type} (feasible : α → Prop) (gain : α → Int)
    (cached : α) (U L : Int)
    (hU : ∀ v, feasible v → gain v ≤ U) (hL : gain cached ≥ L) :
    ∀ v, feasible v → gain v - gain cached ≤ U - L := by
  intro v hv
  have := hU v hv
  omega

/-- 4a. Pairwise ranking certificate. -/
theorem ranking_certificate (p p' eps : Nat → Int) (i j : Nat)
    (hi : -eps i ≤ p' i - p i ∧ p' i - p i ≤ eps i)
    (hj : -eps j ≤ p' j - p j ∧ p' j - p j ≤ eps j)
    (h : p i - eps i > p j + eps j) : p' i > p' j := by
  omega

/-- 4b. Top-set certificate over `Fin n`. -/
theorem ranking_topset {n : Nat} (p p' eps : Fin n → Int) (S : Fin n → Prop)
    (hdev : ∀ k, -eps k ≤ p' k - p k ∧ p' k - p k ≤ eps k)
    (hsep : ∀ i j, S i → ¬ S j → p i - eps i > p j + eps j) :
    ∀ i j, S i → ¬ S j → p' i > p' j := by
  intro i j hi hj
  have := hdev i; have := hdev j; have := hsep i j hi hj
  omega

/-- 4c. Same with the min/max formulated as a common threshold `t`:
    every `p - eps` in `S` is `> t` and every `p + eps` outside is `≤ t`
    (such a `t` exists iff min over `S` exceeds max over the complement). -/
theorem ranking_topset_threshold {n : Nat} (p p' eps : Fin n → Int)
    (S : Fin n → Prop) (t : Int)
    (hdev : ∀ k, -eps k ≤ p' k - p k ∧ p' k - p k ≤ eps k)
    (hin : ∀ i, S i → p i - eps i > t) (hout : ∀ j, ¬ S j → p j + eps j ≤ t) :
    ∀ i j, S i → ¬ S j → p' i > p' j := by
  intro i j hi hj
  have := hdev i; have := hdev j; have := hin i hi; have := hout j hj
  omega

/-- 5. A positive steering gain can coexist with worse validation loss. -/
theorem steering_gain_not_learning_value :
    ∃ (G V : Int → Int) (θ0 θ1 : Int),
      G θ1 > G θ0 ∧ V θ1 > V θ0 :=
  ⟨fun θ => θ, fun θ => θ * θ, 0, 1, by decide, by decide⟩

/-- 6. A zero sampled residual is not a uniform bound. -/
theorem sample_residual_not_uniform (S : List Int) :
    ∃ f g : Int → Int, (∀ s, s ∈ S → f s = g s) ∧ ∃ x, f x ≠ g x := by
  refine ⟨fun _ => 0, fun x => if x ∈ S then 0 else 1, ?_, ?_⟩
  · intro s hs; simp [hs]
  · -- choose a point outside S: one more than the sum of absolute values
    have key : ∀ L : List Int, ∃ x, x ∉ L := by
      intro L
      let B : Nat := (L.map Int.natAbs).foldr (· + ·) 0
      have hb : ∀ L : List Int, ∀ y ∈ L, y.natAbs ≤ (L.map Int.natAbs).foldr (· + ·) 0 := by
        intro L
        induction L with
        | nil => simp
        | cons h t ih =>
          intro y hy
          simp only [List.map_cons, List.foldr_cons]
          cases List.mem_cons.mp hy with
          | inl e => subst e; omega
          | inr m => have := ih y m; omega
      refine ⟨(B : Int) + 1, fun hx => ?_⟩
      have := hb L _ hx
      omega
    obtain ⟨x, hx⟩ := key S
    exact ⟨x, by simp [hx]⟩

/-! ### Optional: integer Cauchy-Schwarz via a Lagrange-type induction -/

theorem dot_self_nonneg : ∀ {n : Nat} (x : Fin n → Int), 0 ≤ dot x x
  | 0, _ => by simp [dot]
  | n + 1, x => by
      have := dot_self_nonneg (fun i : Fin n => x i.succ)
      have h2 : 0 ≤ x 0 * x 0 := by
        rcases Int.le_total 0 (x 0) with h | h
        · exact Int.mul_nonneg h h
        · exact Int.mul_nonneg_of_nonpos_of_nonpos h h
      simp only [dot]; omega

/-- `dot z z` for `z = c•y - d•x` expands bilinearly. -/
theorem dot_comb : ∀ {n : Nat} (x y : Fin n → Int) (c d : Int),
    dot (fun i => c * y i - d * x i) (fun i => c * y i - d * x i)
      = c * c * dot y y - 2 * c * d * dot x y + d * d * dot x x
  | 0, _, _, _, _ => by simp [dot]
  | n + 1, x, y, c, d => by
      have ih := dot_comb (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ) c d
      simp only [dot] at ih ⊢
      rw [ih]
      grind

theorem cauchy_schwarz : ∀ {n : Nat} (x y : Fin n → Int),
    dot x y * dot x y ≤ dot x x * dot y y
  | 0, _, _ => by simp [dot]
  | n + 1, x, y => by
      have ih := cauchy_schwarz (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ)
      have hz := dot_self_nonneg
        (fun i : Fin n => x 0 * y i.succ - y 0 * x i.succ)
      rw [dot_comb] at hz
      simp only [dot]
      generalize dot (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ) = A at *
      generalize dot (fun i : Fin n => x i.succ) (fun i : Fin n => x i.succ) = X at *
      generalize dot (fun i : Fin n => y i.succ) (fun i : Fin n => y i.succ) = Y at *
      generalize x 0 = a at *
      generalize y 0 = b at *
      grind

/-- Squared-l2 admission: if the squared l2 norm of the protected
    change, bounded through Cauchy-Schwarz with a unit-weight row `w`,
    is within budget then the linear functional on `u` is within it. -/
theorem squared_l2_functional_bound {n : Nat} (c u : Fin n → Int) (B : Int)
    (h : dot c c * dot u u ≤ B) : dot c u * dot c u ≤ B :=
  Int.le_trans (cauchy_schwarz c u) h

#print axioms stale_target_lower
#print axioms stale_protected_linf
#print axioms refresh_value_le_gap
#print axioms ranking_certificate
#print axioms ranking_topset
#print axioms ranking_topset_threshold
#print axioms steering_gain_not_learning_value
#print axioms sample_residual_not_uniform
#print axioms cauchy_schwarz
#print axioms squared_l2_functional_bound

end MathCan.SCCG10Admission
