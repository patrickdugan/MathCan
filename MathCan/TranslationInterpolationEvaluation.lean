module

public import Init

public section

/-!
# Constructive finite hyperplane interpolation

The index `none` is a chosen pivot of S, not the identity of the elliptic curve;
`some i` enumerates all other points of S. Thus S has n+1 points here.
The proofs construct a basis of the kernel of a nonzero weighted evaluation
functional and then construct a two-block decoder for every symmetric matrix
annihilated by that functional. No geometry is assumed inside these algebraic
proofs. Identifying the evaluations of bounded-degree curve polynomials with
this hyperplane remains the geometric input of the interpolation application.
-/

namespace MathCan.TranslationInterpolationEvaluation

open Lean.Grind

variable {K : Type} [Field K]

/-- A concrete finite sum, with no abstract summation oracle. -/
def sum : (n : Nat) → (Fin n → K) → K
  | 0, _ => 0
  | n + 1, f => f 0 + sum n (fun i => f i.succ)

theorem sum_congr {n : Nat} (f g : Fin n → K)
    (h : ∀ i, f i = g i) : sum n f = sum n g := by
  have : f = g := funext h
  rw [this]

theorem sum_zero (n : Nat) : sum n (fun _ => (0 : K)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum, ih]
    grind

theorem sum_add (n : Nat) (f g : Fin n → K) :
    sum n (fun i => f i + g i) = sum n f + sum n g := by
  induction n with
  | zero => simp only [sum]; grind
  | succ n ih =>
    simp only [sum, ih]
    grind

theorem sum_mul_left (n : Nat) (c : K) (f : Fin n → K) :
    sum n (fun i => c * f i) = c * sum n f := by
  induction n with
  | zero => simp only [sum]; grind
  | succ n ih =>
    simp only [sum, ih]
    grind

theorem sum_mul_right (n : Nat) (f : Fin n → K) (c : K) :
    sum n (fun i => f i * c) = sum n f * c := by
  calc
    sum n (fun i => f i * c) = sum n (fun i => c * f i) :=
      sum_congr _ _ (fun _ => by grind)
    _ = c * sum n f := sum_mul_left n c f
    _ = sum n f * c := by grind

theorem sum_single (n : Nat) (a : Fin n) (f : Fin n → K) :
    sum n (fun i => if i = a then f i else 0) = f a := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [sum, ite_true, Fin.succ_ne_zero, ite_false, sum_zero]
      grind
    · have h0 : (0 : Fin (n + 1)) ≠ a.succ := Ne.symm (Fin.succ_ne_zero a)
      simp only [sum, h0, ite_false, Fin.succ_inj]
      rw [ih a]
      grind

/-- The weighted evaluation functional on the pivot plus n other points. -/
def dot {n : Nat} (lam v : Option (Fin n) → K) : K :=
  lam none * v none + sum n (fun i => lam (some i) * v (some i))

theorem dot_add {n : Nat} (lam v w : Option (Fin n) → K) :
    dot lam (fun i => v i + w i) = dot lam v + dot lam w := by
  unfold dot
  have h := sum_congr
    (fun i : Fin n => lam (some i) * (v (some i) + w (some i)))
    (fun i => lam (some i) * v (some i) + lam (some i) * w (some i))
    (fun _ => by grind)
  rw [h, sum_add]
  grind

theorem dot_mul {n : Nat} (lam v : Option (Fin n) → K) (c : K) :
    dot lam (fun i => c * v i) = c * dot lam v := by
  unfold dot
  have h := sum_congr
    (fun i : Fin n => lam (some i) * (c * v (some i)))
    (fun i => c * (lam (some i) * v (some i)))
    (fun _ => by grind)
  rw [h, sum_mul_left]
  grind

/-- Canonical hyperplane basis, normalized at the nonpivot points. -/
def basis {n : Nat} (lam : Option (Fin n) → K) (a : Fin n) : Option (Fin n) → K
  | none => -(lam (some a) / lam none)
  | some i => if i = a then 1 else 0

theorem basis_annihilated {n : Nat} (lam : Option (Fin n) → K)
    (hp : lam none ≠ 0) (a : Fin n) : dot lam (basis lam a) = 0 := by
  unfold dot basis
  have h := sum_congr
    (fun i : Fin n => lam (some i) * (if i = a then 1 else 0))
    (fun i => if i = a then lam (some i) else 0)
    (fun i => by split <;> grind)
  rw [h, sum_single]
  have hi := Field.inv_mul_cancel hp
  rw [Field.div_eq_mul_inv]
  grind

theorem dot_zero {n : Nat} (lam : Option (Fin n) → K) :
    dot lam (fun _ => 0) = 0 := by
  unfold dot
  have h := sum_congr
    (fun i : Fin n => lam (some i) * 0) (fun _ => 0) (fun _ => by grind)
  rw [h, sum_zero]
  grind

theorem dot_sum {m : Nat} (n : Nat) (lam : Option (Fin m) → K)
    (v : Fin n → Option (Fin m) → K) :
    dot lam (fun i => sum n (fun a => v a i)) =
      sum n (fun a => dot lam (v a)) := by
  induction n with
  | zero => simpa only [sum] using dot_zero lam
  | succ n ih =>
    simp only [sum]
    rw [dot_add, ih]

/-- Every finite linear combination of the basis lies in the hyperplane. -/
theorem span_annihilated {n : Nat} (lam : Option (Fin n) → K)
    (hp : lam none ≠ 0) (c : Fin n → K) :
    dot lam (fun i => sum n (fun a => c a * basis lam a i)) = 0 := by
  rw [dot_sum]
  have h := sum_congr
    (fun a : Fin n => dot lam (fun i => c a * basis lam a i))
    (fun _ => 0)
    (fun a => by rw [dot_mul, basis_annihilated lam hp a]; grind)
  rw [h, sum_zero]

theorem span_at_nonpivot {n : Nat} (lam : Option (Fin n) → K)
    (c : Fin n → K) (i : Fin n) :
    sum n (fun a => c a * basis lam a (some i)) = c i := by
  have h := sum_congr
    (fun a : Fin n => c a * basis lam a (some i))
    (fun a => if a = i then c a else 0)
    (fun a => by simp only [basis]; split <;> split <;> grind)
  rw [h, sum_single]

/-- Explicit interpolation coefficients are the nonpivot coordinates. -/
theorem hyperplane_reconstruction {n : Nat} (lam : Option (Fin n) → K)
    (hp : lam none ≠ 0) (v : Option (Fin n) → K) (hv : dot lam v = 0) :
    ∀ i, sum n (fun a => v (some a) * basis lam a i) = v i := by
  intro i
  cases i with
  | none =>
    have h := sum_congr
      (fun a : Fin n => v (some a) * basis lam a none)
      (fun a => -(lam none)⁻¹ * (lam (some a) * v (some a)))
      (fun a => by simp only [basis, Field.div_eq_mul_inv]; grind)
    rw [h, sum_mul_left]
    have hi := Field.inv_mul_cancel hp
    unfold dot at hv
    grind
  | some i => exact span_at_nonpivot lam (fun a => v (some a)) i

/-- The canonical basis spans exactly the weighted hyperplane. -/
theorem span_iff_annihilated {n : Nat} (lam : Option (Fin n) → K)
    (hp : lam none ≠ 0) (v : Option (Fin n) → K) :
    (∃ c : Fin n → K, ∀ i, sum n (fun a => c a * basis lam a i) = v i) ↔
      dot lam v = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have he : (fun i => sum n (fun a => c a * basis lam a i)) = v := funext hc
    rw [← he]
    exact span_annihilated lam hp c
  · intro hv
    exact ⟨fun a => v (some a), hyperplane_reconstruction lam hp v hv⟩

/-- Evaluation of a two-block coefficient matrix in the canonical basis. -/
def decode {n : Nat} (lam : Option (Fin n) → K) (C : Fin n → Fin n → K)
    (i j : Option (Fin n)) : K :=
  sum n (fun a => basis lam a i * sum n (fun b => C a b * basis lam b j))

theorem decoder_annihilated {n : Nat} (lam : Option (Fin n) → K)
    (hp : lam none ≠ 0) (C : Fin n → Fin n → K) :
    ∀ i, dot lam (decode lam C i) = 0 := by
  intro i
  unfold decode
  rw [dot_sum]
  have h := sum_congr
    (fun a : Fin n => dot lam
      (fun j => basis lam a i * sum n (fun b => C a b * basis lam b j)))
    (fun _ => 0)
    (fun a => by rw [dot_mul, span_annihilated lam hp (C a)]; grind)
  rw [h, sum_zero]

/-- A symmetric matrix is reconstructed from its nonpivot submatrix.
This proves the finite tensor/interpolation step with actual finite sums. -/
theorem symmetric_decoder_reconstruction {n : Nat} (lam : Option (Fin n) → K)
    (hp : lam none ≠ 0) (M : Option (Fin n) → Option (Fin n) → K)
    (hsym : ∀ i j, M i j = M j i) (hrow : ∀ i, dot lam (M i) = 0) :
    ∀ i j, decode lam (fun a b => M (some a) (some b)) i j = M i j := by
  intro i j
  have hcol : dot lam (fun a => M a j) = 0 := by
    have he : (fun a => M a j) = M j := funext (fun a => hsym a j)
    rw [he]
    exact hrow j
  unfold decode
  calc
    sum n (fun a => basis lam a i *
      sum n (fun b => M (some a) (some b) * basis lam b j)) =
        sum n (fun a => M (some a) j * basis lam a i) := by
      apply sum_congr
      intro a
      rw [hyperplane_reconstruction lam hp (M (some a)) (hrow (some a)) j]
      grind
    _ = M i j := hyperplane_reconstruction lam hp (fun a => M a j) hcol i

/-- Exact equivalence between a two-block decoder and the row annihilator. -/
theorem symmetric_decoder_iff {n : Nat} (lam : Option (Fin n) → K)
    (hp : lam none ≠ 0) (M : Option (Fin n) → Option (Fin n) → K)
    (hsym : ∀ i j, M i j = M j i) :
    (∃ C : Fin n → Fin n → K, ∀ i j, decode lam C i j = M i j) ↔
      ∀ i, dot lam (M i) = 0 := by
  constructor
  · rintro ⟨C, hC⟩ i
    have he : decode lam C i = M i := funext (hC i)
    rw [← he]
    exact decoder_annihilated lam hp C i
  · intro hrow
    exact ⟨fun a b => M (some a) (some b),
      symmetric_decoder_reconstruction lam hp M hsym hrow⟩

theorem decoder_at_nonpivots {n : Nat} (lam : Option (Fin n) → K)
    (C : Fin n → Fin n → K) (i j : Fin n) :
    decode lam C (some i) (some j) = C i j := by
  unfold decode
  have h := sum_congr
    (fun a : Fin n => basis lam a (some i) *
      sum n (fun b => C a b * basis lam b (some j)))
    (fun a => C a j * basis lam a (some i))
    (fun a => by rw [span_at_nonpivot]; grind)
  rw [h, span_at_nonpivot]

/-- The displayed decoder coefficients are uniquely determined. -/
theorem decoder_coefficients_unique {n : Nat} (lam : Option (Fin n) → K)
    (C D : Fin n → Fin n → K)
    (h : ∀ i j, decode lam C i j = decode lam D i j) : C = D := by
  funext i j
  have he := h (some i) (some j)
  rw [decoder_at_nonpivots, decoder_at_nonpivots] at he
  exact he

/-- A point mass on the full finite evaluation set. -/
def pointMass {n : Nat} (a i : Option (Fin n)) : K := if i = a then 1 else 0

theorem dot_pointMass {n : Nat} (lam : Option (Fin n) → K)
    (a : Option (Fin n)) : dot lam (pointMass a) = lam a := by
  cases a with
  | none =>
    unfold dot pointMass
    simp only [ite_true, reduceCtorEq, ite_false]
    have h := sum_congr (fun i : Fin n => lam (some i) * 0)
      (fun _ => 0) (fun _ => by grind)
    rw [h, sum_zero]
    grind
  | some a =>
    unfold dot pointMass
    simp only [reduceCtorEq, ite_false, Option.some.injEq]
    have h := sum_congr
      (fun i : Fin n => lam (some i) * (if i = a then 1 else 0))
      (fun i => if i = a then lam (some i) else 0)
      (fun i => by split <;> grind)
    rw [h, sum_single]
    grind

/-- Assigning the missing identity value adds a scalar negation matrix. -/
def assignPole {n : Nat} (M : Option (Fin n) → Option (Fin n) → K)
    (neg : Option (Fin n) → Option (Fin n)) (u : K)
    (i j : Option (Fin n)) : K := M i j + u * pointMass (neg i) j

theorem assigned_matrix_symmetric {n : Nat}
    (M : Option (Fin n) → Option (Fin n) → K)
    (neg : Option (Fin n) → Option (Fin n)) (u : K)
    (hsym : ∀ i j, M i j = M j i) (hinv : ∀ i, neg (neg i) = i) :
    ∀ i j, assignPole M neg u i j = assignPole M neg u j i := by
  intro i j
  unfold assignPole pointMass
  have hi := hinv i
  have hj := hinv j
  have he := hsym i j
  split <;> split <;> grind

theorem assigned_row_iff_eigenvector {n : Nat}
    (lam : Option (Fin n) → K)
    (M : Option (Fin n) → Option (Fin n) → K)
    (neg : Option (Fin n) → Option (Fin n)) (u : K)
    (hodd : ∀ i, lam (neg i) = -lam i) (i : Option (Fin n)) :
    dot lam (assignPole M neg u i) = 0 ↔ dot lam (M i) = u * lam i := by
  unfold assignPole
  rw [dot_add, dot_mul, dot_pointMass, hodd i]
  constructor <;> intro h <;> grind

/-- The complete finite eigenvector criterion, including the assigned pole
value and the action of the actual negation permutation on finite sums. -/
theorem pole_decoder_iff_eigenvector {n : Nat}
    (lam : Option (Fin n) → K) (hp : lam none ≠ 0)
    (M : Option (Fin n) → Option (Fin n) → K)
    (neg : Option (Fin n) → Option (Fin n)) (u : K)
    (hsym : ∀ i j, M i j = M j i) (hinv : ∀ i, neg (neg i) = i)
    (hodd : ∀ i, lam (neg i) = -lam i) :
    (∃ C : Fin n → Fin n → K,
      ∀ i j, decode lam C i j = assignPole M neg u i j) ↔
    ∀ i, dot lam (M i) = u * lam i := by
  rw [symmetric_decoder_iff lam hp (assignPole M neg u)
    (assigned_matrix_symmetric M neg u hsym hinv)]
  constructor
  · intro h i
    exact (assigned_row_iff_eigenvector lam M neg u hodd i).mp (h i)
  · intro h i
    exact (assigned_row_iff_eigenvector lam M neg u hodd i).mpr (h i)

theorem assigned_value_unique {n : Nat}
    (lam : Option (Fin n) → K) (hp : lam none ≠ 0)
    (M : Option (Fin n) → Option (Fin n) → K) (u v : K)
    (hu : ∀ i, dot lam (M i) = u * lam i)
    (hv : ∀ i, dot lam (M i) = v * lam i) : u = v := by
  have he₁ := hu none
  have he₂ := hv none
  have hz : (u-v) * lam none = 0 := by grind
  cases Field.of_mul_eq_zero hz with
  | inl he => grind
  | inr he => exact False.elim (hp he)

/-- Evaluation of a finite tensor of arbitrary feature functions. When the
features are polynomial evaluations, this is the evaluated two-block polynomial. -/
def evaluateTensor {n m : Nat} (features : Fin m → Option (Fin n) → K)
    (C : Fin m → Fin m → K) (i j : Option (Fin n)) : K :=
  sum m (fun a => features a i * sum m (fun b => C a b * features b j))

theorem feature_span_annihilated {n m : Nat}
    (lam : Option (Fin n) → K) (features : Fin m → Option (Fin n) → K)
    (hfeatures : ∀ a, dot lam (features a) = 0) (c : Fin m → K) :
    dot lam (fun i => sum m (fun a => c a * features a i)) = 0 := by
  rw [dot_sum]
  have h := sum_congr
    (fun a : Fin m => dot lam (fun i => c a * features a i))
    (fun _ => 0)
    (fun a => by rw [dot_mul, hfeatures a]; grind)
  rw [h, sum_zero]

theorem feature_tensor_annihilated {n m : Nat}
    (lam : Option (Fin n) → K) (features : Fin m → Option (Fin n) → K)
    (hfeatures : ∀ a, dot lam (features a) = 0) (C : Fin m → Fin m → K) :
    ∀ i, dot lam (evaluateTensor features C i) = 0 := by
  intro i
  unfold evaluateTensor
  rw [dot_sum]
  have h := sum_congr
    (fun a : Fin m => dot lam
      (fun j => features a i * sum m (fun b => C a b * features b j)))
    (fun _ => 0)
    (fun a => by
      rw [dot_mul, feature_span_annihilated lam features hfeatures (C a)]
      grind)
  rw [h, sum_zero]

/-- The geometric evaluation-image premise is isolated here. From it, the
finite algebra constructs actual feature representatives and decoder coefficients.
No pre-existing decoder or tensor-containment premise is assumed. -/
theorem evaluation_hyperplane_decoder_iff {n : Nat} {P : Type}
    (lam : Option (Fin n) → K) (hp : lam none ≠ 0)
    (eval : P → Option (Fin n) → K)
    (himage : ∀ v, (∃ p, eval p = v) ↔ dot lam v = 0)
    (M : Option (Fin n) → Option (Fin n) → K)
    (hsym : ∀ i j, M i j = M j i) :
    (∃ features : Fin n → P, ∃ C : Fin n → Fin n → K,
      ∀ i j, evaluateTensor (fun a => eval (features a)) C i j = M i j) ↔
    ∀ i, dot lam (M i) = 0 := by
  constructor
  · rintro ⟨features, C, hC⟩ i
    have hall : ∀ a, dot lam (eval (features a)) = 0 := by
      intro a
      exact (himage (eval (features a))).mp ⟨features a, rfl⟩
    have he : evaluateTensor (fun a => eval (features a)) C i = M i := funext (hC i)
    rw [← he]
    exact feature_tensor_annihilated lam (fun a => eval (features a)) hall C i
  · intro hrow
    have hex : ∀ a : Fin n, ∃ p, eval p = basis lam a := by
      intro a
      exact (himage (basis lam a)).mpr (basis_annihilated lam hp a)
    let features : Fin n → P := fun a => Classical.choose (hex a)
    have heval : ∀ a, eval (features a) = basis lam a := fun a => Classical.choose_spec (hex a)
    refine ⟨features, (fun a b => M (some a) (some b)), ?_⟩
    intro i j
    have he : (fun a => eval (features a)) = basis lam := funext heval
    rw [he]
    exact symmetric_decoder_reconstruction lam hp M hsym hrow i j

theorem evaluation_columns_decoder_iff {n : Nat} {P : Type}
    (lam : Option (Fin n) → K) (hp : lam none ≠ 0)
    (eval : P → Option (Fin n) → K)
    (himage : ∀ v, (∃ p, eval p = v) ↔ dot lam v = 0)
    (M : Option (Fin n) → Option (Fin n) → K)
    (hsym : ∀ i j, M i j = M j i) :
    (∃ features : Fin n → P, ∃ C : Fin n → Fin n → K,
      ∀ i j, evaluateTensor (fun a => eval (features a)) C i j = M i j) ↔
    ∀ j, ∃ p, eval p = (fun i => M i j) := by
  rw [evaluation_hyperplane_decoder_iff lam hp eval himage M hsym]
  constructor
  · intro h j
    apply (himage (fun i => M i j)).mpr
    have he : (fun i => M i j) = M j := funext (fun i => hsym i j)
    rw [he]
    exact h j
  · intro h i
    have hz := (himage (fun j => M j i)).mp (h i)
    have he : (fun j => M j i) = M i := funext (fun j => hsym j i)
    rw [he] at hz
    exact hz

/-- Composed criterion for feature evaluations and an assigned identity value.
For the curve application, P is the space of polynomials of the specified degree.
The only evaluation-space hypothesis is its equality with the residue hyperplane. -/
theorem evaluation_pole_decoder_iff {n : Nat} {P : Type}
    (lam : Option (Fin n) → K) (hp : lam none ≠ 0)
    (eval : P → Option (Fin n) → K)
    (himage : ∀ v, (∃ p, eval p = v) ↔ dot lam v = 0)
    (M : Option (Fin n) → Option (Fin n) → K)
    (neg : Option (Fin n) → Option (Fin n)) (u : K)
    (hsym : ∀ i j, M i j = M j i) (hinv : ∀ i, neg (neg i) = i)
    (hodd : ∀ i, lam (neg i) = -lam i) :
    (∃ features : Fin n → P, ∃ C : Fin n → Fin n → K,
      ∀ i j, evaluateTensor (fun a => eval (features a)) C i j = assignPole M neg u i j) ↔
    ∀ i, dot lam (M i) = u * lam i := by
  rw [evaluation_hyperplane_decoder_iff lam hp eval himage (assignPole M neg u)
    (assigned_matrix_symmetric M neg u hsym hinv)]
  constructor
  · intro h i
    exact (assigned_row_iff_eigenvector lam M neg u hodd i).mp (h i)
  · intro h i
    exact (assigned_row_iff_eigenvector lam M neg u hodd i).mpr (h i)

#print axioms span_iff_annihilated
#print axioms symmetric_decoder_reconstruction
#print axioms symmetric_decoder_iff
#print axioms decoder_coefficients_unique
#print axioms dot_pointMass
#print axioms assigned_row_iff_eigenvector
#print axioms pole_decoder_iff_eigenvector
#print axioms assigned_value_unique
#print axioms feature_tensor_annihilated
#print axioms evaluation_hyperplane_decoder_iff
#print axioms evaluation_columns_decoder_iff
#print axioms evaluation_pole_decoder_iff

end MathCan.TranslationInterpolationEvaluation
