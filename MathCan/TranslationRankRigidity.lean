import Init

/-!
# TRR-01: finite counting and translation-error stability

The orbit is supplied as distinct nonzero coordinate vectors. The passage
from a finite-field translate module to these coordinates is in the written
proof, not an imported field or rank theory. The Hamming result is proved
on finite lists and applies to any shift permuting the enumeration.
-/ 

namespace MathCan.TranslationRankRigidity

set_option maxHeartbeats 1500000

/-- Pigeonhole principle without a Mathlib dependency. Remove the last image
    and compress the remaining range by one. -/
theorem fin_injection_bound (n : Nat) :
    ∀ (m : Nat) (f : Fin m → Fin n), Function.Injective f → m ≤ n := by
  induction n with
  | zero =>
    intro m f hf
    cases m with
    | zero => exact Nat.le_refl 0
    | succ m =>
      have h := (f ⟨0, Nat.zero_lt_succ m⟩).isLt
      omega
  | succ n ih =>
    intro m f hf
    cases m with
    | zero => exact Nat.zero_le _
    | succ m =>
      let last : Fin (m+1) := ⟨m, Nat.lt_succ_self m⟩
      let inc : Fin m → Fin (m+1) := fun i =>
        ⟨i.val, by have h := i.isLt; omega⟩
      let cut : Nat := (f last).val
      have hc : cut < n+1 := (f last).isLt
      have avoids : ∀ i : Fin m, (f (inc i)).val ≠ cut := by
        intro i h
        have hh : f (inc i) = f last := Fin.ext h
        have hv := congrArg (fun z : Fin (m+1) => z.val) (hf hh)
        change i.val = m at hv
        have hi := i.isLt
        omega
      let g : Fin m → Fin n := fun i =>
        ⟨if (f (inc i)).val < cut then (f (inc i)).val
          else (f (inc i)).val - 1, by
          have hi := (f (inc i)).isLt
          have ha := avoids i
          by_cases ht : (f (inc i)).val < cut
          · simp only [if_pos ht] <;> omega
          · simp only [if_neg ht] <;> omega⟩
      have hg : Function.Injective g := by
        intro i j h
        have he := congrArg (fun z : Fin n => z.val) h
        change
          (if (f (inc i)).val < cut then (f (inc i)).val else (f (inc i)).val - 1) =
          (if (f (inc j)).val < cut then (f (inc j)).val else (f (inc j)).val - 1) at he
        have hi := avoids i
        have hj := avoids j
        have hv : (f (inc i)).val = (f (inc j)).val := by
          by_cases h1 : (f (inc i)).val < cut <;>
            by_cases h2 : (f (inc j)).val < cut <;>
            simp [h1, h2] at he <;> omega
        have hh := hf (Fin.ext hv)
        exact Fin.ext (congrArg (fun z : Fin (m+1) => z.val) hh)
      have hm := ih m g hg
      omega

theorem nonzero_code_bound (n capacity : Nat)
    (encode : Fin n → Fin capacity)
    (hinj : Function.Injective encode)
    (hnz : ∀ i, 0 < (encode i).val) : n ≤ capacity-1 := by
  let g : Fin n → Fin (capacity-1) := fun i =>
    ⟨(encode i).val-1, by
      have hb := (encode i).isLt
      have hp := hnz i
      omega⟩
  apply fin_injection_bound (capacity-1) n g
  intro i j h
  have hv := congrArg (fun z : Fin (capacity-1) => z.val) h
  change (encode i).val-1 = (encode j).val-1 at hv
  have hi := hnz i
  have hj := hnz j
  exact hinj (Fin.ext (by omega))

/-- A mixed-radix digit with its remaining word. -/
def digitPair (q n : Nat) (a : Fin q) (b : Fin n) : Fin (n*q) :=
  ⟨b.val*q+a.val, by
    have hm : (b.val+1)*q ≤ n*q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt b.isLt)
    rw [Nat.add_mul, Nat.one_mul] at hm
    have ha := a.isLt
    omega⟩

theorem digitPair_injective {q n : Nat} {a a' : Fin q} {b b' : Fin n}
    (h : digitPair q n a b = digitPair q n a' b') :
    a = a' ∧ b = b' := by
  have hv := congrArg (fun z : Fin (n*q) => z.val) h
  change b.val*q+a.val = b'.val*q+a'.val at hv
  have ha := a.isLt
  have ha' := a'.isLt
  have hb : b.val = b'.val := by
    by_cases hl : b.val < b'.val
    · have hm : (b.val+1)*q ≤ b'.val*q :=
        Nat.mul_le_mul_right q (Nat.succ_le_of_lt hl)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    · by_cases hr : b'.val < b.val
      · have hm : (b'.val+1)*q ≤ b.val*q :=
          Nat.mul_le_mul_right q (Nat.succ_le_of_lt hr)
        rw [Nat.add_mul, Nat.one_mul] at hm
        omega
      · omega
  rw [hb] at hv
  exact ⟨Fin.ext (by omega), Fin.ext hb⟩

/-- Exact base-q encoding of r coordinates. -/
def encodeDigits (q : Nat) : (r : Nat) → (Fin r → Fin q) → Fin (q^r)
  | 0, _ => ⟨0, by decide⟩
  | r+1, v =>
      digitPair q (q^r) (v 0) (encodeDigits q r (fun i => v i.succ))

theorem encodeDigits_injective (q r : Nat) :
    Function.Injective (encodeDigits q r) := by
  induction r with
  | zero =>
    intro a b _
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    intro a b h
    have hpair :
        digitPair q (q^r) (a 0) (encodeDigits q r (fun i => a i.succ)) =
        digitPair q (q^r) (b 0) (encodeDigits q r (fun i => b i.succ)) := h
    obtain ⟨h0, ht⟩ := digitPair_injective hpair
    have hrest := ih ht
    funext i
    exact Fin.cases h0 (fun j => congrFun hrest j) i

theorem encodeDigits_zero (q r : Nat) (z : Fin q) (hz : z.val=0) :
    (encodeDigits q r (fun _ => z)).val=0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (encodeDigits q r (fun _ => z)).val*q+z.val=0
    rw [ih, hz] <;> simp

/-- Cardinal bound for a finite orbit of distinct nonzero r-coordinate words.
    A field basis and an enumeration of its Q elements supply the hypotheses. -/
theorem coordinate_orbit_bound (Q r orbit : Nat) (hQ : 0<Q)
    (coords : Fin orbit → (Fin r → Fin Q))
    (hinj : Function.Injective coords)
    (hnz : ∀ i, ∃ j, (coords i j).val ≠ 0) :
    orbit ≤ Q^r-1 := by
  let z : Fin Q := ⟨0,hQ⟩
  apply nonzero_code_bound orbit (Q^r) (fun i => encodeDigits Q r (coords i))
  · intro i j h
    exact hinj (encodeDigits_injective Q r h)
  · intro i
    by_cases h : (encodeDigits Q r (coords i)).val=0
    · have hz := encodeDigits_zero Q r z rfl
      have hc : encodeDigits Q r (coords i) =
          encodeDigits Q r (fun _ => z) := Fin.ext (h.trans hz.symm)
      have he := encodeDigits_injective Q r hc
      obtain ⟨j,hj⟩ := hnz i
      have hj0 : (coords i j).val = 0 :=
        congrArg (fun x : Fin Q => x.val) (congrFun he j)
      exact False.elim (hj hj0)
    · omega

/-- One unit of Hamming loss for unequal symbols. -/
def mismatch {V : Type} [DecidableEq V] (a b : V) : Nat :=
  if a=b then 0 else 1

theorem mismatch_triangle {V : Type} [DecidableEq V] (a b c : V) :
    mismatch a c ≤ mismatch a b + mismatch b c := by
  by_cases hab : a=b
  · subst b
    simp [mismatch]
  · by_cases hbc : b=c
    · subst c
      simp [mismatch]
    · by_cases hac : a=c <;> simp [mismatch, hab, hbc, hac]

theorem mismatch_symm {V : Type} [DecidableEq V] (a b : V) :
    mismatch a b = mismatch b a := by
  by_cases hab : a=b
  · subst b
    rfl
  · have hba : b ≠ a := fun h => hab h.symm
    simp [mismatch, hab, hba]

def hamming {X V : Type} [DecidableEq V] (xs : List X) (f g : X → V) : Nat :=
  match xs with
  | [] => 0
  | a::rest => mismatch (f a) (g a) + hamming rest f g

theorem hamming_triangle {X V : Type} [DecidableEq V] (xs : List X)
    (f g h : X → V) :
    hamming xs f h ≤ hamming xs f g + hamming xs g h := by
  induction xs with
  | nil => simp [hamming]
  | cons a rest ih =>
    have hp := mismatch_triangle (f a) (g a) (h a)
    simp only [hamming]
    omega

theorem hamming_symm {X V : Type} [DecidableEq V] (xs : List X)
    (f g : X → V) : hamming xs f g = hamming xs g f := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [hamming, ih, mismatch_symm (f a) (g a)]

theorem hamming_perm {X V : Type} [DecidableEq V] {xs ys : List X}
    (hp : xs.Perm ys) (f g : X → V) :
    hamming xs f g = hamming ys f g := by
  induction hp with
  | nil => rfl
  | cons a p ih => simp only [hamming, ih]
  | swap a b rest => simp only [hamming]; omega
  | trans p1 p2 ih1 ih2 => exact ih1.trans ih2

theorem hamming_map {X V : Type} [DecidableEq V] (xs : List X)
    (shift : X → X) (f g : X → V) :
    hamming (xs.map shift) f g =
      hamming xs (fun x => f (shift x)) (fun x => g (shift x)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, hamming, ih]

/-- Any perturbation making a shift into a period must pay at least
    half of the original shift distance. -/
theorem periodic_shift_distance {X V : Type} [DecidableEq V]
    (xs : List X) (shift : X → X) (f g : X → V)
    (hp : (xs.map shift).Perm xs) (period : ∀ x, g (shift x)=g x) :
    hamming xs f (fun x => f (shift x)) ≤ 2*hamming xs f g := by
  have hm := hamming_map xs shift g f
  have hperm := hamming_perm hp g f
  have hfix : (fun x => g (shift x)) = g := funext period
  rw [hfix] at hm
  have hshift : hamming xs g (fun x => f (shift x)) = hamming xs g f :=
    hm.symm.trans hperm
  have ht := hamming_triangle xs f g (fun x => f (shift x))
  have hs := hamming_symm xs g f
  omega

theorem periodic_error_budget {X V : Type} [DecidableEq V]
    (xs : List X) (shift : X → X) (f g : X → V) (k s : Nat)
    (hp : (xs.map shift).Perm xs) (period : ∀ x, g (shift x)=g x)
    (hgap : s ≤ hamming xs f (fun x => f (shift x)))
    (herr : hamming xs f g ≤ k) : s ≤ 2*k := by
  have h := periodic_shift_distance xs shift f g hp period
  omega

/-- Arithmetic step of the clean-submatrix proof: 'bad' is the size of
    the union of corrupted column sets of ell chosen rows. -/
theorem clean_block_budget (N k ell bad : Nat)
    (hsize : ell*(k+1) ≤ N) (hbad : bad ≤ ell*k) :
    ell ≤ N-bad := by
  rw [Nat.mul_add, Nat.mul_one] at hsize
  omega

/-- Arithmetic step of the pole proof after a nonzero relation is chosen
    and its zero and exceptional point budgets have been established. -/
theorem pole_zero_budget (N r d t k : Nat)
    (hzeros : N-(r+1)*(t+k) ≤ (r+1)*d) :
    N ≤ (r+1)*(d+t+k) := by
  have he : (r+1)*(d+t+k) = (r+1)*d+(r+1)*(t+k) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [he]
  omega

#print axioms fin_injection_bound
#print axioms nonzero_code_bound
#print axioms digitPair_injective
#print axioms encodeDigits_injective
#print axioms encodeDigits_zero
#print axioms coordinate_orbit_bound
#print axioms mismatch_triangle
#print axioms mismatch_symm
#print axioms hamming_triangle
#print axioms hamming_symm
#print axioms hamming_perm
#print axioms hamming_map
#print axioms periodic_shift_distance
#print axioms periodic_error_budget
#print axioms clean_block_budget
#print axioms pole_zero_budget

end MathCan.TranslationRankRigidity
