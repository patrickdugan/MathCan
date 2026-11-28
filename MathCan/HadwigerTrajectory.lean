import Init

/-! HAD-02 integer coordinate skeleton. Real convexity, gauge attainment,
and compactness are separate written arguments. Kernel replay pending. -/
namespace MathCan.HadwigerTrajectory

def base : List (Int × Int) → Int
  | [] => 0
  | (u, _) :: xs => u + base xs

def mixed : Nat → List (Int × Int) → Int
  | _, [] => 0
  | 0, xs => base xs
  | n+1, (_, w) :: xs => w + mixed n xs

def walkPrefix : Nat → Int → List (Int × Int) → Int
  | _, x, [] => x
  | 0, x, _ :: _ => x
  | n+1, x, (u, w) :: xs => walkPrefix n (x + w - u) xs

theorem prefix_identity (xs : List (Int × Int)) (j : Nat) (x : Int) :
    walkPrefix j x xs = x - base xs + mixed j xs := by
  induction xs generalizing j x with
  | nil =>
    cases j <;> simp [walkPrefix, base, mixed]
  | cons a xs ih =>
    rcases a with ⟨u, w⟩
    cases j with
    | zero => simp [walkPrefix, mixed]
    | succ j =>
      simp only [walkPrefix, mixed, base]
      rw [ih j (x + w - u)]
      omega

theorem padded_identity (xs : List (Int × Int)) (j : Nat) (x pad : Int) :
    walkPrefix j x xs - (x - base xs - pad) = mixed j xs + pad := by
  rw [prefix_identity]
  omega

theorem lifting_coordinate (p q scale e : Int)
    (h : p - q = 2 * (scale - e)) (hq : -(scale + e) ≤ q) :
    scale - 3 * e ≤ p := by
  omega

end MathCan.HadwigerTrajectory
