import Lean

/-!
DETFACT-15: exact streamed modular power semantics and singleton packing.

This abstract natural-number model covers arbitrary bases, including
nonunits. Prime enumeration completeness, the lcm prime factorization
formula, the native C implementation and the upstream relation
production theorem are separate proof obligations.
-/
namespace MathCan.DETFACT15Stream

theorem reduce_left (a b n : Nat) :
    ((a % n) * b) % n = (a * b) % n := by
  calc
    ((a % n) * b) % n =
        ((a % n) * b + n * ((a / n) * b)) % n :=
      (Nat.add_mul_mod_self_left _ _ _).symm
    _ = ((a % n + n * (a / n)) * b) % n := by
      rw [Nat.add_mul, Nat.mul_assoc]
    _ = (a * b) % n := by rw [Nat.mod_add_div]

theorem reduce_right (a b n : Nat) :
    (a * (b % n)) % n = (a * b) % n := by
  rw [Nat.mul_comm a (b % n), reduce_left, Nat.mul_comm b a]

theorem reduce_power_base (a n e : Nat) :
    (a % n) ^ e % n = a ^ e % n := by
  induction e with
  | zero => simp
  | succ e ih =>
    simp only [Nat.pow_succ]
    calc
      ((a % n) ^ e * (a % n)) % n =
          (((a % n) ^ e % n) * (a % n)) % n :=
        (reduce_left _ _ _).symm
      _ = ((a ^ e % n) * (a % n)) % n := by rw [ih]
      _ = (a ^ e * (a % n)) % n := reduce_left _ _ _
      _ = (a ^ e * a) % n := reduce_right _ _ _

theorem modular_power_composition (a n e f : Nat) :
    (a ^ e % n) ^ f % n = a ^ (e * f) % n := by
  rw [reduce_power_base, Nat.pow_mul]

def exponentProduct : List Nat → Nat
  | [] => 1
  | q :: qs => q * exponentProduct qs

def execute (n a : Nat) : List Nat → Nat
  | [] => a % n
  | q :: qs => execute n (a ^ q % n) qs

theorem streamed_power_eq (n a : Nat) (qs : List Nat) :
    execute n a qs = a ^ exponentProduct qs % n := by
  induction qs generalizing a with
  | nil => simp [execute, exponentProduct]
  | cons q qs ih =>
    change execute n (a ^ q % n) qs =
      a ^ (q * exponentProduct qs) % n
    rw [ih]
    exact modular_power_composition a n q (exponentProduct qs)

theorem product_append (xs ys : List Nat) :
    exponentProduct (xs ++ ys) = exponentProduct xs * exponentProduct ys := by
  induction xs with
  | nil => simp [exponentProduct]
  | cons q qs ih =>
    simp only [List.cons_append, exponentProduct, ih, Nat.mul_assoc]

/-- Checkpoint state is trusted only when it equals the verified prefix. -/
theorem checkpoint_resume (n a : Nat) (xs ys : List Nat) :
    execute n (execute n a xs) ys = execute n a (xs ++ ys) := by
  calc
    execute n (execute n a xs) ys =
        (a ^ exponentProduct xs % n) ^ exponentProduct ys % n := by
      rw [streamed_power_eq n (execute n a xs) ys, streamed_power_eq n a xs]
    _ = a ^ (exponentProduct xs * exponentProduct ys) % n :=
      modular_power_composition _ _ _ _
    _ = execute n a (xs ++ ys) := by
      rw [streamed_power_eq, product_append]

/-- Any replacement chunk list with the same product has the same semantics. -/
theorem equal_product_execution (n a : Nat) (xs ys : List Nat)
    (h : exponentProduct xs = exponentProduct ys) :
    execute n a xs = execute n a ys := by
  rw [streamed_power_eq n a xs, streamed_power_eq n a ys, h]

def squareTrace (n x : Nat) : Nat → Nat
  | 0 => x % n
  | j + 1 => squareTrace n x j ^ 2 % n

theorem square_trace_eq (n x j : Nat) :
    squareTrace n x j = x ^ (2 ^ j) % n := by
  induction j with
  | zero => simp [squareTrace]
  | succ j ih =>
    change squareTrace n x j ^ 2 % n = x ^ (2 ^ (j + 1)) % n
    rw [ih, modular_power_composition, Nat.pow_succ]

theorem split_residue_eq (n a j : Nat) (qs : List Nat) :
    squareTrace n (execute n a qs) j =
      a ^ (exponentProduct qs * 2 ^ j) % n := by
  rw [square_trace_eq, streamed_power_eq]
  exact modular_power_composition _ _ _ _

/-- abs(x-1) in Nat, including x=0. This is the native gcd input. -/
def gcdInput (x : Nat) : Nat := if x = 0 then 1 else x - 1

def splitProbe (n x j : Nat) : Nat :=
  Nat.gcd (gcdInput (squareTrace n x j)) n

theorem split_probe_eq (n a j : Nat) (qs : List Nat) :
    splitProbe n (execute n a qs) j =
      Nat.gcd (gcdInput (a ^ (exponentProduct qs * 2 ^ j) % n)) n := by
  unfold splitProbe
  rw [split_residue_eq]

/-- A maximal prime power q satisfies p ≤ q and K < p*q.
These two integer premises suffice: primality is unnecessary here. -/
theorem maximal_power_square_gt (K p q : Nat)
    (hp : p ≤ q) (hnext : K < p * q) : K < q * q := by
  have hmul : p * q ≤ q * q := Nat.mul_le_mul hp (Nat.le_refl q)
  omega

theorem maximal_power_above_threshold (K p q t : Nat)
    (hp : p ≤ q) (hnext : K < p * q)
    (hK : t * t ≤ K) : t < q := by
  have hsq := maximal_power_square_gt K p q hp hnext
  by_cases h : q ≤ t
  · have hm : q * q ≤ t * t := Nat.mul_le_mul h h
    omega
  · omega

/-- If q fits in w bits and K ≥ (2^t)^2, its width is greater than t. -/
theorem maximal_power_width (K p q t w : Nat)
    (hp : p ≤ q) (hnext : K < p * q)
    (hK : (2 ^ t) * (2 ^ t) ≤ K) (hwidth : q < 2 ^ w) :
    t < w := by
  have hq := maximal_power_above_threshold K p q (2 ^ t) hp hnext hK
  by_cases h : w ≤ t
  · have hm : 2 ^ w ≤ 2 ^ t := Nat.pow_le_pow_of_le (by decide) h
    omega
  · omega

/-- The conservative sum-of-bit-widths rule rejects a pair at width 2*t.
This is a sufficient threshold, not a proof of its sharpness. -/
theorem singleton_guard (K p₁ p₂ q₁ q₂ w₁ w₂ t : Nat)
    (hp₁ : p₁ ≤ q₁) (hp₂ : p₂ ≤ q₂)
    (hn₁ : K < p₁ * q₁) (hn₂ : K < p₂ * q₂)
    (hK : (2 ^ t) * (2 ^ t) ≤ K)
    (hw₁ : q₁ < 2 ^ w₁) (hw₂ : q₂ < 2 ^ w₂) :
    2 * t < w₁ + w₂ := by
  have h₁ := maximal_power_width K p₁ q₁ t w₁ hp₁ hn₁ hK hw₁
  have h₂ := maximal_power_width K p₂ q₂ t w₂ hp₂ hn₂ hK hw₂
  omega

theorem static16_singleton_guard (K p₁ p₂ q₁ q₂ w₁ w₂ : Nat)
    (hp₁ : p₁ ≤ q₁) (hp₂ : p₂ ≤ q₂)
    (hn₁ : K < p₁ * q₁) (hn₂ : K < p₂ * q₂)
    (hK : 65536 ≤ K)
    (hw₁ : q₁ < 2 ^ w₁) (hw₂ : q₂ < 2 ^ w₂) :
    16 < w₁ + w₂ := by
  exact singleton_guard K p₁ p₂ q₁ q₂ w₁ w₂ 8 hp₁ hp₂ hn₁ hn₂ hK hw₁ hw₂

#print axioms reduce_power_base
#print axioms streamed_power_eq
#print axioms checkpoint_resume
#print axioms equal_product_execution
#print axioms split_probe_eq
#print axioms maximal_power_width
#print axioms singleton_guard
#print axioms static16_singleton_guard
end MathCan.DETFACT15Stream
