import MathCan.HammingSelector

/-! Finite polynomial semantics for factorial-normalized Taylor transport.
The Pascal coefficients and polynomial operations are explicit core definitions.
No differentiability or Taylor-remainder estimate is assumed in these identities. -/
namespace MathCan.TaylorPolynomial
open Std Lean.Grind
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def choose : Nat → Nat → Nat
  | 0,0 => 1
  | 0,_+1 => 0
  | _+1,0 => 1
  | n+1,k+1 => choose n k+choose n (k+1)

theorem choose_zero (n : Nat) : choose n 0=1 := by cases n <;> rfl

theorem choose_above (n k : Nat) (h : n<k) : choose n k=0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [choose]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [choose,ih k (by omega),ih (k+1) (by omega)]

theorem choose_diagonal (n : Nat) : choose n n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose,ih,choose_above n (n+1) (by omega)]

def coefficient : List R → Nat → R
  | [],_ => 0
  | a::_,0 => a
  | _::xs,n+1 => coefficient xs n

def evaluate : List R → R → R
  | [],_ => 0
  | a::xs,x => a+x*evaluate xs x

def add : List R → List R → List R
  | [],ys => ys
  | xs,[] => xs
  | a::xs,b::ys => (a+b)::add xs ys

def scale (c : R) (xs : List R) : List R := xs.map (fun x=>c*x)
def addConstant (c : R) : List R → List R
  | [] => [c]
  | a::xs => (c+a)::xs

theorem coefficient_add (xs ys : List R) (n : Nat) :
    coefficient (add xs ys) n = coefficient xs n+coefficient ys n := by
  induction xs generalizing ys n with
  | nil => simp [add,coefficient,AddCommMonoid.zero_add]
  | cons a xs ih =>
    cases ys <;> cases n <;> simp [add,coefficient,ih,AddCommMonoid.add_zero]

theorem evaluate_add (xs ys : List R) (x : R) :
    evaluate (add xs ys) x=evaluate xs x+evaluate ys x := by
  induction xs generalizing ys with
  | nil => simp [add,evaluate,AddCommMonoid.zero_add]
  | cons a xs ih => cases ys <;> simp [add,evaluate,ih] <;> grind

theorem coefficient_scale (c : R) (xs : List R) (n : Nat) :
    coefficient (scale c xs) n=c*coefficient xs n := by
  induction xs generalizing n with
  | nil => simp [scale,coefficient,Semiring.mul_zero]
  | cons a xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

theorem evaluate_scale (c : R) (xs : List R) (x : R) :
    evaluate (scale c xs) x=c*evaluate xs x := by
  induction xs with
  | nil => simp [scale,evaluate,Semiring.mul_zero]
  | cons a xs ih => simp only [scale,List.map_cons,evaluate] at ih ⊢; rw [ih]; grind

theorem coefficient_addConstant_zero (c : R) (xs : List R) :
    coefficient (addConstant c xs) 0=c+coefficient xs 0 := by
  cases xs <;> simp [addConstant,coefficient,AddCommMonoid.add_zero]

theorem coefficient_addConstant_succ (c : R) (xs : List R) (n : Nat) :
    coefficient (addConstant c xs) (n+1)=coefficient xs (n+1) := by
  cases xs <;> rfl

theorem evaluate_addConstant (c : R) (xs : List R) (x : R) :
    evaluate (addConstant c xs) x=c+evaluate xs x := by
  cases xs <;> simp [addConstant,evaluate] <;> grind

/-- Coefficient list of (X+h)*P. -/
def affineMul (h : R) : List R → List R
  | [] => []
  | a::xs => (h*a)::addConstant a (affineMul h xs)

theorem evaluate_affineMul (h : R) (xs : List R) (x : R) :
    evaluate (affineMul h xs) x=(x+h)*evaluate xs x := by
  induction xs with
  | nil => simp [affineMul,evaluate,Semiring.mul_zero]
  | cons a xs ih => rw [affineMul,evaluate,evaluate_addConstant,ih,evaluate]; grind

theorem coefficient_affineMul_zero (h : R) (xs : List R) :
    coefficient (affineMul h xs) 0=h*coefficient xs 0 := by
  cases xs <;> simp [affineMul,coefficient,Semiring.mul_zero]

theorem coefficient_affineMul_succ (h : R) (xs : List R) (n : Nat) :
    coefficient (affineMul h xs) (n+1)=coefficient xs n+h*coefficient xs (n+1) := by
  induction xs generalizing n with
  | nil => simp [affineMul,coefficient,Semiring.mul_zero,AddCommMonoid.add_zero]
  | cons a xs ih =>
    cases n with
    | zero =>
      change coefficient (addConstant a (affineMul h xs)) 0=a+h*coefficient xs 0
      rw [coefficient_addConstant_zero,coefficient_affineMul_zero]
    | succ n =>
      change coefficient (addConstant a (affineMul h xs)) (n+1)=coefficient xs n+h*coefficient xs (n+1)
      rw [coefficient_addConstant_succ,ih]

def monomialShift (h : R) : Nat → List R
  | 0 => [1]
  | n+1 => affineMul h (monomialShift h n)

theorem monomial_shift_evaluate (h x : R) (n : Nat) :
    evaluate (monomialShift h n) x=(x+h)^n := by
  induction n with
  | zero => simp [monomialShift,evaluate,Semiring.pow_zero]; grind
  | succ n ih => rw [monomialShift,evaluate_affineMul,ih,Semiring.pow_succ]; grind

/-- The normalized derivative coefficient is binomial(n,beta)*h^(n-beta). -/
theorem monomial_shift_coefficient (h : R) (n beta : Nat) :
    coefficient (monomialShift h n) beta=(choose n beta:R)*h^(n-beta) := by
  induction n generalizing beta with
  | zero => cases beta <;> simp [monomialShift,coefficient,choose,Semiring.natCast_one,
      Semiring.natCast_zero,Semiring.pow_zero,Semiring.zero_mul,Semiring.one_mul]
  | succ n ih =>
    cases beta with
    | zero =>
      rw [monomialShift,coefficient_affineMul_zero,ih]
      simp only [choose_zero,Semiring.natCast_one,Semiring.one_mul,Nat.sub_zero,Semiring.pow_succ]
      grind
    | succ beta =>
      rw [monomialShift,coefficient_affineMul_succ,ih,ih,choose,Semiring.natCast_add]
      have he : n+1-(beta+1)=n-beta := by omega
      rw [he]
      by_cases hb:beta<n
      · have hs:n-beta=(n-(beta+1))+1 := by omega
        simp only [hs,Semiring.pow_succ]
        grind
      · by_cases heq:beta=n
        · subst beta
          simp [choose_diagonal,choose_above n (n+1) (by omega),Semiring.natCast_one,
            Semiring.natCast_zero,Semiring.pow_zero,Semiring.zero_mul,Semiring.one_mul]
          grind
        · rw [choose_above n beta (by omega),choose_above n (beta+1) (by omega)]
          simp [Semiring.natCast_zero,Semiring.zero_mul,Semiring.mul_zero,AddCommMonoid.add_zero]

def total : List R → R
  | [] => 0
  | x::xs => x+total xs

def shiftTerms (h : R) : List (Nat × R) → List R
  | [] => []
  | (n,c)::terms => add (scale c (monomialShift h n)) (shiftTerms h terms)

def evaluateTerms (terms : List (Nat × R)) (x : R) : R :=
  total (terms.map (fun t=>t.2*x^t.1))

def translatedCoefficient (terms : List (Nat × R)) (h : R) (beta : Nat) : R :=
  total (terms.map (fun t=>(choose t.1 beta:R)*h^(t.1-beta)*t.2))

/-- Exact affine substitution for every finite polynomial, of arbitrary degree. -/
theorem shift_terms_evaluate (terms : List (Nat × R)) (h x : R) :
    evaluate (shiftTerms h terms) x=evaluateTerms terms (x+h) := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    rcases t with ⟨n,c⟩
    rw [shiftTerms,evaluate_add,evaluate_scale,monomial_shift_evaluate,ih]
    rfl

theorem shift_terms_coefficient (terms : List (Nat × R)) (h : R) (beta : Nat) :
    coefficient (shiftTerms h terms) beta=translatedCoefficient terms h beta := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    rcases t with ⟨n,c⟩
    rw [shiftTerms,coefficient_add,coefficient_scale,monomial_shift_coefficient,ih]
    simp only [translatedCoefficient,List.map_cons,total]
    grind

end MathCan.TaylorPolynomial
