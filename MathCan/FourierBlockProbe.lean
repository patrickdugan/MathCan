import Init

/-!
# FPB-01: exact one-bit parity lift and Fourier cancellation

This is the independent Lean/Init arithmetic bridge to the FPB-01
Compactification Theory campaign combining OpenAI Math #132/#192.

A sign function on one bit has outputs a,b in Int.
The XOR parity lift on two independent bits has values
  (x,y)=(0,0) -> a
  (0,1) -> b
  (1,0) -> b
  (1,1) -> a.
The four-entry sums below are unnormalized Fourier numerators.

The Lean lemmas verify exact singleton cancellation, paired spectral
transport and preservation of the individual interventions.
No claim is made that the 17-bit finite example, the full selector
construction or the two external source theorems are kernel-formalized.
-/

namespace MathCan.FourierBlockProbe

/-- One-bit XOR-lifted Boolean source: observed only through x xor y. -/
def liftBit (f : Bool → Bool) (x y : Bool) : Bool :=
  f (x.xor y)

/-- Simultaneously flipping both observed registers preserves the source. -/
theorem liftBit_flip_both (f : Bool → Bool) (x y : Bool) :
    liftBit f (!x) (!y) = liftBit f x y := by
  cases x <;> cases y <;> rfl

/-- If a hidden bit matters, flipping either observed copy alone matters. -/
theorem liftBit_individual_sensitivity (f : Bool → Bool)
    (h : f false ≠ f true) :
    liftBit f false false ≠ liftBit f true false ∧
    liftBit f false false ≠ liftBit f false true := by
  constructor <;> simpa [liftBit] using h

/-- Integer-valued sign output of the lifted one-bit source. -/
def liftSign (a b : Int) (x y : Bool) : Int :=
  if x.xor y then b else a

/-- Sum of F(x,y)*chi_x over the entire two-bit sign cube.
    chi_x=+1 at x=false and -1 at x=true. -/
def singletonXNumerator (a b : Int) : Int :=
  liftSign a b false false + liftSign a b false true -
  liftSign a b true false - liftSign a b true true

/-- Analogous first-order signed coefficient in coordinate y. -/
def singletonYNumerator (a b : Int) : Int :=
  liftSign a b false false - liftSign a b false true +
  liftSign a b true false - liftSign a b true true

/-- Numerator of the matched second-order Fourier character chi_x*chi_y. -/
def pairedNumerator (a b : Int) : Int :=
  liftSign a b false false - liftSign a b false true -
  liftSign a b true false + liftSign a b true true

/-- The source one-bit signed singleton numerator is a-b,
so the lift has the paired numerator twice as large. -/
theorem paired_transport (a b : Int) :
    pairedNumerator a b = 2 * (a - b) := by
  simp [pairedNumerator, liftSign]
  omega

theorem singleton_x_cancels (a b : Int) :
    singletonXNumerator a b = 0 := by
  simp [singletonXNumerator, liftSign]

theorem singleton_y_cancels (a b : Int) :
    singletonYNumerator a b = 0 := by
  simp [singletonYNumerator, liftSign]

/-- A uniform average over four lifted points has second-order
coefficient (a-b)/2; the original one-bit coefficient has
the same value. -/
theorem paired_average_identity (a b : Int) :
    pairedNumerator a b = 2 * (a - b) := paired_transport a b

#print axioms liftBit_flip_both
#print axioms liftBit_individual_sensitivity
#print axioms paired_transport
#print axioms singleton_x_cancels
#print axioms singleton_y_cancels
#print axioms paired_average_identity

end MathCan.FourierBlockProbe
