import Mathlib

namespace SpectralGeometry

theorem interior_insertion (a b c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    max (max a b) c - min (min a b) c = b - a := by
  have hab : a ≤ b := le_trans hac hcb
  simp only [max_eq_right hab, max_eq_left hcb, min_eq_left hab, min_eq_left hac]

theorem interior_cost (a b c bits : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (max (max a b) c - min (min a b) c) * bits = (b - a) * bits := by
  rw [interior_insertion a b c hac hcb]

theorem wire_concat (a b c : ℝ) : (b - a) + (c - b) = c - a := by
  ring

theorem soft_three_site (a b c p q r : ℝ) :
    p*q*(1-r)*(b-a) + p*(1-q)*r*(c-a) +
      (1-p)*q*r*(c-b) + p*q*r*(c-a) =
    (b-a)*p*(1-(1-q)*(1-r)) + (c-b)*(1-(1-p)*(1-q))*r := by
  ring

#print axioms interior_insertion
#print axioms interior_cost
#print axioms wire_concat
#print axioms soft_three_site

end SpectralGeometry
