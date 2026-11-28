import Init

/-!
# SPC-02: finite phase arithmetic and deferred-query state separation

This module extends SPC-01 to a six-phase Fourier model over F_7.
The primitive sixth root 3 has powers 1, 3, 2, 6, 4, 5 modulo 7.
Finite-phase uniqueness/collision facts are kernel-checked by `decide`.

The generic deferred-query injection lemma applies to any types, even
infinite ones. The paper separately proves real/complex singular-value
bounds and the binomial finite-state cardinality lower bound: those
quantitative conclusions are not claimed as Lean theorems here.
-/

namespace MathCan.SpectralStability

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- Powers of the primitive order-six root 3 in the field F_7. -/
def omega6 (e : Nat) : Nat :=
  if e % 6 == 0 then 1
  else if e % 6 == 1 then 3
  else if e % 6 == 2 then 2
  else if e % 6 == 3 then 6
  else if e % 6 == 4 then 4
  else 5

/-- The six-point Fourier synthesis with a common invertible scaling omitted. -/
def synth6 (coeff : Fin 6 → Nat) (phase : Fin 6) : Nat :=
  (((List.finRange 6).map fun f =>
      coeff f * omega6 (phase.val * f.val)).sum) % 7

/-- A single frequency with an amplitude represented by F_7. -/
def singleton6 (amp : Fin 7) (freq : Fin 6) : Fin 6 → Nat :=
  fun f => if f == freq then amp.val else 0

/-- Primitive sixth roots are pairwise distinct. -/
theorem sixth_roots_distinct :
    ∀ f g : Fin 6, omega6 f.val = omega6 g.val → f = g := by
  decide

/-- The sum over each character is zero unless it is the trivial one. -/
theorem six_phase_character_orthogonality :
    ∀ j : Fin 6,
      (((List.finRange 6).map fun s => omega6 (s.val * j.val)).sum) % 7 =
        if j.val == 0 then 6 else 0 := by
  decide

/-- Adjacent phases 0,1 distinguish any two nonzero one-tone sources. -/
theorem adjacent_phases_identify_singletons :
    ∀ a b : Fin 7, ∀ i j : Fin 6,
      a.val ≠ 0 →
      synth6 (singleton6 a i) 0 = synth6 (singleton6 b j) 0 →
      synth6 (singleton6 a i) 1 = synth6 (singleton6 b j) 1 →
      i = j := by
  decide

/-- The coprime step five also identifies the unknown single frequency. -/
theorem coprime_fifth_phase_identifies_singletons :
    ∀ a b : Fin 7, ∀ i j : Fin 6,
      a.val ≠ 0 →
      synth6 (singleton6 a i) 0 = synth6 (singleton6 b j) 0 →
      synth6 (singleton6 a i) 5 = synth6 (singleton6 b j) 5 →
      i = j := by
  decide

/-- Step two collides frequencies zero and three at both probes,
for every choice of amplitude. -/
theorem noncoprime_step_two_aliases :
    ∀ a : Fin 7,
      synth6 (singleton6 a 0) 0 = synth6 (singleton6 a 3) 0 ∧
      synth6 (singleton6 a 0) 2 = synth6 (singleton6 a 3) 2 := by
  decide

/-- All six one-tone sources have the same phase-zero output if their
amplitude is fixed; observing that phase alone loses frequency identity. -/
theorem first_phase_is_frequency_blind :
    ∀ f : Fin 6, synth6 (singleton6 1 f) 0 = 1 := by
  decide

/-- Deferred-query separation forces a deterministic monitor's stored
state to be injective on the source family. This theorem assumes exact
answers for *every* query and makes no numerical precision assumptions. -/
theorem separated_queries_force_state_injection
    {Source State Query Output : Type}
    (encode : Source → State)
    (reply : State → Query → Output)
    (correct : Source → Query → Output)
    (hcorrect : ∀ x q, reply (encode x) q = correct x q)
    (hseparate : ∀ x y, (∀ q, correct x q = correct y q) → x = y) :
    Function.Injective encode := by
  intro x y h
  apply hseparate x y
  intro q
  calc
    correct x q = reply (encode x) q := (hcorrect x q).symm
    _ = reply (encode y) q := congrArg (fun s => reply s q) h
    _ = correct y q := hcorrect y q

/-- A monitor that compresses a one-frequency F_7 source then answers
all requested Fourier phases must keep six pairwise distinct states. -/
theorem six_frequency_deferred_monitor_injective
    {State : Type}
    (encode : Fin 6 → State)
    (reply : State → Fin 6 → Nat)
    (hcorrect : ∀ f s, reply (encode f) s = omega6 (s.val * f.val)) :
    Function.Injective encode := by
  apply separated_queries_force_state_injection encode reply
      (fun f s => omega6 (s.val * f.val)) hcorrect
  intro i j h
  have hfirst := h (1 : Fin 6)
  have hroot : omega6 i.val = omega6 j.val := by
    simpa using hfirst
  exact sixth_roots_distinct i j hroot

#print axioms sixth_roots_distinct
#print axioms six_phase_character_orthogonality
#print axioms adjacent_phases_identify_singletons
#print axioms coprime_fifth_phase_identifies_singletons
#print axioms noncoprime_step_two_aliases
#print axioms first_phase_is_frequency_blind
#print axioms separated_queries_force_state_injection
#print axioms six_frequency_deferred_monitor_injective

end MathCan.SpectralStability
