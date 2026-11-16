import ApproximationMathlib.JetSynthesis

/-! Finite correction frames synthesized from target jets. No coefficient-
accuracy premise is assumed: rounded correction and clipping prove it. -/
namespace MathCan.FrameSynthesis
open MathCan.JetSynthesis MathCan.TaylorFrame MathCan.TaylorTransport
open MathCan.CommonGateBound MathCan.ConcreteJetCapture MathCan.SpatialClipped
set_option autoImplicit false

theorem update_range {d J : ℕ} (indices : Fin J → Fin d → ℕ) (C tau : ℝ)
    (hC : 0≤C) (s : Step d) (target v : Fin J → ℝ) :
    ∀beta,-C≤update indices C tau s target v beta ∧ update indices C tau s target v beta≤C := by
  intro beta
  exact symmetric_clip_range C _ hC

theorem prediction_bound {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (C : ℝ) (hC : 0≤C) (s : Step d)
    (hs : s.magnitude≤D) (v : Fin J → ℝ) (hv : ∀j,-C≤v j ∧ v j≤C) (beta : Fin J) :
    |prediction indices s v beta|≤C*commonBudget k D := by
  exact abs_le.mpr (transport_common_bound k D hD indices injective s.axis
    (fun j=>degree j s.axis) _ C hC (signed_step_bound s.negative s.magnitude D hs) v hv beta)

theorem frame_correct_and_valid {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D N a : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (C tau : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : (C+C*commonBudget k D)/tau+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (s : Step d) (hs : s.magnitude≤D) (target v : Fin J → ℝ)
    (htarget : ∀j,-C≤target j ∧ target j≤C) (hv : ∀j,-C≤v j ∧ v j≤C) :
    validFrame D a (frame indices N tau s target v) ∧
    directUpdate indices C (N:ℝ) tau (frame indices N tau s target v) v=update indices C tau s target v := by
  have hc:∀beta,-(N:ℤ)≤correction tau (target beta) (prediction indices s v beta) ∧
      correction tau (target beta) (prediction indices s v beta)≤(N:ℤ) := by
    intro beta
    apply correction_bound tau _ _ ((C+C*commonBudget k D)/tau) N _ hN
    rw [abs_div,abs_of_pos htau]
    apply div_le_div_of_nonneg_right _ htau.le
    calc
      _ ≤ |target beta|+|prediction indices s v beta| := abs_sub _ _
      _ ≤ C+C*commonBudget k D := add_le_add (abs_le.mpr (htarget beta))
        (prediction_bound indices k D hD injective degree C hC s hs v hv beta)
  refine ⟨⟨hs,?_⟩,frame_update indices N C tau s target v (fun beta=>(hc beta).1)⟩
  intro beta
  exact code_bound N a _ (hc beta) hwidth

noncomputable def states {d J : ℕ} (indices : Fin J → Fin d → ℕ) (C tau : ℝ) :
    List (Step d) → (ℕ → Fin J → ℝ) → (Fin J → ℝ) → ℕ → Fin J → ℝ
  | _,_,v,0 => v
  | [],_,_,_+1 => fun _=>0
  | s::tail,targets,v,i+1 => states indices C tau tail (fun j=>targets (j+1))
      (update indices C tau s (targets 1) v) i

noncomputable def frames {d J : ℕ} (indices : Fin J → Fin d → ℕ) (N : ℕ) (C tau : ℝ) :
    List (Step d) → (ℕ → Fin J → ℝ) → (Fin J → ℝ) → List (Frame d J)
  | [],_,_ => []
  | s::tail,targets,v => frame indices N tau s (targets 1) v ::
      frames indices N C tau tail (fun j=>targets (j+1)) (update indices C tau s (targets 1) v)

theorem frames_length {d J : ℕ} (indices : Fin J → Fin d → ℕ) (N : ℕ) (C tau : ℝ)
    (steps : List (Step d)) (targets : ℕ → Fin J → ℝ) (v : Fin J → ℝ) :
    (frames indices N C tau steps targets v).length=steps.length := by
  induction steps generalizing targets v with
  | nil => rfl
  | cons s tail ih => simp only [frames,List.length_cons]; rw [ih]

theorem states_accuracy {d J : ℕ} (indices : Fin J → Fin d → ℕ) (C tau : ℝ)
    (hC : 0≤C) (htau : 0<tau) (steps : List (Step d)) (targets : ℕ → Fin J → ℝ)
    (bounded : ∀i,i≤steps.length → ∀beta,-C≤targets i beta ∧ targets i beta≤C)
    (v : Fin J → ℝ) (initial : ∀beta,|v beta-targets 0 beta|≤tau/2) :
    ∀i,i≤steps.length → ∀beta,|states indices C tau steps targets v i beta-targets i beta|≤tau/2 := by
  induction steps generalizing targets v with
  | nil =>
    intro i hi
    have he:i=0:=by simpa using hi
    subst i
    exact initial
  | cons s tail ih =>
    intro i hi
    cases i with
    | zero => exact initial
    | succ i =>
      exact ih (fun j=>targets (j+1)) (fun j hj=>bounded (j+1) (by simp only [List.length_cons] at hi ⊢; omega))
        (update indices C tau s (targets 1) v) (update_accuracy indices C tau hC htau s _ v (bounded 1 (by simp)))
        i (by simp only [List.length_cons] at hi; omega)

theorem frames_valid_exact {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D N a : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (C tau : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : (C+C*commonBudget k D)/tau+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (steps : List (Step d)) (valid : ∀s,s∈steps → s.magnitude≤D)
    (targets : ℕ → Fin J → ℝ)
    (bounded : ∀i,i≤steps.length → ∀beta,-C≤targets i beta ∧ targets i beta≤C)
    (v : Fin J → ℝ) (hv : ∀beta,-C≤v beta ∧ v beta≤C) :
    (∀f,f∈frames indices N C tau steps targets v → validFrame D a f) ∧
    (∀i,referenceAt indices C (N:ℝ) tau (frames indices N C tau steps targets v) v i=
      states indices C tau steps targets v i) := by
  induction steps generalizing targets v with
  | nil => exact ⟨by simp [frames],by intro i; cases i <;> rfl⟩
  | cons s tail ih =>
    have hs:=valid s (by simp)
    have head:=frame_correct_and_valid indices k D N a hD injective degree C tau hC htau hN hwidth s hs
      (targets 1) v (bounded 1 (by simp)) hv
    have rest:=ih (fun t ht=>valid t (by simp [ht])) (fun j=>targets (j+1))
      (fun j hj=>bounded (j+1) (by simp only [List.length_cons]; omega))
      (update indices C tau s (targets 1) v) (update_range indices C tau hC s _ v)
    constructor
    · intro f hf
      simp only [frames,List.mem_cons] at hf
      rcases hf with he | he
      · subst f; exact head.1
      · exact rest.1 f he
    · intro i
      cases i with
      | zero => rfl
      | succ i => simp only [frames,referenceAt,states]; rw [head.2]; exact rest.2 i

noncomputable def initial {J : ℕ} (C tau : ℝ) (target : Fin J → ℝ) : Fin J → ℝ :=
  fun beta=>symmetricClip C (rounded tau (target beta) 0)

theorem initial_range {J : ℕ} (C tau : ℝ) (hC : 0≤C) (target : Fin J → ℝ) :
    ∀beta,-C≤ initial C tau target beta ∧ initial C tau target beta≤C := by
  intro beta
  exact symmetric_clip_range C _ hC

theorem initial_accuracy {J : ℕ} (C tau : ℝ) (hC : 0≤C) (htau : 0<tau) (target : Fin J → ℝ)
    (bounded : ∀beta,-C≤target beta ∧ target beta≤C) :
    ∀beta,|initial C tau target beta-target beta|≤tau/2 := by
  intro beta
  exact clipped_round_error C tau _ 0 hC htau (bounded beta)

end MathCan.FrameSynthesis
