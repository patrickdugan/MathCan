import ApproximationMathlib.CapturedApproximation
import Mathlib.Algebra.Order.Round

/-! Constructive real quantization and coefficient accuracy. The correction is
computed by integer rounding. Projection to the register interval cannot enlarge
the error, so accuracy is independent of transport amplification and stream length. -/
namespace MathCan.JetSynthesis
open MathCan.TaylorPolynomial MathCan.TaylorTransport MathCan.TaylorFrame
open MathCan.SpatialScalar MathCan.SpatialClipped MathCan.ConcreteJetCapture
set_option autoImplicit false

noncomputable def correction (tau target prediction : ℝ) : ℤ :=
  round ((target-prediction)/tau)

noncomputable def rounded (tau target prediction : ℝ) : ℝ :=
  prediction+tau*(correction tau target prediction:ℝ)

theorem rounded_error (tau target prediction : ℝ) (htau : 0<tau) :
    |rounded tau target prediction-target| ≤ tau/2 := by
  have h:=mul_le_mul_of_nonneg_left (abs_sub_round ((target-prediction)/tau)) htau.le
  have he:rounded tau target prediction-target=
      tau*((correction tau target prediction:ℝ)-(target-prediction)/tau) := by
    unfold rounded
    field_simp
    <;> ring
  rw [he,abs_mul,abs_of_pos htau,abs_sub_comm]
  simpa only [correction,div_eq_mul_inv,mul_one,one_mul] using h

theorem clip_error (C target z : ℝ) (hC : 0≤C) (htarget : -C≤target ∧ target≤C) :
    |symmetricClip C z-target| ≤ |z-target| := by
  by_cases hl:z≤ -C
  · have hz:symmetricClip C z= -C := by
      unfold symmetricClip clip
      rw [relu_of_nonpos _ (by linarith),relu_of_nonpos _ (by linarith)]
      ring
    rw [hz,abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  · by_cases hr:C≤z
    · have hz:symmetricClip C z=C := by
        unfold symmetricClip clip
        rw [relu_of_nonneg _ (by linarith),relu_of_nonneg _ (by linarith)]
        ring
      rw [hz,abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
      linarith
    · rw [symmetric_clip_identity C z (by constructor <;> linarith)]

theorem clipped_round_error (C tau target prediction : ℝ) (hC : 0≤C) (htau : 0<tau)
    (htarget : -C≤target ∧ target≤C) :
    |symmetricClip C (rounded tau target prediction)-target| ≤ tau/2 :=
  le_trans (clip_error C target _ hC htarget) (rounded_error tau target prediction htau)

def code (N : ℕ) (c : ℤ) : ℕ := (c+(N:ℤ)).toNat

theorem code_decode (N : ℕ) (c : ℤ) (hc : -(N:ℤ)≤c) :
    (code N c:ℝ)-(N:ℝ)=(c:ℝ) := by
  have hi:((code N c:ℕ):ℤ)=c+(N:ℤ) := by
    unfold code
    exact Int.toNat_of_nonneg (by omega)
  have hr:=congrArg (fun z:ℤ=>(z:ℝ)) hi
  push_cast at hr
  linarith

theorem code_bound (N a : ℕ) (c : ℤ) (hc : -(N:ℤ)≤c ∧ c≤(N:ℤ))
    (hwidth : 2*N<2^a) : code N c<2^a := by
  have hi:((code N c:ℕ):ℤ)=c+(N:ℤ) := by
    unfold code
    exact Int.toNat_of_nonneg (by omega)
  omega

theorem correction_bound (tau target prediction B : ℝ) (N : ℕ)
    (herror : |(target-prediction)/tau|≤B) (hN : B+1/2≤(N:ℝ)) :
    -(N:ℤ)≤correction tau target prediction ∧ correction tau target prediction≤(N:ℤ) := by
  have hround:=abs_sub_round ((target-prediction)/tau)
  have hc:|(correction tau target prediction:ℝ)|≤(N:ℝ) := by
    unfold correction
    calc
      _ ≤ |round ((target-prediction)/tau)-((target-prediction)/tau)|+
          |(target-prediction)/tau| := by simpa only [sub_zero] using (abs_sub_le (round ((target-prediction)/tau):ℝ) ((target-prediction)/tau) 0)
      _ ≤ 1/2+B := add_le_add (by simpa only [abs_sub_comm] using hround) herror
      _ ≤ _ := by linarith
  have hh:=abs_le.mp hc
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

theorem total_ofFn_eq_sum {J : ℕ} (f : Fin J → ℝ) : total (List.ofFn f)=∑j,f j := by
  induction J with
  | zero => simp [total]
  | succ J ih => simp only [List.ofFn_succ,total,Fin.sum_univ_succ]; rw [ih]

theorem transport_sub {d J : ℕ} (indices : Fin J → Fin d → ℕ) (axis : Fin d)
    (h : ℝ) (v u : Fin J → ℝ) (beta : Fin J) :
    transport indices axis h (fun j=>v j-u j) beta=
      transport indices axis h v beta-transport indices axis h u beta := by
  simp only [transport,total_ofFn_eq_sum,mul_sub,Finset.sum_sub_distrib]

structure Step (d : ℕ) where
  axis : Fin d
  negative : Bool
  magnitude : ℕ

noncomputable def prediction {d J : ℕ} (indices : Fin J → Fin d → ℕ) (s : Step d)
    (v : Fin J → ℝ) : Fin J → ℝ :=
  transport indices s.axis (signedStep s.negative s.magnitude) v

noncomputable def update {d J : ℕ} (indices : Fin J → Fin d → ℕ) (C tau : ℝ)
    (s : Step d) (target v : Fin J → ℝ) : Fin J → ℝ :=
  fun beta=>symmetricClip C (rounded tau (target beta) (prediction indices s v beta))

theorem update_accuracy {d J : ℕ} (indices : Fin J → Fin d → ℕ) (C tau : ℝ)
    (hC : 0≤C) (htau : 0<tau) (s : Step d) (target v : Fin J → ℝ)
    (htarget : ∀beta,-C≤target beta ∧ target beta≤C) :
    ∀beta,|update indices C tau s target v beta-target beta|≤tau/2 := by
  intro beta
  exact clipped_round_error C tau _ _ hC htau (htarget beta)

noncomputable def frame {d J : ℕ} (indices : Fin J → Fin d → ℕ) (N : ℕ) (tau : ℝ)
    (s : Step d) (target v : Fin J → ℝ) : Frame d J :=
  ⟨s.axis,s.negative,s.magnitude,fun beta=>code N (correction tau (target beta) (prediction indices s v beta))⟩

theorem frame_update {d J : ℕ} (indices : Fin J → Fin d → ℕ) (N : ℕ) (C tau : ℝ)
    (s : Step d) (target v : Fin J → ℝ)
    (hcode : ∀beta,-(N:ℤ)≤correction tau (target beta) (prediction indices s v beta)) :
    directUpdate indices C (N:ℝ) tau (frame indices N tau s target v) v=
      update indices C tau s target v := by
  funext beta
  simp only [directUpdate,frame,update,prediction,rounded]
  have hd:=code_decode N _ (hcode beta)
  dsimp only [prediction] at hd
  simpa only [hd]

end MathCan.JetSynthesis
