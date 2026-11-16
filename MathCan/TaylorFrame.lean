import MathCan.TaylorTransport

/-! Fixed-width displacement and correction frames, parsed into a concrete
Hamming-selected Taylor matrix update. Gate bounds are computed finite row
budgets depending only on the fixed index layout and displacement alphabet. -/
namespace MathCan.TaylorFrame
open Std Lean.Grind MathCan.SpatialScalar MathCan.SentinelDecoder MathCan.DecodedJetCapture
open MathCan.HammingSelector MathCan.TaylorPolynomial MathCan.TaylorTransport
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def blockAt {A : Type v} (width : Nat) (xs : List A) : Nat → List A
  | 0 => xs.take width
  | j+1 => blockAt width (xs.drop width) j

theorem block_at_window {A : Type v} (width : Nat) (xs : List A) (j : Nat) :
    blockAt width xs j=(xs.drop (width*j)).take width := by
  induction j generalizing xs with
  | zero => simp [blockAt]
  | succ j ih => rw [blockAt,ih,List.drop_drop,Nat.mul_succ]; congr 2; omega

theorem block_at_map {A : Type v} {B : Type w} (f : A → B) (width : Nat) (xs : List A) (j : Nat) :
    blockAt width (xs.map f) j=(blockAt width xs j).map f := by
  induction j generalizing xs with
  | zero => simp [blockAt,List.map_take]
  | succ j ih => simp only [blockAt,← List.map_drop]; exact ih _

theorem block_at_ofFn {A : Type v} (J width : Nat) (blocks : Fin J → List A)
    (hlen:∀ j,(blocks j).length=width) (j : Fin J) :
    blockAt width (List.ofFn blocks).flatten j.val=blocks j := by
  induction J with
  | zero => exact Fin.elim0 j
  | succ J ih =>
    cases j using Fin.cases with
    | zero =>
      rw [List.ofFn_succ,List.flatten_cons]
      change ((blocks 0)++_).take width=blocks 0
      exact List.take_left' (hlen 0)
    | succ j =>
      rw [List.ofFn_succ,List.flatten_cons]
      change blockAt width (((blocks 0)++_).drop width) j.val=blocks j.succ
      rw [List.drop_left' (hlen 0)]
      exact ih (fun i=>blocks i.succ) (fun i=>hlen i.succ) j

theorem blocks_length {A : Type v} (J width : Nat) (blocks : Fin J → List A)
    (hlen:∀ j,(blocks j).length=width) : (List.ofFn blocks).flatten.length=width*J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [List.ofFn_succ,List.flatten_cons,List.length_append,hlen 0,
      ih (fun j=>blocks j.succ) (fun j=>hlen j.succ),Nat.mul_succ]
    omega

def framePayload {J : Nat} (p a q : Nat) (correction : Fin J → Nat) : List Bool :=
  digits p q ++ (List.ofFn (fun beta=>digits a (correction beta))).flatten

theorem frame_payload_length {J : Nat} (p a q : Nat) (correction : Fin J → Nat) :
    (framePayload p a q correction).length=p+a*J := by
  rw [framePayload,List.length_append,digits_length,blocks_length J a _ (fun j=>digits_length a _)]

theorem frame_amplitude_prefix {J : Nat} (p a q : Nat) (correction : Fin J → Nat) :
    ((framePayload p a q correction).map (bit (R:=R))).take p=(digits p q).map bit := by
  rw [← List.map_take]
  apply congrArg (List.map bit)
  exact List.take_left' (digits_length p q)

theorem frame_correction_window {J : Nat} (p a q : Nat) (correction : Fin J → Nat) (beta : Fin J) :
    blockAt a (((framePayload p a q correction).map (bit (R:=R))).drop p) beta.val =
      (digits a (correction beta)).map bit := by
  rw [← List.map_drop,block_at_map]
  apply congrArg (List.map bit)
  unfold framePayload
  rw [List.drop_left' (digits_length p q)]
  exact block_at_ofFn J a _ (fun j=>digits_length a _) beta

theorem frame_correction_value {J : Nat} (p a q : Nat) (correction : Fin J → Nat)
    (hcor:∀ beta,correction beta<2^a) (beta : Fin J) :
    unsignedLE (blockAt a (((framePayload p a q correction).map (bit (R:=R))).drop p) beta.val)=
      (correction beta:R) := by
  rw [frame_correction_window,unsigned_bits_exact,digits_value a _ (hcor beta)]

def selectedUpdate {d J : Nat} (indices : Fin J → Fin d → Nat) (axis : Fin d)
    (negative : Bool) (D p a : Nat) (C centre tau : R)
    (v : Fin J → R) (payload : List R) : Fin J → R := fun beta =>
  chooseScalar D p (C*rowBudget D indices axis beta) (payload.take p)
    (fun q=>transport indices axis (signedStep negative q) v beta) +
  tau*(unsignedLE (blockAt a (payload.drop p) beta.val)-centre)

/-- The actual one-hot gate circuit computes the selected transport and all
signed correction coordinates; no candidate-bound oracle is assumed. -/
theorem selected_update_frame {d J : Nat} (indices : Fin J → Fin d → Nat) (axis : Fin d)
    (negative : Bool) (D p a q : Nat) (hwidth:D<2^p) (hq:q≤D)
    (C centre tau : R) (hC:0≤C) (v : Fin J → R) (hv:∀ beta,-C≤v beta ∧ v beta≤C)
    (correction : Fin J → Nat) (hcor:∀ beta,correction beta<2^a) :
    selectedUpdate indices axis negative D p a C centre tau v
      ((framePayload p a q correction).map bit) =
      (fun beta=>transport indices axis (signedStep negative q) v beta+
        tau*((correction beta:R)-centre)) := by
  funext beta
  unfold selectedUpdate
  rw [frame_amplitude_prefix,frame_correction_value p a q correction hcor beta]
  rw [choose_scalar_exact D p q hwidth hq _ _ (by
    intro r hr
    exact transport_bound D indices axis _ C hC (signed_step_bound negative r D hr) v hv beta)]

structure Frame (d J : Nat) where
  axis : Fin d
  negative : Bool
  magnitude : Nat
  correction : Fin J → Nat

def validFrame {d J : Nat} (D a : Nat) (f : Frame d J) : Prop :=
  f.magnitude≤D ∧ ∀ beta,f.correction beta<2^a

def payload {d J : Nat} (p a : Nat) (f : Frame d J) : List Bool :=
  framePayload p a f.magnitude f.correction

def directUpdate {d J : Nat} (indices : Fin J → Fin d → Nat) (C centre tau : R)
    (f : Frame d J) (v : Fin J → R) : Fin J → R := fun beta =>
  MathCan.SpatialClipped.symmetricClip C
    (transport indices f.axis (signedStep f.negative f.magnitude) v beta+
      tau*((f.correction beta:R)-centre))

theorem direct_update_range {d J : Nat} (indices : Fin J → Fin d → Nat) (C centre tau : R)
    (hC:0≤C) (f : Frame d J) (v : Fin J → R) :
    ∀ beta,-C≤directUpdate indices C centre tau f v beta ∧ directUpdate indices C centre tau f v beta≤C := by
  intro beta
  exact MathCan.SpatialClipped.symmetric_clip_range C _ hC

theorem bounded_selected_update_frame {d J : Nat} (indices : Fin J → Fin d → Nat)
    (D p a : Nat) (hwidth:D<2^p) (C centre tau : R) (hC:0≤C)
    (f : Frame d J) (hf:validFrame D a f) (v : Fin J → R) (hv:∀ beta,-C≤v beta ∧ v beta≤C) :
    boundedUpdate C (selectedUpdate indices f.axis f.negative D p a C centre tau) v
      ((payload p a f).map bit) = directUpdate indices C centre tau f v := by
  have hh:=selected_update_frame indices f.axis f.negative D p a f.magnitude hwidth hf.1
    C centre tau hC v hv f.correction hf.2
  unfold payload
  unfold boundedUpdate
  rw [hh]
  rfl

end MathCan.TaylorFrame
