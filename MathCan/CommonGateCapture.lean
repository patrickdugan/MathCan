import MathCan.CommonGateBound

/-! One common gate bound for the entire scheduled Taylor decoder. -/
namespace MathCan.CommonGateCapture
open Std Lean.Grind MathCan.SpatialScalar MathCan.SpatialRouting
open MathCan.SpatialNormalized MathCan.SpatialClipped MathCan.SentinelDecoder
open MathCan.DecodedJetCapture MathCan.TaylorTransport MathCan.TaylorFrame
open MathCan.HammingSelector MathCan.CommonGateBound MathCan.ConcreteJetCapture
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def commonUpdate {d J : Nat} (indices : Fin J → Fin d → Nat) (axis : Fin d)
    (negative : Bool) (k D p a : Nat) (C centre tau : R)
    (v : Fin J → R) (payload : List R) : Fin J → R := fun beta =>
  chooseScalar D p (C*commonBudget k D) (payload.take p)
    (fun q=>transport indices axis (signedStep negative q) v beta) +
  tau*(unsignedLE (blockAt a (payload.drop p) beta.val)-centre)

/-- The actual one-hot gate circuit computes the selected transport and all
signed correction coordinates; no candidate-bound oracle is assumed. -/
theorem common_update_frame {d J : Nat} (indices : Fin J → Fin d → Nat) (axis : Fin d)
    (negative : Bool) (k D p a q : Nat) (hD:1≤D)
    (injective:∀ j l,indices j=indices l → j=l) (degree:∀ gamma j,indices gamma j≤k) (hwidth:D<2^p) (hq:q≤D)
    (C centre tau : R) (hC:0≤C) (v : Fin J → R) (hv:∀ beta,-C≤v beta ∧ v beta≤C)
    (correction : Fin J → Nat) (hcor:∀ beta,correction beta<2^a) :
    commonUpdate indices axis negative k D p a C centre tau v
      ((framePayload p a q correction).map bit) =
      (fun beta=>transport indices axis (signedStep negative q) v beta+
        tau*((correction beta:R)-centre)) := by
  funext beta
  unfold commonUpdate
  rw [frame_amplitude_prefix,frame_correction_value p a q correction hcor beta]
  rw [choose_scalar_exact D p q hwidth hq _ _ (by
    intro r hr
    exact transport_common_bound k D hD indices injective axis (fun gamma=>degree gamma axis) _ C hC (signed_step_bound negative r D hr) v hv beta)]

theorem bounded_common_update_frame {d J : Nat} (indices : Fin J → Fin d → Nat)
    (k D p a : Nat) (hD:1≤D) (injective:∀ j l,indices j=indices l → j=l)
    (degree:∀ gamma j,indices gamma j≤k) (hwidth:D<2^p) (C centre tau : R) (hC:0≤C)
    (f : Frame d J) (hf:validFrame D a f) (v : Fin J → R) (hv:∀ beta,-C≤v beta ∧ v beta≤C) :
    boundedUpdate C (commonUpdate indices f.axis f.negative k D p a C centre tau) v
      ((payload p a f).map bit) = directUpdate indices C centre tau f v := by
  have hh:=common_update_frame indices f.axis f.negative k D p a f.magnitude hD injective degree hwidth hf.1
    C centre tau hC v hv f.correction hf.2
  unfold payload boundedUpdate
  rw [hh]
  rfl

def commonScheduledAt {d J : Nat} (indices : Fin J → Fin d → Nat) (k D p a : Nat) (C centre tau : R) :
    List (Fin d × Bool) → R → (Fin J → R) → Nat → Fin J → R
  | _,_,initial,0 => initial
  | [],_,_,_+1 => fun _=>0
  | (axis,negative)::tail,code,initial,i+1 => commonScheduledAt indices k D p a C centre tau tail
      (advance (p+a*J) code)
      (boundedUpdate C (commonUpdate indices axis negative k D p a C centre tau)
        initial (decode (p+a*J) code)) i

/-- The parsed Hamming circuit and concrete Taylor matrices reproduce every
state of the scheduled transport/correction recurrence. -/
theorem common_scheduled_at_exact {d J : Nat} (indices : Fin J → Fin d → Nat)
    (k D p a : Nat) (hD:1≤D)
    (injective:∀ j l,indices j=indices l → j=l) (degree:∀ gamma j,indices gamma j≤k) (hwidth:D<2^p) (C centre tau : R) (hC:0≤C)
    (frames : List (Frame d J)) (valid:∀ f,f∈frames → validFrame D a f)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) (i : Nat) :
    commonScheduledAt indices k D p a C centre tau (schedule frames)
      (word (codePayload p a frames)) initial i = referenceAt indices C centre tau frames initial i := by
  induction frames generalizing initial i with
  | nil => cases i <;> rfl
  | cons f tail ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hf:=valid f (by simp)
      have ht:∀ g,g∈tail → validFrame D a g := fun g hg=>valid g (by simp [hg])
      have hlen:(payload p a f).length=p+a*J := frame_payload_length p a f.magnitude f.correction
      have hread:decode (p+a*J) (word (payload p a f++codePayload p a tail):R)=(payload p a f).map bit := by
        rw [← hlen]
        exact decode_prefix _ _
      have hnext:advance (p+a*J) (word (payload p a f++codePayload p a tail):R)=word (codePayload p a tail) := by
        rw [← hlen]
        exact advance_prefix _ _
      simp only [codePayload] at hread hnext
      simp only [schedule,List.map_cons,codePayload,List.flatten_cons,commonScheduledAt,referenceAt]
      rw [hread,hnext,bounded_common_update_frame indices k D p a hD injective degree hwidth C centre tau hC f hf initial hinit]
      exact ih ht _ (direct_update_range indices C centre tau hC f initial) i

theorem common_scheduled_at_robust {d J : Nat} (indices : Fin J → Fin d → Nat)
    (k D p a : Nat) (hD:1≤D)
    (injective:∀ j l,indices j=indices l → j=l) (degree:∀ gamma j,indices gamma j≤k) (hwidth:D<2^p) (C centre tau : R) (hC:0≤C)
    (frames : List (Frame d J)) (valid:∀ f,f∈frames → validFrame D a f)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) (i : Nat) (e : R)
    (he:-noiseBudget (R:=R) (codePayload p a frames).length≤e ∧
      e≤noiseBudget (R:=R) (codePayload p a frames).length) :
    commonScheduledAt indices k D p a C centre tau (schedule frames)
      (word (codePayload p a frames)+e) initial i = referenceAt indices C centre tau frames initial i := by
  induction frames generalizing initial i e with
  | nil => cases i <;> rfl
  | cons f tail ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hf:=valid f (by simp)
      have ht:∀ g,g∈tail → validFrame D a g := fun g hg=>valid g (by simp [hg])
      have hlen:(payload p a f).length=p+a*J := frame_payload_length p a f.magnitude f.correction
      have hread:decode (p+a*J) (word (payload p a f++codePayload p a tail)+e)=(payload p a f).map bit := by
        rw [← hlen]
        exact decode_prefix_robust _ _ e he
      have hnext:advance (p+a*J) (word (payload p a f++codePayload p a tail)+e)=
          word (codePayload p a tail)+noiseAdvance (p+a*J) e := by
        rw [← hlen]
        exact advance_prefix_robust _ _ e he
      simp only [codePayload] at hread hnext
      simp only [schedule,List.map_cons,codePayload,List.flatten_cons,commonScheduledAt,referenceAt]
      rw [hread,hnext,bounded_common_update_frame indices k D p a hD injective degree hwidth C centre tau hC f hf initial hinit]
      apply ih ht _ (direct_update_range indices C centre tau hC f initial) i (noiseAdvance (p+a*J) e)
      apply noise_budget_transport (p+a*J) (codePayload p a tail).length e
      simpa only [codePayload,List.map_cons,List.flatten_cons,List.length_append,hlen] using he

/-- The packed concrete Taylor recurrence supplies the spatially selected jet.
The matching dimension and frame count ensure the rank is an actual state. -/
theorem common_spatial_capture (n K d J : Nat) (hK:0<K) (delta : R) (hd:0<delta)
    (sites : List (Site R)) (dimension:sites.length=d) (safe:validSites n K delta sites)
    (indices : Fin J → Fin d → Nat) (k D p a : Nat) (hD:1≤D)
    (injective:∀ j l,indices j=indices l → j=l) (degree:∀ gamma j,indices gamma j≤k) (hwidth:D<2^p)
    (C centre tau : R) (hC:0≤C) (frames : List (Frame d J))
    (valid:∀ f,f∈frames → validFrame D a f) (alignment:frames.length+1=K^d)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) :
    snakeRank K (sites.map Site.fine)≤frames.length ∧
    (fun beta=>captureStream C
      (((K^d:Nat):R)*clippedCircuit K (decodedDigits n K delta sites))
      (fun j=>commonScheduledAt indices k D p a C centre tau (schedule frames)
        (word (codePayload p a frames)) initial j beta) (K^d)) =
      referenceAt indices C centre tau frames initial (snakeRank K (sites.map Site.fine)) := by
  have hB:K^sites.length=K^d := congrArg (fun x=>K^x) dimension
  have hv:∀ i,i∈sites.map Site.fine → i<K := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨s,hs,he⟩
    subst i
    exact (safe s hs).2.1
  have hr:=snake_rank_bound K hK (sites.map Site.fine) hv
  simp only [List.length_map] at hr
  refine ⟨by omega,?_⟩
  have heq:(fun j=>commonScheduledAt indices k D p a C centre tau (schedule frames)
      (word (codePayload p a frames)) initial j)=referenceAt indices C centre tau frames initial := by
    funext j
    exact common_scheduled_at_exact indices k D p a hD injective degree hwidth C centre tau hC frames valid initial hinit j
  simp only [heq]
  rw [← hB]
  exact safe_spatial_stream n K J hK delta hd sites safe C hC
    (referenceAt indices C centre tau frames initial)
    (fun j _=>reference_at_range indices C centre tau hC frames initial hinit j)

theorem robust_common_spatial_capture (n K d J : Nat) (hK:0<K) (delta : R) (hd:0<delta)
    (sites : List (Site R)) (dimension:sites.length=d) (safe:validSites n K delta sites)
    (indices : Fin J → Fin d → Nat) (k D p a : Nat) (hD:1≤D)
    (injective:∀ j l,indices j=indices l → j=l) (degree:∀ gamma j,indices gamma j≤k) (hwidth:D<2^p)
    (C centre tau : R) (hC:0≤C) (frames : List (Frame d J))
    (valid:∀ f,f∈frames → validFrame D a f) (alignment:frames.length+1=K^d)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) (e : R)
    (he:-noiseBudget (R:=R) (codePayload p a frames).length≤e ∧
      e≤noiseBudget (R:=R) (codePayload p a frames).length) :
    snakeRank K (sites.map Site.fine)≤frames.length ∧
    (fun beta=>captureStream C
      (((K^d:Nat):R)*clippedCircuit K (decodedDigits n K delta sites))
      (fun j=>commonScheduledAt indices k D p a C centre tau (schedule frames)
        (word (codePayload p a frames)+e) initial j beta) (K^d)) =
      referenceAt indices C centre tau frames initial (snakeRank K (sites.map Site.fine)) := by
  have h:=common_spatial_capture n K d J hK delta hd sites dimension safe indices k D p a hD injective degree hwidth
    C centre tau hC frames valid alignment initial hinit
  simp only [common_scheduled_at_exact indices k D p a hD injective degree hwidth C centre tau hC frames valid initial hinit] at h
  have heq:(fun j=>commonScheduledAt indices k D p a C centre tau (schedule frames)
      (word (codePayload p a frames)+e) initial j)=referenceAt indices C centre tau frames initial := by
    funext j
    exact common_scheduled_at_robust indices k D p a hD injective degree hwidth C centre tau hC frames valid initial hinit j e he
  simpa only [heq] using h

end MathCan.CommonGateCapture
