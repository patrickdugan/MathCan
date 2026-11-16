import MathCan.TaylorFrame

/-! Scheduled, concrete Hamming/Taylor decoding and spatial capture. Axis and
orientation are fixed layer metadata; amplitudes and signed corrections are
read from the single sentinel word. No abstract matrix/update oracle occurs in
the reference recurrence. Analytic jet remainder estimates remain separate. -/
namespace MathCan.ConcreteJetCapture
open Std Lean.Grind MathCan.SpatialScalar MathCan.SpatialRouting
open MathCan.SpatialNormalized MathCan.SpatialClipped MathCan.SentinelDecoder
open MathCan.DecodedJetCapture MathCan.TaylorTransport MathCan.TaylorFrame
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def referenceAt {d J : Nat} (indices : Fin J → Fin d → Nat) (C centre tau : R) :
    List (Frame d J) → (Fin J → R) → Nat → Fin J → R
  | _,initial,0 => initial
  | [],_,_+1 => fun _=>0
  | f::tail,initial,i+1 => referenceAt indices C centre tau tail
      (directUpdate indices C centre tau f initial) i

def scheduledAt {d J : Nat} (indices : Fin J → Fin d → Nat) (D p a : Nat) (C centre tau : R) :
    List (Fin d × Bool) → R → (Fin J → R) → Nat → Fin J → R
  | _,_,initial,0 => initial
  | [],_,_,_+1 => fun _=>0
  | (axis,negative)::tail,code,initial,i+1 => scheduledAt indices D p a C centre tau tail
      (advance (p+a*J) code)
      (boundedUpdate C (selectedUpdate indices axis negative D p a C centre tau)
        initial (decode (p+a*J) code)) i

def schedule {d J : Nat} (frames : List (Frame d J)) : List (Fin d × Bool) :=
  frames.map (fun f=>(f.axis,f.negative))

def codePayload {d J : Nat} (p a : Nat) (frames : List (Frame d J)) : List Bool :=
  (frames.map (payload p a)).flatten

theorem reference_at_range {d J : Nat} (indices : Fin J → Fin d → Nat) (C centre tau : R)
    (hC:0≤C) (frames : List (Frame d J)) (initial : Fin J → R)
    (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) (i : Nat) :
    ∀ beta,-C≤referenceAt indices C centre tau frames initial i beta ∧
      referenceAt indices C centre tau frames initial i beta≤C := by
  induction frames generalizing initial i with
  | nil =>
    cases i with
    | zero => exact hinit
    | succ i => intro beta; simp only [referenceAt]; constructor <;> grind
  | cons f frames ih =>
    cases i with
    | zero => exact hinit
    | succ i => exact ih _ (direct_update_range indices C centre tau hC f initial) i

/-- The parsed Hamming circuit and concrete Taylor matrices reproduce every
state of the scheduled transport/correction recurrence. -/
theorem scheduled_at_exact {d J : Nat} (indices : Fin J → Fin d → Nat)
    (D p a : Nat) (hwidth:D<2^p) (C centre tau : R) (hC:0≤C)
    (frames : List (Frame d J)) (valid:∀ f,f∈frames → validFrame D a f)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) (i : Nat) :
    scheduledAt indices D p a C centre tau (schedule frames)
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
      simp only [schedule,List.map_cons,codePayload,List.flatten_cons,scheduledAt,referenceAt]
      rw [hread,hnext,bounded_selected_update_frame indices D p a hwidth C centre tau hC f hf initial hinit]
      exact ih ht _ (direct_update_range indices C centre tau hC f initial) i

theorem scheduled_at_robust {d J : Nat} (indices : Fin J → Fin d → Nat)
    (D p a : Nat) (hwidth:D<2^p) (C centre tau : R) (hC:0≤C)
    (frames : List (Frame d J)) (valid:∀ f,f∈frames → validFrame D a f)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) (i : Nat) (e : R)
    (he:-noiseBudget (R:=R) (codePayload p a frames).length≤e ∧
      e≤noiseBudget (R:=R) (codePayload p a frames).length) :
    scheduledAt indices D p a C centre tau (schedule frames)
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
      simp only [schedule,List.map_cons,codePayload,List.flatten_cons,scheduledAt,referenceAt]
      rw [hread,hnext,bounded_selected_update_frame indices D p a hwidth C centre tau hC f hf initial hinit]
      apply ih ht _ (direct_update_range indices C centre tau hC f initial) i (noiseAdvance (p+a*J) e)
      apply noise_budget_transport (p+a*J) (codePayload p a tail).length e
      simpa only [codePayload,List.map_cons,List.flatten_cons,List.length_append,hlen] using he

/-- The packed concrete Taylor recurrence supplies the spatially selected jet.
The matching dimension and frame count ensure the rank is an actual state. -/
theorem concrete_spatial_capture (n K d J : Nat) (hK:0<K) (delta : R) (hd:0<delta)
    (sites : List (Site R)) (dimension:sites.length=d) (safe:validSites n K delta sites)
    (indices : Fin J → Fin d → Nat) (D p a : Nat) (hwidth:D<2^p)
    (C centre tau : R) (hC:0≤C) (frames : List (Frame d J))
    (valid:∀ f,f∈frames → validFrame D a f) (alignment:frames.length+1=K^d)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) :
    snakeRank K (sites.map Site.fine)≤frames.length ∧
    (fun beta=>captureStream C
      (((K^d:Nat):R)*clippedCircuit K (decodedDigits n K delta sites))
      (fun j=>scheduledAt indices D p a C centre tau (schedule frames)
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
  have heq:(fun j=>scheduledAt indices D p a C centre tau (schedule frames)
      (word (codePayload p a frames)) initial j)=referenceAt indices C centre tau frames initial := by
    funext j
    exact scheduled_at_exact indices D p a hwidth C centre tau hC frames valid initial hinit j
  simp only [heq]
  rw [← hB]
  exact safe_spatial_stream n K J hK delta hd sites safe C hC
    (referenceAt indices C centre tau frames initial)
    (fun j _=>reference_at_range indices C centre tau hC frames initial hinit j)

theorem robust_concrete_spatial_capture (n K d J : Nat) (hK:0<K) (delta : R) (hd:0<delta)
    (sites : List (Site R)) (dimension:sites.length=d) (safe:validSites n K delta sites)
    (indices : Fin J → Fin d → Nat) (D p a : Nat) (hwidth:D<2^p)
    (C centre tau : R) (hC:0≤C) (frames : List (Frame d J))
    (valid:∀ f,f∈frames → validFrame D a f) (alignment:frames.length+1=K^d)
    (initial : Fin J → R) (hinit:∀ beta,-C≤initial beta ∧ initial beta≤C) (e : R)
    (he:-noiseBudget (R:=R) (codePayload p a frames).length≤e ∧
      e≤noiseBudget (R:=R) (codePayload p a frames).length) :
    snakeRank K (sites.map Site.fine)≤frames.length ∧
    (fun beta=>captureStream C
      (((K^d:Nat):R)*clippedCircuit K (decodedDigits n K delta sites))
      (fun j=>scheduledAt indices D p a C centre tau (schedule frames)
        (word (codePayload p a frames)+e) initial j beta) (K^d)) =
      referenceAt indices C centre tau frames initial (snakeRank K (sites.map Site.fine)) := by
  have h:=concrete_spatial_capture n K d J hK delta hd sites dimension safe indices D p a hwidth
    C centre tau hC frames valid alignment initial hinit
  simp only [scheduled_at_exact indices D p a hwidth C centre tau hC frames valid initial hinit] at h
  have heq:(fun j=>scheduledAt indices D p a C centre tau (schedule frames)
      (word (codePayload p a frames)+e) initial j)=referenceAt indices C centre tau frames initial := by
    funext j
    exact scheduled_at_robust indices D p a hwidth C centre tau hC frames valid initial hinit j e he
  simpa only [heq] using h

end MathCan.ConcreteJetCapture
