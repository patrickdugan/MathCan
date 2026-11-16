import MathCan.SentinelDecoder

/-!
The base-4 reader feeds finite payload frames to a clipped jet update and
then the previously proved spatial capture circuit. The update is an explicit
function on decoded scalar bits. No decoder-correctness premise is used.
The generic update includes finite matrix transport and signed corrections;
analytic Taylor transport bounds and the amplitude selector remain separate.
-/
namespace MathCan.DecodedJetCapture
open Std Lean.Grind MathCan.SpatialScalar MathCan.SpatialRouting
open MathCan.SpatialNormalized MathCan.SpatialClipped MathCan.SentinelDecoder
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def unsignedLE : List R → R
  | [] => 0
  | b::tail => b+2*unsignedLE tail

def unsignedNat : List Bool → Nat
  | [] => 0
  | b::tail => (if b then 1 else 0)+2*unsignedNat tail

theorem unsigned_bits_exact (bits : List Bool) :
    unsignedLE (bits.map (bit (R := R))) = (unsignedNat bits:R) := by
  induction bits with
  | nil => simp only [List.map_nil,unsignedLE,unsignedNat,Semiring.natCast_zero]
  | cons b tail ih =>
    cases b <;> simp [List.map_cons,unsignedLE,unsignedNat,bit,ih,
      Semiring.natCast_add,Semiring.natCast_mul,Semiring.natCast_zero,Semiring.natCast_one,
      Semiring.natCast_eq_ofNat (α := R) 2] <;> grind

theorem decoded_unsigned_exact (bits : List Bool) :
    unsignedLE (decode bits.length (word (R := R) bits)) = (unsignedNat bits:R) := by
  rw [decode_word,unsigned_bits_exact]

theorem decoded_signed_exact (C : R) (bits : List Bool) :
    unsignedLE (decode bits.length (word (R := R) bits))-C = (unsignedNat bits:R)-C := by
  rw [decoded_unsigned_exact]

/-- Explicit finite matrix multiplication with a decoded correction vector. -/
def matrixCorrection {J : Nat} (tau : R)
    (matrix : List R → Fin J → Fin J → R) (correction : List R → Fin J → R)
    (v : Fin J → R) (payload : List R) : Fin J → R := fun beta =>
  sum J (fun j => if h : j < J then matrix payload beta ⟨j,h⟩ * v ⟨j,h⟩ else 0) +
    tau*correction payload beta

def boundedUpdate {J : Nat} (C : R)
    (update : (Fin J → R) → List R → Fin J → R)
    (v : Fin J → R) (payload : List R) : Fin J → R :=
  fun beta => symmetricClip C (update v payload beta)

theorem bounded_update_range {J : Nat} (C : R) (hC : 0 ≤ C)
    (update : (Fin J → R) → List R → Fin J → R) (v : Fin J → R) (payload : List R) :
    ∀ beta, -C ≤ boundedUpdate C update v payload beta ∧ boundedUpdate C update v payload beta ≤ C := by
  intro beta
  exact symmetric_clip_range C _ hC

/-- Correct physical states are unaffected by the decoder's state clipping. -/
theorem bounded_update_identity {J : Nat} (C : R)
    (update : (Fin J → R) → List R → Fin J → R) (v : Fin J → R) (payload : List R)
    (bounds : ∀ beta, -C ≤ update v payload beta ∧ update v payload beta ≤ C) :
    boundedUpdate C update v payload = update v payload := by
  funext beta
  exact symmetric_clip_identity C _ (bounds beta)

def referenceJetAt {J : Nat} (C : R)
    (update : (Fin J → R) → List R → Fin J → R) :
    List (List Bool) → (Fin J → R) → Nat → Fin J → R
  | _,initial,0 => initial
  | [],_,_+1 => fun _ => 0
  | frame::tail,initial,i+1 =>
    referenceJetAt C update tail (boundedUpdate C update initial (frame.map bit)) i

def decodedJetAt {J : Nat} (C : R)
    (update : (Fin J → R) → List R → Fin J → R) :
    List Nat → R → (Fin J → R) → Nat → Fin J → R
  | _,_,initial,0 => initial
  | [],_,_,_+1 => fun _ => 0
  | width::tail,code,initial,i+1 =>
    decodedJetAt C update tail (advance width code)
      (boundedUpdate C update initial (decode width code)) i

/-- Concatenated payloads feed every frame to exactly the same state update. -/
theorem decoded_jet_at_exact {J : Nat} (C : R)
    (update : (Fin J → R) → List R → Fin J → R) (frames : List (List Bool))
    (initial : Fin J → R) (i : Nat) :
    decodedJetAt C update (frames.map List.length) (word frames.flatten) initial i =
      referenceJetAt C update frames initial i := by
  induction frames generalizing initial i with
  | nil => cases i <;> rfl
  | cons frame tail ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.map_cons,List.flatten_cons,decodedJetAt,referenceJetAt]
      rw [advance_prefix,decode_prefix]
      exact ih _ i

theorem reference_jet_range {J : Nat} (C : R) (hC : 0 ≤ C)
    (update : (Fin J → R) → List R → Fin J → R) (frames : List (List Bool))
    (initial : Fin J → R) (hinit : ∀ beta, -C ≤ initial beta ∧ initial beta ≤ C) (i : Nat) :
    ∀ beta, -C ≤ referenceJetAt C update frames initial i beta ∧
      referenceJetAt C update frames initial i beta ≤ C := by
  induction frames generalizing initial i with
  | nil =>
    cases i with
    | zero => exact hinit
    | succ i => intro beta; simp only [referenceJetAt]; constructor <;> grind
  | cons frame tail ih =>
    cases i with
    | zero => exact hinit
    | succ i => exact ih _ (bounded_update_range C hC update initial _) i

theorem decoded_jet_range {J : Nat} (C : R) (hC : 0 ≤ C)
    (update : (Fin J → R) → List R → Fin J → R) (frames : List (List Bool))
    (initial : Fin J → R) (hinit : ∀ beta, -C ≤ initial beta ∧ initial beta ≤ C) (i : Nat) :
    ∀ beta, -C ≤ decodedJetAt C update (frames.map List.length) (word frames.flatten) initial i beta ∧
      decodedJetAt C update (frames.map List.length) (word frames.flatten) initial i beta ≤ C := by
  rw [decoded_jet_at_exact]
  exact reference_jet_range C hC update frames initial hinit i

/-- A packed sentinel word supplies all jets captured at the spatial rank. -/
theorem decoded_spatial_capture (n K J : Nat) (hK : 0 < K) (delta : R) (hd : 0 < delta)
    (sites : List (Site R)) (valid : validSites n K delta sites) (C : R) (hC : 0 ≤ C)
    (update : (Fin J → R) → List R → Fin J → R) (frames : List (List Bool))
    (alignment : frames.length+1 = K^sites.length) (initial : Fin J → R)
    (hinit : ∀ beta, -C ≤ initial beta ∧ initial beta ≤ C) :
    snakeRank K (sites.map Site.fine) ≤ frames.length ∧
    (fun beta => captureStream C
      (((K^sites.length:Nat):R) * clippedCircuit K (decodedDigits n K delta sites))
      (fun j => decodedJetAt C update (frames.map List.length) (word frames.flatten) initial j beta)
      (K^sites.length)) =
      referenceJetAt C update frames initial (snakeRank K (sites.map Site.fine)) := by
  have hvalid : ∀ i, i ∈ sites.map Site.fine → i < K := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨s,hs,he⟩
    subst i
    exact (valid s hs).2.1
  have hr := snake_rank_bound K hK (sites.map Site.fine) hvalid
  simp only [List.length_map] at hr
  refine ⟨by omega, ?_⟩
  have heq : (fun j => decodedJetAt C update (frames.map List.length) (word frames.flatten) initial j) =
      referenceJetAt C update frames initial := by
    funext j
    exact decoded_jet_at_exact C update frames initial j
  simp only [heq]
  exact safe_spatial_stream n K J hK delta hd sites valid C hC
    (referenceJetAt C update frames initial)
    (fun j _ => reference_jet_range C hC update frames initial hinit j)

theorem decoded_jet_at_robust {J : Nat} (C : R)
    (update : (Fin J → R) → List R → Fin J → R) (frames : List (List Bool))
    (initial : Fin J → R) (i : Nat) (e : R)
    (he : -noiseBudget (R := R) frames.flatten.length ≤ e ∧
      e ≤ noiseBudget (R := R) frames.flatten.length) :
    decodedJetAt C update (frames.map List.length) (word frames.flatten+e) initial i =
      referenceJetAt C update frames initial i := by
  induction frames generalizing initial i e with
  | nil => cases i <;> rfl
  | cons frame tail ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.map_cons,List.flatten_cons,decodedJetAt,referenceJetAt]
      rw [advance_prefix_robust frame tail.flatten e he,decode_prefix_robust frame tail.flatten e he]
      apply ih _ i (noiseAdvance frame.length e)
      apply noise_budget_transport frame.length tail.flatten.length e
      simpa only [List.flatten_cons,List.length_append] using he

/-- The spatially captured jet is unchanged by a sufficiently small code error. -/
theorem robust_decoded_spatial_capture (n K J : Nat) (hK : 0 < K) (delta : R) (hd : 0 < delta)
    (sites : List (Site R)) (valid : validSites n K delta sites) (C : R) (hC : 0 ≤ C)
    (update : (Fin J → R) → List R → Fin J → R) (frames : List (List Bool))
    (alignment : frames.length+1 = K^sites.length) (initial : Fin J → R)
    (hinit : ∀ beta, -C ≤ initial beta ∧ initial beta ≤ C) (e : R)
    (he : -noiseBudget (R := R) frames.flatten.length ≤ e ∧
      e ≤ noiseBudget (R := R) frames.flatten.length) :
    snakeRank K (sites.map Site.fine) ≤ frames.length ∧
    (fun beta => captureStream C
      (((K^sites.length:Nat):R) * clippedCircuit K (decodedDigits n K delta sites))
      (fun j => decodedJetAt C update (frames.map List.length) (word frames.flatten+e) initial j beta)
      (K^sites.length)) =
      referenceJetAt C update frames initial (snakeRank K (sites.map Site.fine)) := by
  have h := decoded_spatial_capture n K J hK delta hd sites valid C hC update frames alignment initial hinit
  simp only [decoded_jet_at_exact] at h
  have heq : (fun j => decodedJetAt C update (frames.map List.length) (word frames.flatten+e) initial j) =
      referenceJetAt C update frames initial := by
    funext j
    exact decoded_jet_at_robust C update frames initial j e he
  simpa only [heq] using h

end MathCan.DecodedJetCapture
