import Std

/-!
# Operational identifiability through an observation map

The types `World`, `Record`, and `Property` are arbitrary. These theorems concern
equality of accessible records and the possibility of deterministic decoding.
They contain no assumptions or conclusions about spacetime, Lorentzian metrics,
dimension, gravitational dynamics, or quantum channels.

An observation-preserving update preserves the record selected by `observe`.
This condition is distinct from trace preservation of a quantum operation.
-/

namespace OperationalIdentifiability

universe u v w z

variable {World : Type u} {Record : Type v} {Property : Type w}

/-- A decoder assigns equal outputs to worlds with equal accessible records. -/
theorem decoder_constant_on_observation_fibers
    (observe : World → Record) (decode : Record → Property)
    {w₀ w₁ : World} (hobs : observe w₀ = observe w₁) :
    decode (observe w₀) = decode (observe w₁) :=
  congrArg decode hobs

/-- A property that differs within an observation fiber admits no uniformly
correct deterministic decoder from those records. -/
theorem no_uniform_decoder_of_indistinguishable_worlds
    (observe : World → Record) (property : World → Property)
    (w₀ w₁ : World) (hobs : observe w₀ = observe w₁)
    (hdiff : property w₀ ≠ property w₁) :
    ¬ ∃ decode : Record → Property,
      ∀ world : World, decode (observe world) = property world := by
  intro hex
  obtain ⟨decode, hcorrect⟩ := hex
  apply hdiff
  calc
    property w₀ = decode (observe w₀) := (hcorrect w₀).symm
    _ = decode (observe w₁) := congrArg decode hobs
    _ = property w₁ := hcorrect w₁

/-- Processing a record before decoding preserves the same obstruction. -/
theorem postprocessing_cannot_remove_decoder_obstruction
    {Processed : Type z}
    (observe : World → Record) (process : Record → Processed)
    (property : World → Property)
    (w₀ w₁ : World) (hobs : observe w₀ = observe w₁)
    (hdiff : property w₀ ≠ property w₁) :
    ¬ ∃ decode : Processed → Property,
      ∀ world : World, decode (process (observe world)) = property world :=
  no_uniform_decoder_of_indistinguishable_worlds
    (fun world => process (observe world)) property w₀ w₁
    (congrArg process hobs) hdiff

/-- If an update preserves every accessible record, it also preserves equality
of records between any two worlds. -/
theorem observation_preserving_update_cannot_separate
    (observe : World → Record) (update : World → World)
    (hpreserve : ∀ world : World, observe (update world) = observe world)
    {w₀ w₁ : World} (hobs : observe w₀ = observe w₁) :
    observe (update w₀) = observe (update w₁) := by
  calc
    observe (update w₀) = observe w₀ := hpreserve w₀
    _ = observe w₁ := hobs
    _ = observe (update w₁) := (hpreserve w₁).symm

#print axioms decoder_constant_on_observation_fibers
#print axioms no_uniform_decoder_of_indistinguishable_worlds
#print axioms postprocessing_cannot_remove_decoder_obstruction
#print axioms observation_preserving_update_cannot_separate

end OperationalIdentifiability
