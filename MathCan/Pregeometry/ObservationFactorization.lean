import Std

/-!
# Exact decoding on reachable observation classes

The quotient construction uses worlds modulo equality of their accessible
records. It embeds into the record type with image exactly the reachable
records. A fiber-constant property descends uniquely to this quotient, with
no classical choice. Extending to every record uses an explicit default;
the implementation of that extension uses classical choice and decidability.

The final example has an empty world type, an inhabited record type and an
empty property type. Fiber constancy then holds while a total decoder cannot
exist. Every result concerns abstract functions over arbitrary types.
-/

namespace MathCan.Pregeometry

universe u v w

variable {World : Type u} {Record : Type v} {Property : Type w}

/-- The property agrees whenever the accessible records agree. -/
def FiberConstant (observe : World → Record) (property : World → Property) : Prop :=
  ∀ a b, observe a = observe b → property a = property b

/-- Equality of accessible records is an equivalence relation on worlds. -/
def observationSetoid (observe : World → Record) : Setoid World where
  r a b := observe a = observe b
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Reachable records represented by their classes of producing worlds. -/
abbrev ObservedClasses (observe : World → Record) := Quotient (observationSetoid observe)

/-- Send a world to its class of indistinguishable worlds. -/
def observeClass (observe : World → Record) (world : World) : ObservedClasses observe :=
  Quotient.mk (observationSetoid observe) world

/-- Each observation class has a well-defined record. -/
def classRecord (observe : World → Record) : ObservedClasses observe → Record :=
  Quotient.lift observe (fun _ _ h => h)

/-- The class representation retains the complete accessible record. -/
theorem classRecord_observeClass (observe : World → Record) (world : World) :
    classRecord observe (observeClass observe world) = observe world := rfl

/-- Equal records and equal observation classes express the same relation. -/
theorem observeClass_eq_iff (observe : World → Record) (a b : World) :
    observeClass observe a = observeClass observe b ↔ observe a = observe b := by
  constructor
  · intro h
    exact congrArg (classRecord observe) h
  · intro h
    exact Quotient.sound h

/-- Embedding observation classes into the ambient record type is injective. -/
theorem classRecord_injective (observe : World → Record)
    (a b : ObservedClasses observe)
    (h : classRecord observe a = classRecord observe b) : a = b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => exact Quotient.sound h

/-- Every observation class comes from a world; this is an existence statement
in Prop and selects no representative as data. -/
theorem observedClass_representative (observe : World → Record)
    (recordClass : ObservedClasses observe) :
    ∃ world, observeClass observe world = recordClass := by
  induction recordClass using Quotient.inductionOn with
  | h world => exact ⟨world, rfl⟩

/-- The embedded classes are exactly the records produced by some world. -/
theorem classRecord_image_iff (observe : World → Record) (record : Record) :
    (∃ cls, classRecord observe cls = record) ↔ ∃ world, observe world = record := by
  constructor
  · intro ⟨cls, hcls⟩
    obtain ⟨world, hworld⟩ := observedClass_representative observe cls
    exact ⟨world, by rw [← hworld] at hcls; exact hcls⟩
  · intro ⟨world, hworld⟩
    exact ⟨observeClass observe world, hworld⟩

/-- Fiber constancy permits a constructive quotient lift. -/
def classDecoder (observe : World → Record) (property : World → Property)
    (hconstant : FiberConstant observe property) : ObservedClasses observe → Property :=
  Quotient.lift property hconstant

/-- The descended decoder recovers the property of every world. -/
theorem classDecoder_correct (observe : World → Record) (property : World → Property)
    (hconstant : FiberConstant observe property) (world : World) :
    classDecoder observe property hconstant (observeClass observe world) = property world := rfl

/-- A decoder on reachable classes is fixed by its values on worlds. -/
theorem classDecoder_unique (observe : World → Record) (property : World → Property)
    (hconstant : FiberConstant observe property)
    (decode : ObservedClasses observe → Property)
    (hcorrect : ∀ world, decode (observeClass observe world) = property world) :
    decode = classDecoder observe property hconstant := by
  funext cls
  induction cls using Quotient.inductionOn with
  | h world => exact hcorrect world

/-- Exact decoding on reachable classes is equivalent to fiber constancy.
The decoder is unique, including when the class type is empty. -/
theorem fiberConstant_iff_unique_classDecoder
    (observe : World → Record) (property : World → Property) :
    FiberConstant observe property ↔
      ∃ decode : ObservedClasses observe → Property,
        (∀ world, decode (observeClass observe world) = property world) ∧
        ∀ other : ObservedClasses observe → Property,
          (∀ world, other (observeClass observe world) = property world) → other = decode := by
  constructor
  · intro hconstant
    exact ⟨classDecoder observe property hconstant,
      classDecoder_correct observe property hconstant,
      fun other hother => classDecoder_unique observe property hconstant other hother⟩
  · intro ⟨decode, hcorrect, _⟩ a b hab
    calc
      property a = decode (observeClass observe a) := (hcorrect a).symm
      _ = decode (observeClass observe b) :=
        congrArg decode ((observeClass_eq_iff observe a b).mpr hab)
      _ = property b := hcorrect b

/-- Extend decoding to every ambient record. The default supplies values
outside the reachable image. This definition uses classical witness choice. -/
noncomputable def decoderWithDefault (observe : World → Record)
    (property : World → Property) (default : Property) : Record → Property := by
  classical
  exact fun record => if h : ∃ world, observe world = record
    then property (Classical.choose h)
    else default

/-- Fiber constancy makes representative choice harmless on reachable records. -/
theorem decoderWithDefault_correct (observe : World → Record)
    (property : World → Property) (default : Property)
    (hconstant : FiberConstant observe property) (world : World) :
    decoderWithDefault observe property default (observe world) = property world := by
  classical
  unfold decoderWithDefault
  split
  · next h => exact hconstant _ world (Classical.choose_spec h)
  · next h => exact False.elim (h ⟨world, rfl⟩)

/-- With an explicit output default, fiber constancy characterizes the
existence of an exact total decoder over the ambient record type. -/
theorem totalDecoder_exists_iff_fiberConstant (observe : World → Record)
    (property : World → Property) (default : Property) :
    (∃ decode : Record → Property, ∀ world, decode (observe world) = property world) ↔
      FiberConstant observe property := by
  constructor
  · intro ⟨decode, hcorrect⟩ a b hab
    calc
      property a = decode (observe a) := (hcorrect a).symm
      _ = decode (observe b) := congrArg decode hab
      _ = property b := hcorrect b
  · intro hconstant
    exact ⟨decoderWithDefault observe property default,
      decoderWithDefault_correct observe property default hconstant⟩

/-- Fiber constancy is vacuous for the indicated empty world type. -/
theorem empty_world_fiberConstant :
    FiberConstant (fun world : Empty => (nomatch world : Unit))
      (fun world : Empty => world) := by
  intro world
  cases world

/-- An inhabited ambient record type cannot decode into the empty output type.
This exhibits the missing condition in an unrestricted total-extension claim. -/
theorem empty_world_no_totalDecoder :
    ¬ ∃ decode : Unit → Empty,
      ∀ world : Empty, decode (nomatch world : Unit) = world := by
  intro ⟨decode, _⟩
  exact Empty.elim (decode ())

#print axioms classRecord_observeClass
#print axioms observeClass_eq_iff
#print axioms classRecord_injective
#print axioms observedClass_representative
#print axioms classRecord_image_iff
#print axioms classDecoder_correct
#print axioms classDecoder_unique
#print axioms fiberConstant_iff_unique_classDecoder
#print axioms decoderWithDefault_correct
#print axioms totalDecoder_exists_iff_fiberConstant
#print axioms empty_world_fiberConstant
#print axioms empty_world_no_totalDecoder

end MathCan.Pregeometry
