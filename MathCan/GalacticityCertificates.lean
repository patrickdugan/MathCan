import Lean

namespace GalacticityCertificates

/-- With a fixed certificate, acceptance cannot distinguish observationally
    identical worlds. Certificate-specific access must be accounted for. -/
theorem certificate_alias {W C O : Type}
    (obs : C → W → O) (verify : C → O → Bool)
    (z : C) (good bad : W) (same : obs z good = obs z bad)
    (accepted : verify z (obs z good) = true) :
    verify z (obs z bad) = true := by
  rw [← same]
  exact accepted

def bxor (a b : Bool) : Bool := if a then !b else b
def band (a b : Bool) : Bool := if a then b else false

theorem affine_xor_pointwise (a b c d : Bool) :
    bxor (bxor a b) (bxor c d) = bxor (bxor a c) (bxor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem affine_and_constant_left (a b c : Bool) :
    band a (bxor b c) = (if a then bxor b c else false) := by
  rfl

theorem affine_and_constant_right (a b c : Bool) :
    band (bxor a b) c = (if c then bxor a b else false) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Equal linear parts and equal biases give an idempotent product.
    Equal linear parts and opposite biases give zero. -/
theorem affine_and_same_part (x b d : Bool) :
    band (bxor x b) (bxor x d) =
      (if b = d then bxor x b else false) := by
  cases x <;> cases b <;> cases d <;> rfl

/-- Mixed second difference of a product on an independent two-bit
    coordinate square is one. A full rank-to-square lemma is separate. -/
theorem product_mixed_difference (b d : Bool) :
    bxor (bxor (band (bxor false b) (bxor false d))
                (band (bxor true b) (bxor false d)))
         (bxor (band (bxor false b) (bxor true d))
                (band (bxor true b) (bxor true d))) = true := by
  cases b <;> cases d <;> rfl

/-- A finite Boolean expression with explicitly supplied syntax. -/
inductive Expr where
  | atom : Nat → Expr
  | lit : Bool → Expr
  | xor : Expr → Expr → Expr
  | and : Expr → Expr → Expr

def Expr.eval (env : Nat → Bool) : Expr → Bool
  | .atom i => env i
  | .lit b => b
  | .xor a b => bxor (a.eval env) (b.eval env)
  | .and a b => band (a.eval env) (b.eval env)

/-- Small proof calculus that can avoid expansion of nonlinear subterms.
    It is sound but no completeness or proof-size guarantee is asserted. -/
inductive Rewrite : Expr → Expr → Prop where
  | refl (a : Expr) : Rewrite a a
  | symm {a b : Expr} : Rewrite a b → Rewrite b a
  | trans {a b c : Expr} : Rewrite a b → Rewrite b c → Rewrite a c
  | xorCongr {a b c d : Expr} :
      Rewrite a b → Rewrite c d → Rewrite (.xor a c) (.xor b d)
  | andCongr {a b c d : Expr} :
      Rewrite a b → Rewrite c d → Rewrite (.and a c) (.and b d)
  | xorSelf (a : Expr) : Rewrite (.xor a a) (.lit false)
  | xorZero (a : Expr) : Rewrite (.xor a (.lit false)) a
  | andZero (a : Expr) : Rewrite (.and a (.lit false)) (.lit false)
  | andOne (a : Expr) : Rewrite (.and a (.lit true)) a

theorem rewrite_sound {a b : Expr} (p : Rewrite a b)
    (env : Nat → Bool) : a.eval env = b.eval env := by
  induction p with
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | xorCongr _ _ ih₁ ih₂ =>
      simp only [Expr.eval]
      rw [ih₁, ih₂]
  | andCongr _ _ ih₁ ih₂ =>
      simp only [Expr.eval]
      rw [ih₁, ih₂]
  | xorSelf a =>
      simp only [Expr.eval]
      cases a.eval env <;> rfl
  | xorZero a =>
      simp only [Expr.eval]
      cases a.eval env <;> rfl
  | andZero a =>
      simp only [Expr.eval]
      cases a.eval env <;> rfl
  | andOne a =>
      simp only [Expr.eval]
      cases a.eval env <;> rfl

/-- A local cancellation certificate has no need to evaluate the subtree. -/
theorem cancellation_sound (a : Expr) (env : Nat → Bool) :
    (Expr.xor a a).eval env = false :=
  rewrite_sound (Rewrite.xorSelf a) env

/-- Cost of acquiring a verified representation must be funded upfront. -/
theorem certificate_funding (capital discovery verification build : Nat) :
    (discovery ≤ capital ∧ verification ≤ capital - discovery ∧
      build ≤ capital - discovery - verification) ↔
    discovery + verification + build ≤ capital := by omega

end GalacticityCertificates
