import Std

/-!
# Quantum diamond: exact Pauli support pullback

CNOT conjugation updates binary Pauli exponents by x_target ^= x_control and
z_control ^= z_target. Global Pauli phase is deliberately omitted here.
The four CNOTs are executed SA, SB, AT, BT. Pullback applies conjugations
in reverse execution order. This finite theorem certifies the support part
of the no-signalling argument, not the general density-matrix theorem.
-/
namespace MathCan.Pregeometry.QuantumDiamond

structure Support where
  xs : Bool
  xa : Bool
  xb : Bool
  xt : Bool
  zs : Bool
  za : Bool
  zb : Bool
  zt : Bool
  deriving DecidableEq

def cxSA (p : Support) : Support :=
  { p with xa := p.xa ^^ p.xs, zs := p.zs ^^ p.za }

def cxSB (p : Support) : Support :=
  { p with xb := p.xb ^^ p.xs, zs := p.zs ^^ p.zb }

def cxAT (p : Support) : Support :=
  { p with xt := p.xt ^^ p.xa, za := p.za ^^ p.zt }

def cxBT (p : Support) : Support :=
  { p with xt := p.xt ^^ p.xb, zb := p.zb ^^ p.zt }

def pullback (p : Support) : Support := cxSA (cxSB (cxAT (cxBT p)))

def target (x z : Bool) : Support :=
  ⟨false, false, false, x, false, false, false, z⟩

theorem target_pullback (x z : Bool) :
    pullback (target x z) = ⟨false, false, false, x, false, z, z, z⟩ := by
  cases x <;> cases z <;> decide +kernel

theorem target_pullback_source_identity (x z : Bool) :
    (pullback (target x z)).xs = false ∧
      (pullback (target x z)).zs = false := by
  rw [target_pullback]
  decide

#print axioms target_pullback
#print axioms target_pullback_source_identity

end MathCan.Pregeometry.QuantumDiamond
