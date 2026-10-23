import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalCenter
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParabolicFactorization

/-! Literal radical and central embeddings into the SAME actual upper
group. The middle group fixes the central root pointwise, all q. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays

def radicalUpperHom (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q s →* naturalUnipotent (s + 2) q where
  toFun g := ⟨g.val.val, fixedRadical_mem_upper q s g⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem upperFixedHom_injective (q : CFSG.PrimePower) (r : ℕ) :
    Function.Injective (upperFixedHom q r) := by
  intro x y he
  have hraw : x.val = y.val :=
    congrArg (fun u : naturalFixed r q => u.val) he
  apply Subtype.ext
  exact hraw

theorem radicalUpperHom_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (radicalUpperHom q s) := by
  intro x y he
  have hraw : x.val.val = y.val.val :=
    congrArg (fun u : naturalUnipotent (s + 2) q => u.val) he
  apply Subtype.ext
  apply Subtype.ext
  exact hraw

def upperCentralHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (centralParameters q s) →* naturalUnipotent (s + 2) q :=
  (radicalUpperHom q s).comp (centralRadicalHom q s)

theorem upperCentralHom_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (upperCentralHom q s) :=
  (radicalUpperHom_injective q s).comp (centralRadicalHom_injective q s)

theorem radicalMiddleConjugate_central (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (c : Multiplicative (centralParameters q s)) :
    radicalMiddleConjugate q s a (centralRadicalHom q s c) = centralRadicalHom q s c := by
  apply Subtype.ext
  apply blockFixedMatrixHom_injective q s
  change blockFixedMatrixHom q s
    (naturalFixedMiddleHom q s a * (centralRadicalElement q s c.toAdd).val *
      (naturalFixedMiddleHom q s a)⁻¹) =
    blockFixedMatrixHom q s (centralRadicalElement q s c.toAdd).val
  rw [map_mul, map_mul, map_inv, blockFixedMatrixHom_middle,
    centralRadicalElement_block, middleUnit_conjugate_upper]
  simp only [Matrix.zero_vecMul, Matrix.mulVec_zero]

theorem middle_centralRadical_commute (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (c : Multiplicative (centralParameters q s)) :
    naturalFixedMiddleHom q s a * (centralRadicalHom q s c).val =
      (centralRadicalHom q s c).val * naturalFixedMiddleHom q s a := by
  have he := congrArg (fun g : fixedRadical q s => g.val)
    (radicalMiddleConjugate_central q s a c)
  change naturalFixedMiddleHom q s a * (centralRadicalHom q s c).val *
    (naturalFixedMiddleHom q s a)⁻¹ = (centralRadicalHom q s c).val at he
  have hh := congrArg (fun g : naturalFixed (s + 2) q => g * naturalFixedMiddleHom q s a) he
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
