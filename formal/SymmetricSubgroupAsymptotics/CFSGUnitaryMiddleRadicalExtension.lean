import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalMiddleAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveCover
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-! The actual middle special-unitary group acts on the actual
nonabelian radical. Literal block conjugation gives a semidirect hom
and its actual original-model projective projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGProjectiveLinearPointAction

private def radicalMiddleAut (q : CFSG.PrimePower) (s : ℕ) (a : naturalFixed s q) :
    MulAut (fixedRadical q s) where
  toFun := radicalMiddleConjugate q s a
  invFun := radicalMiddleConjugate q s a⁻¹
  left_inv g := by
    apply Subtype.ext
    change naturalFixedMiddleHom q s a⁻¹ *
      (naturalFixedMiddleHom q s a * g.val * (naturalFixedMiddleHom q s a)⁻¹) *
      (naturalFixedMiddleHom q s a⁻¹)⁻¹ = g.val
    rw [map_inv]
    group
  right_inv g := by
    apply Subtype.ext
    change naturalFixedMiddleHom q s a *
      (naturalFixedMiddleHom q s a⁻¹ * g.val * (naturalFixedMiddleHom q s a⁻¹)⁻¹) *
      (naturalFixedMiddleHom q s a)⁻¹ = g.val
    rw [map_inv]
    group
  map_mul' g h := by
    apply Subtype.ext
    change naturalFixedMiddleHom q s a * (g.val * h.val) * (naturalFixedMiddleHom q s a)⁻¹ =
      (naturalFixedMiddleHom q s a * g.val * (naturalFixedMiddleHom q s a)⁻¹) *
        (naturalFixedMiddleHom q s a * h.val * (naturalFixedMiddleHom q s a)⁻¹)
    group

def radicalMiddleAutHom (q : CFSG.PrimePower) (s : ℕ) :
    naturalFixed s q →* MulAut (fixedRadical q s) where
  toFun := radicalMiddleAut q s
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change naturalFixedMiddleHom q s 1 * g.val * (naturalFixedMiddleHom q s 1)⁻¹ = g.val
    rw [map_one]
    group
  map_mul' a b := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change naturalFixedMiddleHom q s (a * b) * g.val * (naturalFixedMiddleHom q s (a * b))⁻¹ =
      naturalFixedMiddleHom q s a *
        (naturalFixedMiddleHom q s b * g.val * (naturalFixedMiddleHom q s b)⁻¹) *
          (naturalFixedMiddleHom q s a)⁻¹
    rw [map_mul]
    group

def naturalVectorMulAutHom (q : CFSG.PrimePower) (s : ℕ) :
    naturalFixed s q →* MulAut (Multiplicative (Fin (s + 1) → q.Extension 2)) where
  toFun g := {
    toFun v := Multiplicative.ofAdd (linearEquiv g.val.val v.toAdd)
    invFun v := Multiplicative.ofAdd ((linearEquiv g.val.val).symm v.toAdd)
    left_inv v := (linearEquiv g.val.val).symm_apply_apply v.toAdd
    right_inv v := (linearEquiv g.val.val).apply_symm_apply v.toAdd
    map_mul' v w := (linearEquiv g.val.val).map_add v.toAdd w.toAdd }
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change linearEquiv (1 : (Mat (q.Extension 2) s)ˣ) v.toAdd = v.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change linearEquiv (g.val.val * h.val.val) v.toAdd =
      linearEquiv g.val.val (linearEquiv h.val.val v.toAdd)
    rw [map_mul]
    rfl

theorem naturalVectorMulAutHom_apply (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed s q) (v : Multiplicative (Fin (s + 1) → q.Extension 2)) :
    naturalVectorMulAutHom q s g v =
      Multiplicative.ofAdd ((g.val.val : Mat (q.Extension 2) s) *ᵥ v.toAdd) := rfl

theorem radicalMiddleAut_parameter (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (g : fixedRadical q s) :
    fixedRadicalParameterHom q s (radicalMiddleAutHom q s a g) =
      naturalVectorMulAutHom q s a (fixedRadicalParameterHom q s g) :=
  fixedRadicalParameter_middle_conjugate q s a g

def middleRadicalExtensionHom (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q s ⋊[radicalMiddleAutHom q s] naturalFixed s q →* naturalFixed (s + 2) q :=
  SemidirectProduct.lift (fixedRadical q s).subtype (naturalFixedMiddleHom q s)
    (fun _ => MonoidHom.ext (fun _ => rfl))

theorem middleRadicalExtensionHom_inl (q : CFSG.PrimePower) (s : ℕ)
    (g : fixedRadical q s) :
    middleRadicalExtensionHom q s (SemidirectProduct.inl g) = g.val := by
  simp only [middleRadicalExtensionHom, SemidirectProduct.lift_inl]
  rfl

def higherUnitaryProjectiveExtensionHom (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q (s + 2) ⋊[radicalMiddleAutHom q (s + 2)] naturalFixed (s + 2) q →*
      CFSG.Models.TwistedA (s + 4) q :=
  (unitaryProjectiveCover q (s + 1)).comp (middleRadicalExtensionHom q (s + 2))

theorem higherUnitaryProjectiveExtensionHom_inl (q : CFSG.PrimePower) (s : ℕ)
    (g : fixedRadical q (s + 2)) :
    higherUnitaryProjectiveExtensionHom q s (SemidirectProduct.inl g) =
      unitaryProjectiveCover q (s + 1) g.val := by
  change unitaryProjectiveCover q (s + 1)
    (middleRadicalExtensionHom q (s + 2) (SemidirectProduct.inl g)) = _
  rw [middleRadicalExtensionHom_inl]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
