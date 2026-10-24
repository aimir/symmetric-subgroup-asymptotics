import SymmetricSubgroupAsymptotics.FiniteBilinearIsometryOrderBound
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The literal matrix-unit action is faithful. A subgroup preserving a
nondegenerate bilinear form, and its actual central quotient, inherit
the basis-stabilizer order bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.MatrixUnitBilinearIsometryOrderBound
variable (F I : Type*) [Field F] [Fintype I] [DecidableEq I]

def naturalLinearHom (H : Subgroup (Matrix I I F)ˣ) : H →* ((I → F) ≃ₗ[F] (I → F)) :=
  ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (I → F))).toMonoidHom).comp H.subtype

theorem naturalLinearHom_apply (H : Subgroup (Matrix I I F)ˣ)
    (g : H) (v : I → F) : naturalLinearHom F I H g v = (g.val : Matrix I I F) *ᵥ v := rfl

theorem naturalLinearHom_injective (H : Subgroup (Matrix I I F)ˣ) :
    Function.Injective (naturalLinearHom F I H) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (I → F))).injective.comp
      Subtype.val_injective

theorem subgroup_card_le [Finite F] (H : Subgroup (Matrix I I F)ˣ)
    (B : LinearMap.BilinForm F (I → F)) (hB : B.Nondegenerate)
    (hpres : ∀ g : H, ∀ x y : I → F,
      B ((g.val : Matrix I I F) *ᵥ x) ((g.val : Matrix I I F) *ᵥ y) = B x y) :
    Nat.card H ≤ Nat.card F ^ (Nat.card I * (Nat.card I + 1) / 2) := by
  have hb := FiniteBilinearIsometryOrderBound.card_le_pow_finrank
    (naturalLinearHom F I H) (naturalLinearHom_injective F I H) B hB hpres
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using hb

theorem central_quotient_card_le [Finite F] (H : Subgroup (Matrix I I F)ˣ)
    (B : LinearMap.BilinForm F (I → F)) (hB : B.Nondegenerate)
    (hpres : ∀ g : H, ∀ x y : I → F,
      B ((g.val : Matrix I I F) *ᵥ x) ((g.val : Matrix I I F) *ᵥ y) = B x y) :
    Nat.card (H ⧸ Subgroup.center H) ≤
      Nat.card F ^ (Nat.card I * (Nat.card I + 1) / 2) :=
  (Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center H))
    (QuotientGroup.mk'_surjective _)).trans (subgroup_card_le F I H B hB hpres)

end SymmetricSubgroupAsymptotics.MatrixUnitBilinearIsometryOrderBound
