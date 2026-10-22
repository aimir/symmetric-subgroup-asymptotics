import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoRange
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoQuadratic

/-! Actual characteristic-two B/C elementary-group equivalence. The map
is hyperplane restriction, its image is proved from literal root formulas,
and its kernel is eliminated by the transpose quadratic form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoEquivalence
open CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBGenerationBlockRestriction
open CFSGOrthogonalBGenerationCharTwoRestriction
open CFSGOrthogonalBGenerationCharTwoRange
open CFSGOrthogonalBGenerationCharTwoQuadratic
open CFSGOrthogonalBGenerationQuadraticKernel
variable (K : Type) [Field K] [CharP K 2]

theorem naturalRestriction_injective (r : ℕ) :
    Function.Injective (naturalRestriction K r) := by
  intro g h he
  have hm : naturalRestriction K r (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hb : upperBlock K (Fin r ⊕ Fin r) ((g * h⁻¹).val : Mat K r) = 1 :=
    congrArg Units.val hm
  have hmat : ((g * h⁻¹).val : Mat K r) = 1 :=
    eq_one_of_upperBlock_eq_one K (Fin r) _
      (elementary_le_rowSubgroup K r (g * h⁻¹).property) hb
      (elementary_preserves_quadratic K r (g * h⁻¹))
  have hu : g * h⁻¹ = 1 := by
    apply Subtype.ext
    exact Units.ext hmat
  exact mul_inv_eq_one.mp hu

theorem restrictionIntoC_injective (r : ℕ) :
    Function.Injective (restrictionIntoC K r) := by
  intro g h he
  exact naturalRestriction_injective K r (congrArg Subtype.val he)

def elementaryEquiv [Finite K] (r : ℕ) :
    elementaryRootGroup K r ≃* CFSGSymplecticSerreMatrices.elementaryRootGroup K r :=
  MulEquiv.ofBijective (restrictionIntoC K r)
    ⟨restrictionIntoC_injective K r, restrictionIntoC_surjective K r⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoEquivalence
