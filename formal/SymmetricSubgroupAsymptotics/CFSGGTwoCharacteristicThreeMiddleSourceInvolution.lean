import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSource
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylSquares
import Mathlib.Tactic.Group

/-! The actual square of the short Weyl word is the source involution.
Its opposite signs on the central plane and scalar line are literal
original torus actions, not assumptions about a Levi representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSourceInvolution
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoOriginalWeylSquares
open CFSGGTwoOriginalPositiveTorusAction CFSGGTwoNaturalPositiveTorusAction
open CFSGGTwoCharacteristicThreeMiddleSource CFSGGTwoCharacteristicThreeMiddleCentralWords
variable (K : Type) [Field K] [CharP K 3] [Finite K]

private theorem node_one (i : Fin 2) : torusNode K i 1 = 1 := by
  have h : weylParameter K i (-1) = (weylParameter K i 1)⁻¹ := by
    simp [weylParameter,mul_inv_rev,modelRoot_inv,mul_assoc]
  simp only [torusNode,h,mul_inv_cancel]

theorem torusPair_eq_short_square : torusPair K (-1,1) = shortWord K*shortWord K := by
  rw [torusPair,node_one,mul_one]
  exact (shortWord_square K).symm

def involution : source K := ⟨torusPair K (-1,1),by
  rw [torusPair_eq_short_square]
  exact (source K).mul_mem (shortWeyl_mem_source K) (shortWeyl_mem_source K)⟩

theorem involution_val : (involution K).val = torusPair K (-1,1) := rfl

theorem involution_square : (involution K)^2 = 1 := by
  apply Subtype.ext
  change (torusPair K (-1,1))^2 = 1
  have hp : ((-1,1) : Kˣ × Kˣ)^2 = 1 := by ext <;> simp
  have h := congrArg (torusHom K) hp
  rw [map_pow,map_one,torusHom_apply] at h
  exact h

theorem involution_positive_commute (a : K) :
    (involution K).val*positiveModel K 0 a = positiveModel K 0 a*(involution K).val := by
  have h := torusPair_positiveModel K (-1,1) 0 a
  have hs : rootScale K (-1,1) 0 = 1 := by simp [rootScale]
  rw [hs] at h
  simp only [Units.val_one,mul_one] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem involution_weyl_commute :
    (involution K).val*shortWord K = shortWord K*(involution K).val := by
  rw [involution_val,torusPair_eq_short_square]
  group

theorem involution_central_flip (v : Fin 3 → K) :
    (involution K).val*centralWord K v*(involution K).val⁻¹ =
      centralWord K ![-v 0,-v 1,v 2] := torus_flip_centralWord K v

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSourceInvolution
