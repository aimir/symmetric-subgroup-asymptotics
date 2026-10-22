import SymmetricSubgroupAsymptotics.CFSGFFourLongRootFourthCoefficient
import SymmetricSubgroupAsymptotics.CFSGFFourLongRootMatrices
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSelectedRootAction

/-! The selected long-root word acts by its literal E6 Weyl matrix on the
SAME original F4 integral image. The remaining source generators are
retained with their original divided-power action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGSerreModelRootGeneration
local instance fFourImageWeylActionDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K]

abbrev imageGroup := (imageRepresentation realizationData K).range

def sourceWeyl : Model CartanMatrix.F₄ K :=
  modelRoot CartanMatrix.F₄ K false 2 1*modelRoot CartanMatrix.F₄ K true 2 (-1)*
    modelRoot CartanMatrix.F₄ K false 2 1

def imageWeyl : imageGroup K :=
  (imageRepresentation realizationData K).rangeRestrict (sourceWeyl K)

theorem long_root_image_action (neg : Bool) (t : K) (y : (baseChange realizationData K).range) :
    (imageRepresentation realizationData K (modelRoot CartanMatrix.F₄ K neg 2 t) y).val=
      (canonicalRoot realizationData K neg 2 t : Matrix Index Index K)*y.val*
        (↑((canonicalRoot realizationData K neg 2 t)⁻¹):Matrix Index Index K) :=
  imageRepresentation_root_selected realizationData K neg 2 (baseChange_long_fourth K neg) t y

theorem weyl_image_action (y : (baseChange realizationData K).range) :
    (imageRepresentation realizationData K (sourceWeyl K) y).val=
      (canonicalWeyl realizationData K 2 : Matrix Index Index K)*y.val*
        (↑((canonicalWeyl realizationData K 2)⁻¹):Matrix Index Index K) := by
  simp only [sourceWeyl,map_mul,LinearEquiv.mul_apply]
  rw [long_root_image_action,long_root_image_action,long_root_image_action]
  simp only [canonicalWeyl,Units.val_mul,_root_.mul_inv_rev,mul_assoc]

private theorem weyl_image_power (k : ℕ) (y : (baseChange realizationData K).range) :
    (((imageRepresentation realizationData K (sourceWeyl K))^k) y).val=
      CFSGAlgebraConjugationAction.action K (Matrix Index Index K)
        ((canonicalWeyl realizationData K 2)^k) y.val := by
  induction k with
  | zero=>simp only [pow_zero,map_one];rfl
  | succ k ih=>
    rw [pow_succ',LinearEquiv.mul_apply,weyl_image_action,ih]
    rw [pow_succ',map_mul,LinearEquiv.mul_apply]
    rfl

theorem imageWeyl_four : (imageWeyl K)^4=1 := by
  apply Subtype.ext
  change (imageRepresentation realizationData K (sourceWeyl K))^4=1
  apply LinearEquiv.ext
  intro y
  apply Subtype.ext
  have hh := weyl_image_power K 4 y
  simpa only [long_weyl_four,map_one] using hh

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
