import SymmetricSubgroupAsymptotics.CFSGFFourAllRootImageConstraint
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots

/-! Every original F4 root operator intertwines with its literal folded
matrix root unit on the SAME base-changed integral image. All simple
roots, both signs and all parameters are retained. The equality of the
two action ranges does not assert faithfulness of the ambient module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGSerreModelRootGeneration
local instance fullRootActionDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

theorem full_baseChange_rootOperator (K : Type) [Field K] (neg : Bool) (i : Fin 4)
    (t : K) (x : Space CartanMatrix.F₄ K) :
    baseChange realizationData K (rootOperator CartanMatrix.F₄ K neg i t x)=
      (canonicalRoot realizationData K neg i t : Matrix Index Index K)*
        baseChange realizationData K x*
        (↑((canonicalRoot realizationData K neg i t)⁻¹) : Matrix Index Index K) := by
  rw [canonicalRoot_val,canonicalRoot_inv_val]
  exact baseChange_rootOperator realizationData K (baseChange_all_fourth K) neg i t x

theorem full_root_image_action (K : Type) [Field K] (neg : Bool) (i : Fin 4)
    (t : K) (y : (baseChange realizationData K).range) :
    (imageRepresentation realizationData K (modelRoot CartanMatrix.F₄ K neg i t) y).val=
      (canonicalRoot realizationData K neg i t : Matrix Index Index K)*y.val*
        (↑((canonicalRoot realizationData K neg i t)⁻¹) : Matrix Index Index K) := by
  rw [canonicalRoot_val,canonicalRoot_inv_val]
  exact imageRepresentation_root realizationData K (baseChange_all_fourth K) neg i t y

def fullNaturalImageAction (K : Type) [Field K] :
    canonicalElementaryGroup realizationData K→*
      ((baseChange realizationData K).range≃ₗ[K](baseChange realizationData K).range) :=
  canonicalImageAction realizationData K (baseChange_all_fourth K)

theorem full_action_ranges_eq (K : Type) [Field K] :
    (imageRepresentation realizationData K).range=(fullNaturalImageAction K).range :=
  canonical_action_ranges_eq realizationData K (baseChange_all_fourth K)

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
