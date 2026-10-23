import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSevenProjection
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleStringAction

/-! One selected actual original action after the seven-coordinate
projection. Its two intermediate string terms vanish, leaving the
literal cubed endpoint parameter. This proves one root/vector family;
it does not assume or assert stability under every signed root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSevenCubicPilot
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices
open CFSGGTwoOriginalFieldBasis CFSGGTwoOriginalSevenProjection
open CFSGGTwoOriginalCharacteristicThreeString CFSGGTwoOriginalSimpleStringAction
local notation "A" => CartanMatrix.G₂
variable (K : Type) [Field K]

private theorem first_string_projection_zero :
    sevenProjection K (stringElement K false 1)=0 := by
  change sevenProjection K (fieldVectors K (Sum.inl (false,2)))=0
  rw [sevenProjection,LinearMap.comp_apply,fieldCoordinates_vectors]
  apply Subtype.ext
  funext i
  rcases i with j|j <;> fin_cases j
  all_goals first | rfl | exact neg_zero

private theorem second_string_projection_zero :
    sevenProjection K (stringElement K false 2)=0 := by
  change sevenProjection K (fieldVectors K (Sum.inl (false,3)))=0
  rw [sevenProjection,LinearMap.comp_apply,fieldCoordinates_vectors]
  apply Subtype.ext
  funext i
  rcases i with j|j <;> fin_cases j
  all_goals first | rfl | exact neg_zero

theorem short_long_cubed_endpoint (t : K) :
    sevenProjection K (rootOperator A K false 0 t (stringElement K false 0))=
      sevenProjection K (stringElement K false 0)+
        t^3 • sevenProjection K (stringElement K false 3) := by
  rw [rootOperator_long_string,map_add,map_add,map_add,map_smul,map_smul,map_smul,
    first_string_projection_zero,second_string_projection_zero]
  simp only [smul_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSevenCubicPilot
