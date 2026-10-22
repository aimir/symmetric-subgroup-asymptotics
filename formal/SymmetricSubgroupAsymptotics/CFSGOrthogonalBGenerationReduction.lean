import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationModels
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoReduction

/-! Exact residual refinement after generation of the entire original
B family, with precisely the original rank-three guard. Previously
retained non-B tags are unchanged, and no new generation premise is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

def RemainingGenerationIndexWithoutTypeASuzukiBCD : CFSG.Index → Prop
  | .B _ _ _ => False
  | i => RemainingGenerationIndexWithoutTypeASuzukiCDCharTwoB i

theorem model_twoGenerated_or_remaining_without_typeA_suzuki_B_C_D (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    TwoGenerated i.Model ∨ RemainingGenerationIndexWithoutTypeASuzukiBCD i := by
  cases i <;> try exact model_twoGenerated_or_remaining_without_typeA_suzuki_C_D_charTwoB _ hn
  case B r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    exact Or.inl (typeB_twoGenerated_of_index r q hr)

theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_B_C_D_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model → RemainingGenerationIndexWithoutTypeASuzukiBCD i →
        TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCenterless G → TwoGenerated G := by
  apply finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_D_charTwoB_models hCFSG
  intro i _ _ hc _
  rcases model_twoGenerated_or_remaining_without_typeA_suzuki_B_C_D i
    (noncommutative_of_simple_centerless i.Model hc) with hgen | hremain
  · exact hgen
  · exact remaining i hc hremain

end SymmetricSubgroupAsymptotics.CFSGReduction
