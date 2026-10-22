import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoModels
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationReduction

/-! Exact residual refinement after characteristic-two type-B generation.
Only B tags with field prime two are discharged. Every previous non-B
obligation and every odd-characteristic B tag remains unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

def RemainingGenerationIndexWithoutTypeASuzukiCDCharTwoB : CFSG.Index → Prop
  | .B _ q _ => q.prime ≠ 2
  | i => RemainingGenerationIndexWithoutTypeASuzukiCD i

theorem model_twoGenerated_or_remaining_without_typeA_suzuki_C_D_charTwoB (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    TwoGenerated i.Model ∨ RemainingGenerationIndexWithoutTypeASuzukiCDCharTwoB i := by
  cases i <;> try exact model_twoGenerated_or_remaining_without_typeA_suzuki_C_D _ hn
  case B r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    by_cases hq : q.prime = 2
    · exact Or.inl (typeB_charTwo_twoGenerated r hr q hq)
    · exact Or.inr hq

theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_D_charTwoB_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model → RemainingGenerationIndexWithoutTypeASuzukiCDCharTwoB i →
        TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCenterless G → TwoGenerated G := by
  apply finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_D_models hCFSG
  intro i _ _ hc _
  rcases model_twoGenerated_or_remaining_without_typeA_suzuki_C_D_charTwoB i
    (noncommutative_of_simple_centerless i.Model hc) with hgen | hremain
  · exact hgen
  · exact remaining i hc hremain

end SymmetricSubgroupAsymptotics.CFSGReduction
