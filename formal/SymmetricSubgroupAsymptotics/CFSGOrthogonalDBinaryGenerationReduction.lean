import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryModelGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticGenerationReduction

/-! Exact residual refinement after the actual binary D generating
pair. Every nonbinary D tag and all other previous obligations remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

def RemainingGenerationIndexWithoutTypeASuzukiCBinaryD : CFSG.Index → Prop
  | .D _ q _ => q.order ≠ 2
  | i => RemainingGenerationIndexWithoutTypeASuzukiC i

theorem model_twoGenerated_or_remaining_without_typeA_suzuki_C_binaryD (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    TwoGenerated i.Model ∨ RemainingGenerationIndexWithoutTypeASuzukiCBinaryD i := by
  cases i <;> try exact model_twoGenerated_or_remaining_without_typeA_suzuki_C _ hn
  case D r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.D r q) := hsimple
    by_cases hq : q.order = 2
    · exact Or.inl (typeD_binary_twoGenerated_rank r q hr hq)
    · exact Or.inr hq

theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_binaryD_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model → RemainingGenerationIndexWithoutTypeASuzukiCBinaryD i →
        TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCenterless G → TwoGenerated G := by
  apply finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_models hCFSG
  intro i _ _ hc _
  rcases model_twoGenerated_or_remaining_without_typeA_suzuki_C_binaryD i
    (noncommutative_of_simple_centerless i.Model hc) with hgen | hremain
  · exact hgen
  · exact remaining i hc hremain

end SymmetricSubgroupAsymptotics.CFSGReduction
