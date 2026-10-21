import SymmetricSubgroupAsymptotics.CFSGSuzukiTwoGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeAModelGeneration

/-! Exact concrete-model dispatch after proving the full original Suzuki
family. The remaining callback explicitly omits only the already-proved
branches; this file does not assert that the other Lie models are solved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

def RemainingGenerationIndexWithoutTypeAAndSuzuki : CFSG.Index→Prop
  | .suzuki _ _ => False
  | i => RemainingGenerationIndexWithoutTypeA i

theorem model_twoGenerated_or_remaining_without_typeA_suzuki (i : CFSG.Index)
    (hn : ¬IsMulCommutative i.Model) :
    TwoGenerated i.Model∨RemainingGenerationIndexWithoutTypeAAndSuzuki i := by
  cases i <;> try exact model_twoGenerated_or_remaining_without_typeA _ hn
  case suzuki m hm => exact Or.inl (CFSGSuzukiGeneration.suzuki_twoGenerated m hm)

theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model→RemainingGenerationIndexWithoutTypeAAndSuzuki i→TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G],IsSimpleGroup G→IsCenterless G→TwoGenerated G := by
  apply finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_models hCFSG
  intro i _ _ hc hi
  cases i <;> try exact remaining _ hc hi
  case suzuki => exact CFSGSuzukiGeneration.suzuki_twoGenerated _ (by assumption)

end SymmetricSubgroupAsymptotics.CFSGReduction
