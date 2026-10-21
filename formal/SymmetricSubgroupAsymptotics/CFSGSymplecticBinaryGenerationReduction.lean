import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankDispatch
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelGeneration

/-! Exact refinement of the concrete simple-generation residual after
proving the original binary C family. All nonbinary C tags and all other
previously open tags remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

def RemainingGenerationIndexWithoutTypeASuzukiBinaryC : CFSG.Index→Prop
  | .C _ q _ _ => q.order≠2
  | i => RemainingGenerationIndexWithoutTypeAAndSuzuki i

theorem model_twoGenerated_or_remaining_without_typeA_suzuki_binaryC (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    TwoGenerated i.Model∨RemainingGenerationIndexWithoutTypeASuzukiBinaryC i := by
  cases i <;> try exact model_twoGenerated_or_remaining_without_typeA_suzuki _ hn
  case C r q hr hs hsimple =>
    letI : IsSimpleGroup (CFSG.Models.C r q) := hsimple
    by_cases hq : q.order=2
    · exact Or.inl (typeC_binary_twoGenerated_of_index r q hr hs hq)
    · exact Or.inr hq

theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_binaryC_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model→RemainingGenerationIndexWithoutTypeASuzukiBinaryC i→TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G],IsSimpleGroup G→IsCenterless G→TwoGenerated G := by
  apply finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_models hCFSG
  intro i _ _ hc _
  rcases model_twoGenerated_or_remaining_without_typeA_suzuki_binaryC i
    (noncommutative_of_simple_centerless i.Model hc) with hgen|hremain
  · exact hgen
  · exact remaining i hc hremain

end SymmetricSubgroupAsymptotics.CFSGReduction
