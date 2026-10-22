import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleIndexBounds

/-! The WHOLE original B family is removed from the exact remaining
simple-index model predicate. Every other original model obligation is
retained literally; no higher-level recognition input is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def RemainingSimpleIndexModelWithoutTypeASuzukiCB : CFSG.Index → Prop
  | .B _ _ _ => False
  | i => RemainingSimpleIndexModelWithoutTypeASuzukiC i

theorem simpleIndex_model_or_remaining_without_typeA_suzuki_C_B (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    ModelSimpleIndexBounds i ∨ RemainingSimpleIndexModelWithoutTypeASuzukiCB i := by
  cases i <;> try exact simpleIndex_model_or_remaining_without_typeA_suzuki_C _ hn
  case B r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    exact Or.inl (typeB_simpleIndexBounds r hr q)

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_C_B_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSimpleIndexModelWithoutTypeASuzukiCB i →
        ModelSimpleIndexBounds i) : PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_C_models hCFSG
  intro i _ _ hn _
  rcases simpleIndex_model_or_remaining_without_typeA_suzuki_C_B i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
