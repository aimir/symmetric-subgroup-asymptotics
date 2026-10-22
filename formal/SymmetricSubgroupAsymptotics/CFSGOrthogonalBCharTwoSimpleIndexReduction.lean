import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoSimpleIndex

/-! Only actual characteristic-two B tags are removed from the current
simple-index residual. Odd B and all other remaining tags are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def RemainingSimpleIndexModelWithoutTypeASuzukiCCharTwoB : CFSG.Index → Prop
  | .B _ q _ => q.prime ≠ 2
  | i => RemainingSimpleIndexModelWithoutTypeASuzukiC i

theorem simpleIndex_model_or_remaining_without_typeA_suzuki_C_charTwoB (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    ModelSimpleIndexBounds i ∨ RemainingSimpleIndexModelWithoutTypeASuzukiCCharTwoB i := by
  cases i <;> try exact simpleIndex_model_or_remaining_without_typeA_suzuki_C _ hn
  case B r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    by_cases hq : q.prime = 2
    · exact Or.inl (typeB_charTwo_simpleIndexBounds r hr q hq)
    · exact Or.inr hq

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_C_charTwoB_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSimpleIndexModelWithoutTypeASuzukiCCharTwoB i →
        ModelSimpleIndexBounds i) : PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_C_models hCFSG
  intro i _ _ hn _
  rcases simpleIndex_model_or_remaining_without_typeA_suzuki_C_charTwoB i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
