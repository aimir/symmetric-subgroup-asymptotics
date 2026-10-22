import SymmetricSubgroupAsymptotics.CFSGOrthogonalDHigherRankSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleIndexReduction

/-! All original type-D ranks at least five leave the exact simple-index
residual. The D4 triality case remains literally present, as do all other
previously open models. No conditional automorphism-recognition input is
substituted for a removed family. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def RemainingSimpleIndexModelWithoutTypeASuzukiCBDHigh : CFSG.Index→Prop
  | .D r _ _ => r=4
  | i => RemainingSimpleIndexModelWithoutTypeASuzukiCB i

theorem simpleIndex_model_or_remaining_without_typeA_suzuki_C_B_DHigh (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    ModelSimpleIndexBounds i ∨ RemainingSimpleIndexModelWithoutTypeASuzukiCBDHigh i := by
  cases i <;> try exact simpleIndex_model_or_remaining_without_typeA_suzuki_C_B _ hn
  case D r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.D r q) := hsimple
    by_cases hhigh : 5≤r
    · exact Or.inl (typeD_high_simpleIndexBounds r hhigh q)
    · right
      change r=4
      omega

theorem publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_C_B_DHigh_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSimpleIndexModelWithoutTypeASuzukiCBDHigh i →
        ModelSimpleIndexBounds i) : PublishedSimpleIndexBounds := by
  apply publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_C_B_models hCFSG
  intro i _ _ hn _
  rcases simpleIndex_model_or_remaining_without_typeA_suzuki_C_B_DHigh i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
