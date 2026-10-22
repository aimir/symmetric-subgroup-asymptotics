import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexGoodSylow
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoGoodSylowReduction

/-! Exact residual refinement removing the entire original type-D
family from the good-Sylow task. Other still-open tags are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoBD : CFSG.Index → Prop
  | .D _ _ _ => False
  | i => RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoB i

theorem model_goodSylow_or_remaining_without_typeA_suzuki_C_charTwoB_D (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoBD i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_typeA_suzuki_C_charTwoB _ hn
  case D r q hr hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.D r q) := hsimple
    exact Or.inl ⟨q.prime, typeD_goodSylowPrime r q hr⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_typeA_suzuki_C_charTwoB_D
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoBD i →
        ∃ p, GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_typeA_suzuki_C_charTwoB_D i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
