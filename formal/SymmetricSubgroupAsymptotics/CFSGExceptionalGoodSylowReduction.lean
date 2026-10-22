import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckGoodSylow
import SymmetricSubgroupAsymptotics.CFSGClassicalGoodSylowReduction

/-! The original untwisted E6/E7/E8 families leave the exact good-Sylow
residual, in addition to A/B/C/D and Suzuki. Every other classifier tag
is retained literally. This is not a closure of the whole AG input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexWithoutClassicalSuzukiE : CFSG.Index→Prop
  | .E6 _ => False
  | .E7 _ => False
  | .E8 _ => False
  | i => RemainingGoodSylowIndexWithoutTypeASuzukiBCD i

theorem model_goodSylow_or_remaining_without_classical_suzuki_E (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    (∃p,GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutClassicalSuzukiE i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_typeA_suzuki_B_C_D _ hn
  case E6 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := hsimple
    exact Or.inl ⟨q.prime,CFSGExceptionalGeckGoodSylow.typeE6_goodSylowPrime q⟩
  case E7 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := hsimple
    exact Or.inl ⟨q.prime,CFSGExceptionalGeckGoodSylow.typeE7_goodSylowPrime q⟩
  case E8 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := hsimple
    exact Or.inl ⟨q.prime,CFSGExceptionalGeckGoodSylow.typeE8_goodSylowPrime q⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_classical_suzuki_E
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexWithoutClassicalSuzukiE i →
        ∃p,GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_classical_suzuki_E i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
