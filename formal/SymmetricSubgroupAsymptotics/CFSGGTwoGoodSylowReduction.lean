import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGAlternatingGoodSylowReduction

/-! The actual original G2 family leaves the exact remaining good-Sylow
model cases. All undischargeable cases stay explicit in the residual. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 : CFSG.Index → Prop
  | .G2 _ _ => False
  | i => RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingAndTwistedA2 i

theorem model_goodSylow_or_remaining_without_classical_suzuki_E_alternating_twistedA2_G2
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨
      RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 i := by
  cases i <;>
    try exact model_goodSylow_or_remaining_without_classical_suzuki_E_alternating_twistedA2 _ hn
  case G2 q hguard hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := hsimple
    exact Or.inl ⟨q.prime, CFSGGTwoOriginalGoodSylow.typeGTwo_goodSylowPrime q⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_classical_suzuki_E_alternating_twistedA2_G2
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 i →
          ∃ p, GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_classical_suzuki_E_alternating_twistedA2_G2 i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
