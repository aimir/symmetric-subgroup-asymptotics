import SymmetricSubgroupAsymptotics.CFSGAlternatingFiveGoodSylow
import SymmetricSubgroupAsymptotics.CFSGExceptionalGoodSylowReduction

/-! The original A5 classifier tag is removed from the actual good-Sylow
residual. All larger alternating models and every other previously open
model remain explicit. This does not assert the whole AG theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5 : CFSG.Index → Prop
  | .alternating n _ => n ≠ 5
  | i => RemainingGoodSylowIndexWithoutClassicalSuzukiE i

theorem model_goodSylow_or_remaining_without_classical_suzuki_E_A5
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬ IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨
      RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5 i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_classical_suzuki_E _ hn
  case alternating n hdegree hfinite hsimple =>
    by_cases h : n = 5
    · subst n
      exact Or.inl ⟨2, CFSGAlternatingFiveGoodSylow.goodSylowPrime⟩
    · exact Or.inr h

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_classical_suzuki_E_A5
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5 i →
        ∃ p, GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_classical_suzuki_E_A5 i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
