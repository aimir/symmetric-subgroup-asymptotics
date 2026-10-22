import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryGoodSylowReduction
import SymmetricSubgroupAsymptotics.CFSGGTwoGoodSylowReduction

/-! Remove the complete twisted-A branch while preserving all previously
proved alternating, G2, exceptional-E, classical and Suzuki reductions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterUnitary : CFSG.Index → Prop
  | .twistedA _ _ _ _ => False
  | i => RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 i

theorem model_goodSylow_or_remaining_after_unitary (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexAfterUnitary i := by
  cases i <;>
    try exact model_goodSylow_or_remaining_without_classical_suzuki_E_alternating_twistedA2_G2 _ hn
  case twistedA r q hr hsmall hfinite hsimple =>
    exact Or.inl ⟨q.prime, twistedA_goodSylowPrime r hr q hsmall⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_after_unitary
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexAfterUnitary i →
        ∃ p, GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_after_unitary i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
