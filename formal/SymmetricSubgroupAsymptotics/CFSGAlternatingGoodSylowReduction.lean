import SymmetricSubgroupAsymptotics.CFSGAlternatingGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedA2GoodSylowReduction

/-! Every original alternating tag leaves the exact good-Sylow residual.
The previously proved classical, Suzuki, exceptional E and twisted-A2
cases remain discharged; all other models remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingAndTwistedA2 : CFSG.Index → Prop
  | .alternating _ _ => False
  | i => RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5AndTwistedA2 i

theorem model_goodSylow_or_remaining_without_classical_suzuki_E_alternating_twistedA2
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨
      RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingAndTwistedA2 i := by
  cases i <;>
    try exact model_goodSylow_or_remaining_without_classical_suzuki_E_A5_twistedA2 _ hn
  case alternating n hdegree hfinite hsimple =>
    exact Or.inl ⟨2, CFSGAlternatingGoodSylow.goodSylowPrime n hdegree⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_classical_suzuki_E_alternating_twistedA2
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingAndTwistedA2 i →
          ∃ p, GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_classical_suzuki_E_alternating_twistedA2 i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
