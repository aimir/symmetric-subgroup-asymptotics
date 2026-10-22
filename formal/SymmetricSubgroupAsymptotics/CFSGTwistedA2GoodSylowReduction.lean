import SymmetricSubgroupAsymptotics.CFSGTwistedA2ModelGoodSylow
import SymmetricSubgroupAsymptotics.CFSGAlternatingFiveGoodSylowReduction

/-! Only the literal rank-two twisted-A tags leave the exact good-Sylow
residual. Higher twisted-A ranks and every other prior remaining tag are
retained; no closure of the whole AG input is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5AndTwistedA2 : CFSG.Index → Prop
  | i@(.twistedA r _ _ _) => RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5 i ∧ r ≠ 2
  | i => RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5 i

theorem model_goodSylow_or_remaining_without_classical_suzuki_E_A5_twistedA2 (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨
      RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5AndTwistedA2 i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_classical_suzuki_E_A5 _ hn
  case twistedA r q hr hsmall hfinite hsimple =>
    by_cases htwo : r = 2
    · subst r
      exact Or.inl ⟨q.prime, twistedA2_goodSylowPrime q (hsmall rfl)⟩
    · rcases model_goodSylow_or_remaining_without_classical_suzuki_E_A5
        (.twistedA r q hr hsmall) hn with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, htwo⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_classical_suzuki_E_A5_twistedA2
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5AndTwistedA2 i →
          ∃ p, GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_classical_suzuki_E_A5_twistedA2 i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
