import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeGoodSylow
import SymmetricSubgroupAsymptotics.CFSGUnitaryGoodSylowReductionCurrent

/-! The complete original twisted-D branch leaves the good-Sylow
residual, preserving every previously closed family. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterTwistedD : CFSG.Index → Prop
  | .twistedD _ _ _ => False
  | i => RemainingGoodSylowIndexAfterUnitary i

theorem model_goodSylow_or_remaining_after_twistedD (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexAfterTwistedD i := by
  cases i <;> try exact model_goodSylow_or_remaining_after_unitary _ hn
  case twistedD r q hr hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := hsimple
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
    exact Or.inl ⟨q.prime, CFSGTwistedDRelativeGoodSylow.original_goodSylowPrime s q⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_after_twistedD
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexAfterTwistedD i →
        ∃ p, GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_and_remaining_after_unitary hCFSG
  intro i _ _ hn _
  rcases model_goodSylow_or_remaining_after_twistedD i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
