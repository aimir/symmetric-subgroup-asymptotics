import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedDGoodSylowModelReduction

/-! The complete ORIGINAL triality D4 branch leaves the good-Sylow
residual. All other previously discharged and remaining branches are
preserved literally. No simple-index or outer-order leaf is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterTriality : CFSG.Index → Prop
  | .trialityD4 _ => False
  | i => RemainingGoodSylowIndexAfterTwistedD i

theorem model_goodSylow_or_remaining_after_triality (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexAfterTriality i := by
  cases i <;> try exact model_goodSylow_or_remaining_after_twistedD _ hn
  case trialityD4 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := hsimple
    exact Or.inl ⟨q.prime,CFSGTrialityGeckGoodSylow.original_goodSylowPrime q⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_after_triality
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexAfterTriality i →
        ∃ p, GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_and_remaining_after_twistedD hCFSG
  intro i _ _ hn _
  rcases model_goodSylow_or_remaining_after_triality i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
