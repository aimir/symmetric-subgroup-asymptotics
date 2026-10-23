import SymmetricSubgroupAsymptotics.CFSGFFourOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGoodSylowReduction

/-! The complete ORIGINAL F4 branch leaves the good-Sylow residual.
Only that branch is removed; the separate model-budget residual stays
unchanged. No simple-index or outer-order assertion is added here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterFFour : CFSG.Index → Prop
  | .F4 _ => False
  | i => RemainingGoodSylowIndexAfterTriality i

theorem model_goodSylow_or_remaining_after_fFour (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexAfterFFour i := by
  cases i <;> try exact model_goodSylow_or_remaining_after_triality _ hn
  case F4 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := hsimple
    exact Or.inl ⟨q.prime,CFSGFFourOriginalGoodSylow.typeFFour_goodSylowPrime q⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_after_fFour
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexAfterFFour i →
        ∃ p, GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_and_remaining_after_triality hCFSG
  intro i _ _ hn _
  rcases model_goodSylow_or_remaining_after_fFour i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
