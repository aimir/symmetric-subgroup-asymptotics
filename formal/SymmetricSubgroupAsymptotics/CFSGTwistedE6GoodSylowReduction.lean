import SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGFFourGoodSylowReduction

/-! The complete ORIGINAL twisted E6 branch leaves the good-Sylow
residual. The independent simple-index/outer-order residual is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterTwistedE6 : CFSG.Index → Prop
  | .twistedE6 _ => False
  | i => RemainingGoodSylowIndexAfterFFour i

theorem model_goodSylow_or_remaining_after_twistedE6 (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexAfterTwistedE6 i := by
  cases i <;> try exact model_goodSylow_or_remaining_after_fFour _ hn
  case twistedE6 q hfinite hsimple =>
    letI : Finite (CFSG.Models.TwistedE6 q) := hfinite
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := hsimple
    exact Or.inl ⟨q.prime,CFSGTwistedE6OriginalGoodSylow.typeTwistedE6_goodSylowPrime q⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_after_twistedE6
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexAfterTwistedE6 i →
        ∃ p, GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_and_remaining_after_fFour hCFSG
  intro i _ _ hn _
  rcases model_goodSylow_or_remaining_after_twistedE6 i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
