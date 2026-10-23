import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GoodSylowReduction

/-! The actual original ReeG2 branch leaves the good-Sylow residual.
Its independent simple-index/outer-order obligations are not removed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterReeGTwo : CFSG.Index → Prop
  | .reeG2 _ _ => False
  | i => RemainingGoodSylowIndexAfterTwistedE6 i

theorem model_goodSylow_or_remaining_after_ReeGTwo (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexAfterReeGTwo i := by
  cases i <;> try exact model_goodSylow_or_remaining_after_twistedE6 _ hn
  case reeG2 m hm hfinite hsimple =>
    letI : Finite (CFSG.Models.ReeG2 m) := hfinite
    letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := hsimple
    exact Or.inl ⟨3,CFSGReeGTwoOriginalGoodSylow.reeGTwo_goodSylowPrime m hm⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_after_ReeGTwo
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexAfterReeGTwo i →
        ∃ p, GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_and_remaining_after_twistedE6 hCFSG
  intro i _ _ hn _
  rcases model_goodSylow_or_remaining_after_ReeGTwo i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
