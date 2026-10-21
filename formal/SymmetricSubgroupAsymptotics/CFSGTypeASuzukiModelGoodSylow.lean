import SymmetricSubgroupAsymptotics.CFSGTypeAModelGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelGoodSylow

/-! The actual type-A and Suzuki simple-model leaves are discharged.
The other pinned families remain explicit in the soluble-generation
reduction, rather than being hidden behind a classification alias. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexWithoutTypeASuzuki : CFSG.Index → Prop
  | .A _ _ _ _ => False
  | .suzuki _ _ => False
  | _ => True

theorem model_goodSylow_or_remaining_without_typeA_suzuki
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (_hn : ¬ IsMulCommutative i.Model) :
    (∃ p,GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutTypeASuzuki i := by
  cases i <;> try exact Or.inr trivial
  case A r q hr hs hfinite hsimple =>
    exact Or.inl ⟨q.prime,typeA_goodSylowPrime r q hr⟩
  case suzuki m hm hfinite hsimple =>
    exact Or.inl ⟨2,CFSGSuzukiModelGoodSylow.goodSylowPrime m⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_typeA_suzuki
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexWithoutTypeASuzuki i →
        ∃ p,GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_typeA_suzuki i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
