import SymmetricSubgroupAsymptotics.CFSGTypeAGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelReduction

/-! Exact classifier/Suzuki dispatch after the whole literal type-A
family is proved. All other actual finite simple model obligations stay
explicit; this file does not assert that those remaining cases are closed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem typeA_goodSylowPrime (r : ℕ) (q : CFSG.PrimePower) (hr : 1 ≤ r) :
    GoodSylowPrime (CFSG.Models.A r q) q.prime := by
  exact CFSGTypeAGoodSylow.psl_goodSylowPrime q.Field q.prime (r+1) (by omega)

def RemainingGoodSylowIndexWithoutTypeA : CFSG.Index → Prop
  | .A _ _ _ _ => False
  | _ => True

theorem model_goodSylow_or_remaining_without_typeA
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (_hn : ¬ IsMulCommutative i.Model) :
    (∃ p,GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutTypeA i := by
  cases i <;> try exact Or.inr trivial
  case A r q hr hs hfinite hsimple =>
    exact Or.inl ⟨q.prime,typeA_goodSylowPrime r q hr⟩

theorem simple_goodSylow_of_cfsg_and_remaining_without_typeA
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexWithoutTypeA i →
        ∃ p,GoodSylowPrime i.Model p)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ¬ IsMulCommutative T) : ∃ p,GoodSylowPrime T p := by
  apply simple_goodSylow_of_cfsg_models hCFSG ?_ T hT
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_typeA i hn with h | h
  · exact h
  · exact remaining i hn h

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_typeA
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexWithoutTypeA i →
        ∃ p,GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_typeA i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
