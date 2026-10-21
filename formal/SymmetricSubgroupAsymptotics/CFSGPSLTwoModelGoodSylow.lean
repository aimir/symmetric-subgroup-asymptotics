import SymmetricSubgroupAsymptotics.CFSGPSLTwoGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelReduction

/-! Exact classifier dispatch for the proved literal rank-one type-A
good Sylow leaf. All other model obligations remain explicit. The finite,
simple and noncommutative guards are retained at the classification
boundary; no assertion about the remaining families is made here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

/-- The prime is the classifier parameter's actual defining prime. -/
theorem typeA_rankOne_goodSylowPrime (q : CFSG.PrimePower) :
    GoodSylowPrime (CFSG.Models.A 1 q) q.prime := by
  exact CFSGPSLTwoGoodSylow.psl_goodSylowPrime (F:=q.Field) q.prime

/-- Remove precisely the now-proved rank-one type-A branch. -/
def RemainingGoodSylowIndexWithoutRankOneTypeA : CFSG.Index → Prop
  | .A r _ _ _ => r≠1
  | _ => True

theorem model_goodSylow_or_remaining_without_rankOne_typeA
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (_hn : ¬ IsMulCommutative i.Model) :
    (∃ p,GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutRankOneTypeA i := by
  cases i <;> try exact Or.inr trivial
  case A r q hr hs hfinite hsimple =>
    by_cases h : r=1
    · subst r
      exact Or.inl ⟨q.prime,typeA_rankOne_goodSylowPrime q⟩
    · exact Or.inr h

theorem simple_goodSylow_of_cfsg_and_remaining_without_rankOne_typeA
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexWithoutRankOneTypeA i →
        ∃ p,GoodSylowPrime i.Model p)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ¬ IsMulCommutative T) : ∃ p,GoodSylowPrime T p := by
  apply simple_goodSylow_of_cfsg_models hCFSG ?_ T hT
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_rankOne_typeA i hn with h | h
  · exact h
  · exact remaining i hn h

/-- The Suzuki induction is composed only after every still-listed
model obligation is supplied. This is a reduction, not a CFSG-only proof. -/
theorem aschbacherGuralnick_of_cfsg_and_remaining_without_rankOne_typeA
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingGoodSylowIndexWithoutRankOneTypeA i →
        ∃ p,GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_rankOne_typeA i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
