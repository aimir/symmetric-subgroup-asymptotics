import SymmetricSubgroupAsymptotics.CFSGSymplecticGoodSylowReduction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoProjectiveEquiv

/-! Actual good-Sylow data transfers to the original characteristic-two
B model by its proved faithful projective C realization. No extra natural
faithfulness, C-source simplicity, or B Sylow-recognition premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem typeB_charTwo_goodSylowPrime (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hq : q.prime=2) [IsSimpleGroup (CFSG.Models.B r q)] :
    GoodSylowPrime (CFSG.Models.B r q) 2 := by
  letI : CharP q.Field 2 := by rw [←hq]; infer_instance
  obtain ⟨k,rfl⟩ : ∃k:ℕ,r=k+1 := ⟨r-1,by omega⟩
  exact goodSylowPrime_map
    (CFSGOrthogonalBSerreMatrices.serreProjectiveEquivSymplecticProjective_charTwo
      q.Field k (by omega)).symm
    (symplectic_projective_goodSylowPrime q.Field 2 k (by omega))

def RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoB : CFSG.Index → Prop
  | .B _ q _ => q.prime≠2
  | i => RemainingGoodSylowIndexWithoutTypeASuzukiC i

theorem model_goodSylow_or_remaining_without_typeA_suzuki_C_charTwoB (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    (∃p,GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoB i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_typeA_suzuki_C _ hn
  case B r q hr hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    by_cases hq : q.prime=2
    · exact Or.inl ⟨2,typeB_charTwo_goodSylowPrime r hr q hq⟩
    · exact Or.inr hq

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_typeA_suzuki_C_charTwoB
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoB i→
        ∃p,GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_typeA_suzuki_C_charTwoB i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
