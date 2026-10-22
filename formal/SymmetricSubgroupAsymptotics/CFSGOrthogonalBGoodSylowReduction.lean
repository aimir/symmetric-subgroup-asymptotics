import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOppositeGeneration
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentSylow
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoGoodSylowReduction

/-! Actual good-Sylow data for the entire original B family. Odd
characteristic uses the literal quadratic roots and actual opposition;
characteristic two uses the already-proved original B/C equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent

theorem orthogonalB_elementary_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p r : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2:K)≠0) :
    GoodSylowPrime (elementaryRootGroup K (r+1)) p := by
  refine ⟨Fact.out,unipotentSylow K p r h2,
    CFSGOrthogonalBCoordinateFlip.opposition K r,?_,?_⟩
  · exact normalizer_unipotent_soluble K r h2
  · exact CFSGOrthogonalBCoordinateFlip.two_unipotents_generate K r

theorem orthogonalB_projective_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p r : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2:K)≠0) :
    GoodSylowPrime (elementaryProjective K (r+1)) p :=
  goodSylowPrime_surjective (QuotientGroup.mk' (Subgroup.center
    (elementaryRootGroup K (r+1)))) (QuotientGroup.mk'_surjective _)
      (orthogonalB_elementary_goodSylowPrime K p r h2)

theorem typeB_goodSylowPrime (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] :
    GoodSylowPrime (CFSG.Models.B r q) q.prime := by
  by_cases hq : q.prime=2
  · simpa only [hq] using typeB_charTwo_goodSylowPrime r hr q hq
  · have h2 : (2:q.Field)≠0 := by
      intro he
      have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp he
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)
    obtain ⟨s,rfl⟩ : ∃s:ℕ,r=s+3 := ⟨r-3,by omega⟩
    let e := serreProjectiveEquivElementaryProjective q.Field (s+2) h2
    letI orthogonalBGoodSylow_projectiveFinite : Finite (elementaryProjective q.Field (s+3)) :=
      Finite.of_surjective (QuotientGroup.mk' (Subgroup.center
        (elementaryRootGroup q.Field (s+3)))) (QuotientGroup.mk'_surjective _)
    exact goodSylowPrime_map e.symm
      (orthogonalB_projective_goodSylowPrime q.Field q.prime (s+2) h2)

def RemainingGoodSylowIndexWithoutTypeASuzukiBC : CFSG.Index → Prop
  | .B _ _ _ => False
  | i => RemainingGoodSylowIndexWithoutTypeASuzukiCCharTwoB i

theorem model_goodSylow_or_remaining_without_typeA_suzuki_B_C (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    (∃p,GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutTypeASuzukiBC i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_typeA_suzuki_C_charTwoB _ hn
  case B r q hr hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    exact Or.inl ⟨q.prime,typeB_goodSylowPrime r hr q⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_typeA_suzuki_B_C
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingGoodSylowIndexWithoutTypeASuzukiBC i→
        ∃p,GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_typeA_suzuki_B_C i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
