import SymmetricSubgroupAsymptotics.CFSGSymplecticOppositeUnipotent
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentSylow
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective
import SymmetricSubgroupAsymptotics.CFSGTypeASuzukiModelGoodSylow

/-! Actual good Sylow data for every original type-C simple model. The
original matrix Sylow, its soluble normalizer, and its opposite generate
before passage through the actual central quotient and Serre realization. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices CFSGSymplecticUnipotent

theorem symplectic_elementary_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p r : ℕ) [Fact p.Prime] [CharP K p] (hr : 0<r) :
    GoodSylowPrime (elementaryRootGroup K (r+1)) p := by
  refine ⟨Fact.out,unipotentSylow K p r hr,
    CFSGSymplecticOppositeUnipotent.opposition K (r+1),?_,?_⟩
  · exact normalizer_unipotent_soluble K r hr
  · exact CFSGSymplecticOppositeUnipotent.two_unipotents_generate K (r+1)

theorem symplectic_projective_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p r : ℕ) [Fact p.Prime] [CharP K p] (hr : 0<r) :
    GoodSylowPrime (elementaryProjective K (r+1)) p := by
  exact goodSylowPrime_surjective (QuotientGroup.mk' (Subgroup.center
    (elementaryRootGroup K (r+1)))) (QuotientGroup.mk'_surjective _)
    (symplectic_elementary_goodSylowPrime K p r hr)

theorem typeC_goodSylowPrime (r : ℕ) (q : CFSG.PrimePower) (hr : 2≤r)
    [IsSimpleGroup (CFSG.Models.C r q)] : GoodSylowPrime (CFSG.Models.C r q) q.prime := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  exact goodSylowPrime_map (serreProjectiveEquivElementaryProjective q.Field k).symm
    (symplectic_projective_goodSylowPrime q.Field q.prime k (by omega))

def RemainingGoodSylowIndexWithoutTypeASuzukiC : CFSG.Index → Prop
  | .C _ _ _ _ => False
  | i => RemainingGoodSylowIndexWithoutTypeASuzuki i

theorem model_goodSylow_or_remaining_without_typeA_suzuki_C (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    (∃p,GoodSylowPrime i.Model p) ∨ RemainingGoodSylowIndexWithoutTypeASuzukiC i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_typeA_suzuki _ hn
  case C r q hr hs hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.C r q) := hsimple
    exact Or.inl ⟨q.prime,typeC_goodSylowPrime r q hr⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_typeA_suzuki_C
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingGoodSylowIndexWithoutTypeASuzukiC i→
        ∃p,GoodSylowPrime i.Model p) : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_typeA_suzuki_C i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
