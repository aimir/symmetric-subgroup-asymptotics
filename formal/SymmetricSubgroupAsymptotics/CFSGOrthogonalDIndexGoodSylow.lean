import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylow
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBorelSoluble
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeGeneration
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Actual good defining-characteristic Sylow data for every original
type-D simple model. The literal U, its soluble original normalizer,
and its actual Coxeter conjugate are retained through the original
central quotient and proved Serre realization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDIndexSylow

theorem orthogonalD_normalizer_unipotent_soluble (K : Type) [Field K] (s : ℕ) :
    IsSolvable (Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) := by
  letI : IsSolvable (borel K (s + 4)) := borel_soluble K (s + 4)
  exact solvable_of_solvable_injective
    (f := Subgroup.inclusion (CFSGOrthogonalDIndexComponentNormalizer.normalizer_le_borel K s))
    (Subgroup.inclusion_injective _)

theorem orthogonalD_elementary_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p s : ℕ) [Fact p.Prime] [CharP K p] :
    GoodSylowPrime (elementaryRootGroup K (s + 4)) p := by
  refine ⟨Fact.out, unipotentSylow K s p, coxeterWeyl K (s + 3), ?_, ?_⟩
  · exact orthogonalD_normalizer_unipotent_soluble K s
  · exact CFSGOrthogonalDIndexOppositeGeneration.two_unipotents_generate K s

theorem orthogonalD_projective_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p s : ℕ) [Fact p.Prime] [CharP K p] :
    GoodSylowPrime (elementaryProjective K (s + 4)) p :=
  goodSylowPrime_surjective (QuotientGroup.mk' (Subgroup.center
    (elementaryRootGroup K (s + 4)))) (QuotientGroup.mk'_surjective _)
      (orthogonalD_elementary_goodSylowPrime K p s)

theorem typeD_goodSylowPrime (r : ℕ) (q : CFSG.PrimePower) (hr : 4 ≤ r)
    [IsSimpleGroup (CFSG.Models.D r q)] : GoodSylowPrime (CFSG.Models.D r q) q.prime := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  letI orthogonalDGoodSylowProjectiveFinite : Finite (elementaryProjective q.Field (s + 4)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center
      (elementaryRootGroup q.Field (s + 4)))) (QuotientGroup.mk'_surjective _)
  let e : CFSG.Models.D (s + 4) q ≃* elementaryProjective q.Field (s + 4) :=
    serreProjectiveEquivElementaryProjective q.Field s
  exact goodSylowPrime_map e.symm (orthogonalD_projective_goodSylowPrime q.Field q.prime s)

end SymmetricSubgroupAsymptotics.CFSGReduction
