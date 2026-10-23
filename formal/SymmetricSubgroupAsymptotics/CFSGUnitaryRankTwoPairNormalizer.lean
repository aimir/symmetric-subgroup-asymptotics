import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoOppositeNormalizerTorus
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoFlagNormalizer

/-! The actual full upper/opposite Sylow normalizer intersection equals
its literal projective torus. Both inclusions are proved on the original
matrix cover; no abstract automorphism recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rankTwo_torus_le_flag (q : CFSG.PrimePower) :
    (rankTwoNaturalTorus q).range ≤ rankTwoUpperFlag q := by
  rintro _ ⟨z, rfl⟩
  apply (rankTwoUpperFlag_mem_iff q _).mpr
  intro i j hij
  rw [rankTwoNaturalTorus_matrix]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

theorem rankTwo_reversal_torus_le_flag (q : CFSG.PrimePower)
    (t : naturalFixed 2 q) (ht : t ∈ (rankTwoNaturalTorus q).range) :
    (reversalFixed q 2)⁻¹ * t * reversalFixed q 2 ∈ rankTwoUpperFlag q := by
  obtain ⟨z, rfl⟩ := ht
  apply (rankTwoUpperFlag_mem_iff q _).mpr
  intro i j hij
  rw [reversal_inverse_conjugation q 2]
  change ((signedReversalUnit (q.Extension 2) 2 : Mat (q.Extension 2) 2) *
    (((rankTwoNaturalTorus q z).val).val : Mat (q.Extension 2) 2) *
    (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2)) i j = 0
  rw [signedReversal_conjugation_entry, rankTwoNaturalTorus_matrix]
  have hne : i.rev ≠ j.rev := fun h => (ne_of_gt hij) (Fin.rev_injective h)
  simp [Matrix.diagonal_apply_ne _ hne]

theorem rankTwo_torus_le_natural_pair_normalizer (q : CFSG.PrimePower) :
    (rankTwoNaturalTorus q).range ≤
      Subgroup.normalizer (rankTwoUpperSubgroup q : Set _) ⊓
        Subgroup.normalizer (rankTwoOppositeSubgroup q : Set _) := by
  intro t ht
  constructor
  · rw [rankTwo_natural_normalizer_eq_flag]
    exact rankTwo_torus_le_flag q ht
  · let w := reversalFixed q 2
    have hk : w⁻¹ * t * w ∈ Subgroup.normalizer (rankTwoUpperSubgroup q : Set _) := by
      rw [rankTwo_natural_normalizer_eq_flag]
      exact rankTwo_reversal_torus_le_flag q t ht
    apply (rankTwoUpperSubgroup q).le_normalizer_map (MulAut.conj w).toMonoidHom
    refine ⟨w⁻¹ * t * w, hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem rankTwo_natural_pair_normalizer_eq_torus (q : CFSG.PrimePower) :
    Subgroup.normalizer (rankTwoUpperSubgroup q : Set _) ⊓
      Subgroup.normalizer (rankTwoOppositeSubgroup q : Set _) =
        (rankTwoNaturalTorus q).range :=
  le_antisymm (rankTwo_natural_pair_normalizer_le_torus q)
    (rankTwo_torus_le_natural_pair_normalizer q)

theorem rankTwo_projective_pair_normalizer_eq_torus (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) :
    Subgroup.normalizer ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq) : Set _) ⊓
      Subgroup.normalizer ((rankTwoOppositeSubgroup q).map (rankTwoProjectiveCover q hq) : Set _) =
        (rankTwoProjectiveTorus q hq).range := by
  apply le_antisymm (rankTwo_projective_pair_normalizer_le_torus q hq)
  rintro _ ⟨z, rfl⟩
  have ht := rankTwo_torus_le_natural_pair_normalizer q
    (show rankTwoNaturalTorus q z ∈ (rankTwoNaturalTorus q).range from ⟨z, rfl⟩)
  exact ⟨(rankTwoUpperSubgroup q).le_normalizer_map (rankTwoProjectiveCover q hq)
      ⟨_, ht.1, rfl⟩,
    (rankTwoOppositeSubgroup q).le_normalizer_map (rankTwoProjectiveCover q hq)
      ⟨_, ht.2, rfl⟩⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
