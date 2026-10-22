import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborTriangles

/-! The actual D4 neighbour relation is exactly agreement in two of
the three displayed flag coordinates, with distinct original planes.
Coincident triples still represent different adjacent planes; no fibre
has been silently collapsed and no global triality coherence is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

theorem neighborThreeSpace_eq_parameters (S : Neighbors K) :
    neighborThreeSpace K S = threeExtensionRulingEquiv K (neighborOppositeParameters K S) :=
  ((threeExtensionRulingEquiv K).apply_symm_apply _).symm

theorem neighbor_threeSpace_le_maximal_iff (S : Neighbors K) (M : MaximalExtensions K) :
    (neighborThreeSpace K S).val ≤ M.val ↔
      M = columnMaximalExtension K (neighborOppositeParameters K S).1 ∨
        M = rowMaximalExtension K (neighborOppositeParameters K S).2 := by
  rw [neighborThreeSpace_eq_parameters]
  exact threeExtension_le_maximal_iff K _ _ M

theorem adjacent_neighbors_share_opposite_parameter (S T : Neighbors K)
    (hST : NeighborAdjacent K S T) :
    (neighborOppositeParameters K S).1 = (neighborOppositeParameters K T).1 ∨
      (neighborOppositeParameters K S).2 = (neighborOppositeParameters K T).2 := by
  obtain ⟨M, hS, hT⟩ := adjacent_neighbors_common_maximal K S T hST
  rw [neighbor_threeSpace_le_maximal_iff] at hS hT
  rcases hS with hS | hS <;> rcases hT with hT | hT
  · exact Or.inl (columnMaximalExtension_injective K (hS.symm.trans hT))
  · exact False.elim (columnMaximalExtension_ne_rowMaximalExtension K _ _ (hS.symm.trans hT))
  · exact False.elim (columnMaximalExtension_ne_rowMaximalExtension K _ _ (hT.symm.trans hS))
  · exact Or.inr (rowMaximalExtension_injective K (hS.symm.trans hT))

private theorem distinct_neighbor_inf_le_one (S T : Neighbors K) (hne : S ≠ T) :
    Module.finrank K ↥(S.val ⊓ T.val) ≤ 1 := by
  have hb := Submodule.finrank_mono (inf_le_left : S.val ⊓ T.val ≤ S.val)
  rw [S.property.1] at hb
  by_contra hbad
  have hd : Module.finrank K ↥(S.val ⊓ T.val) = 2 := by omega
  have heS : S.val ⊓ T.val = S.val := Submodule.eq_of_le_of_finrank_le inf_le_left
    (by rw [hd, S.property.1])
  have heT : S.val ⊓ T.val = T.val := Submodule.eq_of_le_of_finrank_le inf_le_right
    (by rw [hd, T.property.1])
  exact hne (Subtype.ext (heS.symm.trans heT))

theorem adjacent_of_same_threeSpace (S T : Neighbors K) (hne : S ≠ T)
    (hW : neighborThreeSpace K S = neighborThreeSpace K T) : NeighborAdjacent K S T := by
  have hT : T.val ≤ (neighborThreeSpace K S).val := by
    rw [hW]
    exact neighbor_le_threeSpace K T
  have hsup := sup_le (neighbor_le_threeSpace K S) hT
  have hb := Submodule.finrank_mono hsup
  rw [(neighborThreeSpace K S).property.1] at hb
  have hd := Submodule.finrank_sup_add_finrank_inf_eq S.val T.val
  rw [S.property.1, T.property.1] at hd
  have hi := distinct_neighbor_inf_le_one K S T hne
  refine ⟨hne, by omega, ?_⟩
  intro x hx
  exact (neighborThreeSpace K S).property.2.1 x (hsup hx)

theorem adjacent_of_same_point_common_maximal (S T : Neighbors K) (hne : S ≠ T)
    (hU : neighborPoint K S = neighborPoint K T) (M : MaximalExtensions K)
    (hSM : S.val ≤ M.val) (hTM : T.val ≤ M.val) : NeighborAdjacent K S T := by
  have hUT : (neighborPoint K S).val ≤ T.val := by
    rw [hU]
    exact neighbor_point_le K T
  have hb := Submodule.finrank_mono (le_inf (neighbor_point_le K S) hUT)
  rw [(neighborPoint K S).property.1] at hb
  have hi := distinct_neighbor_inf_le_one K S T hne
  refine ⟨hne, by omega, ?_⟩
  intro x hx
  exact M.property.2.1 x ((sup_le hSM hTM) hx)

def SameTwoNeighborFlags (S T : Neighbors K) : Prop :=
  (neighborPoint K S = neighborPoint K T ∧
    ((neighborOppositeParameters K S).1 = (neighborOppositeParameters K T).1 ∨
      (neighborOppositeParameters K S).2 = (neighborOppositeParameters K T).2)) ∨
    neighborOppositeParameters K S = neighborOppositeParameters K T

theorem neighbor_adjacent_iff_two_flags (S T : Neighbors K) :
    NeighborAdjacent K S T ↔ S ≠ T ∧ SameTwoNeighborFlags K S T := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_cases hU : neighborPoint K S = neighborPoint K T
    · exact Or.inl ⟨hU, adjacent_neighbors_share_opposite_parameter K S T h⟩
    · exact Or.inr (neighbor_parameters_eq_of_points_ne K S T h.2.1 hU)
  · rintro ⟨hne, (⟨hU, hp | hq⟩ | hparam)⟩
    · let M := columnMaximalExtension K (neighborOppositeParameters K S).1
      apply adjacent_of_same_point_common_maximal K S T hne hU M
      · exact (neighbor_le_threeSpace K S).trans
          ((neighbor_threeSpace_le_maximal_iff K S M).mpr (Or.inl rfl))
      · apply (neighbor_le_threeSpace K T).trans
        apply (neighbor_threeSpace_le_maximal_iff K T M).mpr
        exact Or.inl (congrArg (columnMaximalExtension K) hp)
    · let M := rowMaximalExtension K (neighborOppositeParameters K S).2
      apply adjacent_of_same_point_common_maximal K S T hne hU M
      · exact (neighbor_le_threeSpace K S).trans
          ((neighbor_threeSpace_le_maximal_iff K S M).mpr (Or.inr rfl))
      · apply (neighbor_le_threeSpace K T).trans
        apply (neighbor_threeSpace_le_maximal_iff K T M).mpr
        exact Or.inr (congrArg (rowMaximalExtension K) hq)
    · apply adjacent_of_same_threeSpace K S T hne
      rw [neighborThreeSpace_eq_parameters K S, neighborThreeSpace_eq_parameters K T, hparam]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
