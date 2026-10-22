import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedGeometricCliques

/-! Root-completed residue cliques are the literal global geometric
sets: all two-planes in a three-space, or all incident two-planes
between a point and a maximal singular space. Quadratic zero is kept
in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

theorem mem_rootCompletedClique_iff (S : Set (Neighbors K)) (P : SingularPlanes K 0) :
    P ∈ rootCompletedClique K S ↔
      P = originalRootPlane K ∨ ∃ N ∈ S, neighborAsPlane K N = P := by
  constructor
  · rintro (he | ⟨h, hS⟩)
    · exact Or.inl he
    · exact Or.inr ⟨(neighborSubsetEquiv K).symm ⟨P, h⟩, hS, Subtype.ext rfl⟩
  · rintro (he | ⟨N, hN, rfl⟩)
    · exact Or.inl he
    · refine Or.inr ⟨originalRoot_adjacent_neighbor K N, ?_⟩
      exact hN

private theorem plane_inf_finrank_one (P Q : SingularPlanes K 0) (hne : P ≠ Q)
    (hlo : 1 ≤ Module.finrank K ↥(P.val ⊓ Q.val)) :
    Module.finrank K ↥(P.val ⊓ Q.val) = 1 := by
  have hhi := Submodule.finrank_mono (inf_le_left : P.val ⊓ Q.val ≤ P.val)
  rw [P.property.1] at hhi
  by_cases he : Module.finrank K ↥(P.val ⊓ Q.val) = 2
  · have hP : P.val ⊓ Q.val = P.val :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [he, P.property.1])
    have hQ : P.val ⊓ Q.val = Q.val :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [he, Q.property.1])
    exact False.elim (hne (Subtype.ext (hP.symm.trans hQ)))
  · omega

private theorem plane_in_three_is_neighbor (W : ThreeExtensions K) (P : SingularPlanes K 0)
    (hP : P.val ≤ W.val) (hne : P ≠ originalRootPlane K) :
    originalPlaneAdjacent K (originalRootPlane K) P := by
  have hs := Submodule.finrank_mono (sup_le W.property.2.2 hP : rootPlane K ⊔ P.val ≤ W.val)
  rw [W.property.1] at hs
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (rootPlane K) P.val
  rw [rootPlane_finrank, P.property.1] at hd
  have hlo : 1 ≤ Module.finrank K ↥((originalRootPlane K).val ⊓ P.val) := by
    change 1 ≤ Module.finrank K ↥(rootPlane K ⊓ P.val)
    omega
  refine ⟨fun he => hne (Subtype.ext he.symm),
    plane_inf_finrank_one K (originalRootPlane K) P (Ne.symm hne) hlo, ?_⟩
  intro z hz
  exact W.property.2.1 z ((sup_le W.property.2.2 hP) hz)

private theorem plane_in_star_is_neighbor (U : RootPoints K) (M : MaximalExtensions K)
    (P : SingularPlanes K 0) (hUP : U.val ≤ P.val) (hPM : P.val ≤ M.val)
    (hne : P ≠ originalRootPlane K) : originalPlaneAdjacent K (originalRootPlane K) P := by
  have hlo := Submodule.finrank_mono (le_inf U.property.2 hUP)
  rw [U.property.1] at hlo
  refine ⟨fun he => hne (Subtype.ext he.symm),
    plane_inf_finrank_one K (originalRootPlane K) P (Ne.symm hne) hlo, ?_⟩
  intro z hz
  exact M.property.2.1 z ((sup_le M.property.2.2 hPM) hz)

theorem rootCompleted_top_eq (W : ThreeExtensions K) :
    rootCompletedClique K (neighborTop K W) = {P : SingularPlanes K 0 | P.val ≤ W.val} := by
  ext P
  rw [mem_rootCompletedClique_iff]
  constructor
  · rintro (rfl | ⟨N, hN, rfl⟩)
    · exact W.property.2.2
    · exact hN
  · intro hP
    by_cases he : P = originalRootPlane K
    · exact Or.inl he
    · have hn := plane_in_three_is_neighbor K W P hP he
      exact Or.inr ⟨(neighborSubsetEquiv K).symm ⟨P, hn⟩, hP, Subtype.ext rfl⟩

theorem rootCompleted_columnStar_eq (U : RootPoints K)
    (p : CFSGOrthogonalDIndexTrialityD2Coordinates.RulingParameters K) :
    rootCompletedClique K (neighborColumnStar K U p) =
      {P : SingularPlanes K 0 | U.val ≤ P.val ∧ P.val ≤ (columnMaximalExtension K p).val} := by
  ext P
  rw [mem_rootCompletedClique_iff]
  constructor
  · rintro (rfl | ⟨N, hN, rfl⟩)
    · exact ⟨U.property.2, (columnMaximalExtension K p).property.2.2⟩
    · exact hN
  · intro hP
    by_cases he : P = originalRootPlane K
    · exact Or.inl he
    · have hn := plane_in_star_is_neighbor K U (columnMaximalExtension K p) P hP.1 hP.2 he
      exact Or.inr ⟨(neighborSubsetEquiv K).symm ⟨P, hn⟩, hP, Subtype.ext rfl⟩

theorem rootCompleted_rowStar_eq (U : RootPoints K)
    (q : CFSGOrthogonalDIndexTrialityD2Coordinates.RulingParameters K) :
    rootCompletedClique K (neighborRowStar K U q) =
      {P : SingularPlanes K 0 | U.val ≤ P.val ∧ P.val ≤ (rowMaximalExtension K q).val} := by
  ext P
  rw [mem_rootCompletedClique_iff]
  constructor
  · rintro (rfl | ⟨N, hN, rfl⟩)
    · exact ⟨U.property.2, (rowMaximalExtension K q).property.2.2⟩
    · exact hN
  · intro hP
    by_cases he : P = originalRootPlane K
    · exact Or.inl he
    · have hn := plane_in_star_is_neighbor K U (rowMaximalExtension K q) P hP.1 hP.2 he
      exact Or.inr ⟨(neighborSubsetEquiv K).symm ⟨P, hn⟩, hP, Subtype.ext rfl⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
