import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarMaximalCliques
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GlobalTypeCoherence

/-! Actual point/maximal-space stars are in PROVED bijection with
ALL non-top original global maximal cliques. Neither direction is a
model-identification or recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem maximal_original_clique_nonempty (T : Set (SingularPlanes K 0))
    (hT : MaximalClique (originalPlaneAdjacent K) T) : T.Nonempty := by
  by_contra hn
  have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  have hc : Clique (originalPlaneAdjacent K) {originalRootPlane K} := by
    rintro P rfl Q rfl
    exact Or.inl rfl
  have hm := hT.2 {originalRootPlane K} hc (by rw [he]; exact Set.empty_subset _)
  have hh := hm (show originalRootPlane K ∈ ({originalRootPlane K} : Set (SingularPlanes K 0)) from rfl)
  have hf : originalRootPlane K ∈ (∅ : Set (SingularPlanes K 0)) := by
    rw [← he]
    exact hh
  exact hf

theorem every_non_top_clique_is_star (T : Set (SingularPlanes K 0))
    (hT : MaximalClique (originalPlaneAdjacent K) T) (ht : naturalCliqueType K T ≠ 0) :
    ∃ S : PointStarLabels K, pointStarPlanes K S = T := by
  obtain ⟨P, hP⟩ := maximal_original_clique_nonempty K T hT
  obtain ⟨g, hg⟩ := exists_natural_root_transporter K P
  let T0 := naturalCliqueImage K g⁻¹ T
  have hm : MaximalClique (originalPlaneAdjacent K) T0 := naturalCliqueImage_maximal K g⁻¹ T hT
  have hr : originalRootPlane K ∈ T0 := ⟨P, hP, by rw [← hg, naturalPlaneImage_inv_cancel]⟩
  have he : T = naturalCliqueImage K g T0 := by
    have hc : naturalCliqueImage K g T0 = T := by
      simpa only [inv_inv] using naturalCliqueImage_inv_cancel K g⁻¹ T
    exact hc.symm
  have htype := naturalImage_type_of_root_maximal_clique K g T0 hm hr
  rw [← he] at htype
  have ht0 : naturalCliqueType K T0 ≠ 0 := fun hz => ht (htype.trans hz)
  rcases maximal_original_clique_through_root_geometric K T0 hm hr with
    ⟨W, hW⟩ | ⟨U, p, hp⟩ | ⟨U, q, hq⟩
  · exact False.elim (ht0 (by rw [hW, completed_top_type]))
  · let M := columnMaximalExtension K p
    let S0 : PointStarLabels K :=
      ⟨(U.val, ⟨M.val, M.property.1, M.property.2.1⟩), U.property.1, U.property.2.trans M.property.2.2⟩
    have hs : pointStarPlanes K S0 = T0 := by
      rw [hp, rootCompleted_columnStar_eq]
      rfl
    refine ⟨naturalPointStarImage K g S0, ?_⟩
    calc
      pointStarPlanes K (naturalPointStarImage K g S0) = naturalCliqueImage K g (pointStarPlanes K S0) :=
        (naturalPointStarImage_sets K g S0).symm
      _ = naturalCliqueImage K g T0 := congrArg (naturalCliqueImage K g) hs
      _ = T := he.symm
  · let M := rowMaximalExtension K q
    let S0 : PointStarLabels K :=
      ⟨(U.val, ⟨M.val, M.property.1, M.property.2.1⟩), U.property.1, U.property.2.trans M.property.2.2⟩
    have hs : pointStarPlanes K S0 = T0 := by
      rw [hq, rootCompleted_rowStar_eq]
      rfl
    refine ⟨naturalPointStarImage K g S0, ?_⟩
    calc
      pointStarPlanes K (naturalPointStarImage K g S0) = naturalCliqueImage K g (pointStarPlanes K S0) :=
        (naturalPointStarImage_sets K g S0).symm
      _ = naturalCliqueImage K g T0 := congrArg (naturalCliqueImage K g) hs
      _ = T := he.symm

abbrev NonTopMaximalCliques :=
  {T : Set (SingularPlanes K 0) // MaximalClique (originalPlaneAdjacent K) T ∧ naturalCliqueType K T ≠ 0}

def starCliqueEmbedding (S : PointStarLabels K) : NonTopMaximalCliques K :=
  ⟨pointStarPlanes K S, pointStar_maximal_non_top K S⟩

def starCliqueEquiv : PointStarLabels K ≃ NonTopMaximalCliques K :=
  Equiv.ofBijective (starCliqueEmbedding K) ⟨
    fun S T he => pointStarPlanes_injective K (congrArg Subtype.val he),
    fun T => by
      obtain ⟨S, hS⟩ := every_non_top_clique_is_star K T.val T.property.1 T.property.2
      exact ⟨S, Subtype.ext hS⟩⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
