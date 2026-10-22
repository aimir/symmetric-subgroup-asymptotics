import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarNaturalAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedGeometricCliques

/-! EVERY actual point/maximal-space star set is a genuine non-top
global maximal clique. This is proved by an actual elementary plane
transporter and the established root-extension exhaustion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K]

theorem pointStar_through_root_is_geometric (S : PointStarLabels K)
    (hr : originalRootPlane K ∈ pointStarPlanes K S) :
    (∃ U : RootPoints K, ∃ p : CFSGOrthogonalDIndexTrialityD2Coordinates.RulingParameters K,
      pointStarPlanes K S = rootCompletedClique K (neighborColumnStar K U p)) ∨
    (∃ U : RootPoints K, ∃ q : CFSGOrthogonalDIndexTrialityD2Coordinates.RulingParameters K,
      pointStarPlanes K S = rootCompletedClique K (neighborRowStar K U q)) := by
  let U : RootPoints K := ⟨S.val.1, S.property.1, hr.1⟩
  let M : MaximalExtensions K := ⟨S.val.2.val, S.val.2.property.1, S.val.2.property.2, hr.2⟩
  obtain ⟨j, hj⟩ := (maximalExtensionRulingEquiv K).surjective M
  rcases j with p | q
  · have he : columnMaximalExtension K p = M := hj
    refine Or.inl ⟨U, p, ?_⟩
    rw [rootCompleted_columnStar_eq]
    change globalStarPlanes K S.val.1 S.val.2.val = globalStarPlanes K S.val.1 (columnMaximalExtension K p).val
    exact congrArg (globalStarPlanes K S.val.1) (congrArg Subtype.val he).symm
  · have he : rowMaximalExtension K q = M := hj
    refine Or.inr ⟨U, q, ?_⟩
    rw [rootCompleted_rowStar_eq]
    change globalStarPlanes K S.val.1 S.val.2.val = globalStarPlanes K S.val.1 (rowMaximalExtension K q).val
    exact congrArg (globalStarPlanes K S.val.1) (congrArg Subtype.val he).symm

theorem pointStar_root_maximal_non_top [Finite K] (S : PointStarLabels K)
    (hr : originalRootPlane K ∈ pointStarPlanes K S) :
    MaximalClique (originalPlaneAdjacent K) (pointStarPlanes K S) ∧ naturalCliqueType K (pointStarPlanes K S) ≠ 0 := by
  rcases pointStar_through_root_is_geometric K S hr with ⟨U, p, he⟩ | ⟨U, q, he⟩
  · rw [he, completed_columnStar_type]
    exact ⟨completed_columnStar_maximal K U p, by decide⟩
  · rw [he, completed_rowStar_type]
    exact ⟨completed_rowStar_maximal K U q, by decide⟩

theorem pointStar_maximal_non_top [Finite K] (S : PointStarLabels K) :
    MaximalClique (originalPlaneAdjacent K) (pointStarPlanes K S) ∧ naturalCliqueType K (pointStarPlanes K S) ≠ 0 := by
  obtain ⟨P, _, hP, _, _⟩ := pointStar_has_two_planes K S
  obtain ⟨g, hg⟩ := exists_natural_root_transporter K P
  let S0 := naturalPointStarImage K g⁻¹ S
  have hr : originalRootPlane K ∈ pointStarPlanes K S0 := by
    rw [← naturalPointStarImage_sets]
    exact ⟨P, hP, by rw [← hg, naturalPlaneImage_inv_cancel]⟩
  have hs0 := pointStar_root_maximal_non_top K S0 hr
  have hinv : naturalPointStarImage K g S0 = S := by
    simpa only [inv_inv] using naturalPointStarImage_inv_cancel K g⁻¹ S
  have he : naturalCliqueImage K g (pointStarPlanes K S0) = pointStarPlanes K S :=
    (naturalPointStarImage_sets K g S0).trans (congrArg (pointStarPlanes K) hinv)
  have hmc := naturalCliqueImage_maximal K g (pointStarPlanes K S0) hs0.1
  have ht := naturalImage_type_of_root_maximal_clique K g (pointStarPlanes K S0) hs0.1 hr
  rw [he] at hmc ht
  exact ⟨hmc, fun hz => hs0.2 (ht.symm.trans hz)⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
