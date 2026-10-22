import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueTypes

/-! Actual elementary transport preserves the three global clique
labels. The proof uses genuine quadratic component parity for stars;
no automorphism type-preservation is asserted as an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexSingularComponents
open CFSGOrthogonalDIndexTrialityD2Coordinates CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K]

theorem naturalImage_top_type (g : elementaryRootGroup K 4) (W : ThreeExtensions K) :
    naturalCliqueType K (naturalCliqueImage K g (rootCompletedClique K (neighborTop K W))) = 0 := by
  have hd : Module.finrank K (W.val.map (naturalLinearHom K 4 g).toLinearMap) = 3 :=
    ((naturalLinearHom K 4 g).finrank_map_eq W.val).trans W.property.1
  unfold naturalCliqueType
  rw [originalCliqueSpan_naturalImage, completed_top_span, hd, if_pos rfl]

theorem naturalImage_columnStar_type (g : elementaryRootGroup K 4) (U : RootPoints K)
    (p : RulingParameters K) :
    naturalCliqueType K (naturalCliqueImage K g
      (rootCompletedClique K (neighborColumnStar K U p))) = 1 := by
  let B := columnMaximalExtension K (cliqueReferenceParameter K)
  let M := columnMaximalExtension K p
  have hd : Module.finrank K (M.val.map (naturalLinearHom K 4 g).toLinearMap) = 4 :=
    ((naturalLinearHom K 4 g).finrank_map_eq M.val).trans M.property.1
  have he : Even (distance 4 B.val (M.val.map (naturalLinearHom K 4 g).toLinearMap)) :=
    (elementary_preserves_extension_component K g B M).mpr
      (column_column_extension_same_component K _ _)
  unfold naturalCliqueType
  rw [originalCliqueSpan_naturalImage, completed_columnStar_span]
  change (if Module.finrank K (M.val.map (naturalLinearHom K 4 g).toLinearMap) = 3 then
    (0 : Fin 3) else if Even (distance 4 B.val (M.val.map (naturalLinearHom K 4 g).toLinearMap))
    then 1 else 2) = 1
  rw [hd, if_neg (show (4 : ℕ) ≠ 3 by decide), if_pos he]

theorem naturalImage_rowStar_type (g : elementaryRootGroup K 4) (U : RootPoints K)
    (q : RulingParameters K) :
    naturalCliqueType K (naturalCliqueImage K g
      (rootCompletedClique K (neighborRowStar K U q))) = 2 := by
  let B := columnMaximalExtension K (cliqueReferenceParameter K)
  let M := rowMaximalExtension K q
  have hd : Module.finrank K (M.val.map (naturalLinearHom K 4 g).toLinearMap) = 4 :=
    ((naturalLinearHom K 4 g).finrank_map_eq M.val).trans M.property.1
  have he : ¬ Even (distance 4 B.val (M.val.map (naturalLinearHom K 4 g).toLinearMap)) := by
    intro h
    exact column_row_extension_not_same_component K _ _
      ((elementary_preserves_extension_component K g B M).mp h)
  unfold naturalCliqueType
  rw [originalCliqueSpan_naturalImage, completed_rowStar_span]
  change (if Module.finrank K (M.val.map (naturalLinearHom K 4 g).toLinearMap) = 3 then
    (0 : Fin 3) else if Even (distance 4 B.val (M.val.map (naturalLinearHom K 4 g).toLinearMap))
    then 1 else 2) = 2
  rw [hd, if_neg (show (4 : ℕ) ≠ 3 by decide), if_neg he]

theorem naturalImage_type_of_root_maximal_clique [Finite K] (g : elementaryRootGroup K 4)
    (T : Set (SingularPlanes K 0)) (hT : MaximalClique (originalPlaneAdjacent K) T)
    (hx : originalRootPlane K ∈ T) :
    naturalCliqueType K (naturalCliqueImage K g T) = naturalCliqueType K T := by
  rcases maximal_original_clique_through_root_geometric K T hT hx with
    ⟨W, rfl⟩ | ⟨U, p, rfl⟩ | ⟨U, q, rfl⟩
  · rw [naturalImage_top_type, completed_top_type]
  · rw [naturalImage_columnStar_type, completed_columnStar_type]
  · rw [naturalImage_rowStar_type, completed_rowStar_type]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
