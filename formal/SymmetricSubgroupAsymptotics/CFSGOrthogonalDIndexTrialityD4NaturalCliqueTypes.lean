import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ActualCliqueSpan
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ElementaryComponentColor

/-! Three natural GLOBAL clique labels from actual subspace spans:
three-space tops, and the two genuine parity components of maximal
singular four-space stars. No automorphism invariance is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD2Coordinates CFSGOrthogonalDIndexSingularComponents
open CFSGOrthogonalDIndexPositiveSpace
variable (K : Type) [Field K]

def cliqueReferenceParameter : RulingParameters K :=
  Projectivization.mk K (Pi.single (0 : Fin 2) (1 : K)) (by simp)

def naturalCliqueType (T : Set (SingularPlanes K 0)) : Fin 3 :=
  if Module.finrank K (originalCliqueSpan K T) = 3 then 0 else
    if Even (distance 4 (columnMaximalExtension K (cliqueReferenceParameter K)).val
      (originalCliqueSpan K T)) then 1 else 2

theorem completed_top_type (W : ThreeExtensions K) :
    naturalCliqueType K (rootCompletedClique K (neighborTop K W)) = 0 := by
  unfold naturalCliqueType
  rw [completed_top_span, W.property.1, if_pos rfl]

theorem completed_columnStar_type (U : RootPoints K) (p : RulingParameters K) :
    naturalCliqueType K (rootCompletedClique K (neighborColumnStar K U p)) = 1 := by
  unfold naturalCliqueType
  rw [completed_columnStar_span, (columnMaximalExtension K p).property.1]
  rw [if_neg (show (4 : ℕ) ≠ 3 by decide), if_pos (column_column_extension_same_component K _ _)]

theorem completed_rowStar_type (U : RootPoints K) (q : RulingParameters K) :
    naturalCliqueType K (rootCompletedClique K (neighborRowStar K U q)) = 2 := by
  unfold naturalCliqueType
  rw [completed_rowStar_span, (rowMaximalExtension K q).property.1]
  rw [if_neg (show (4 : ℕ) ≠ 3 by decide), if_neg (column_row_extension_not_same_component K _ _)]

def naturalCliqueImage (g : elementaryRootGroup K 4) (T : Set (SingularPlanes K 0)) :
    Set (SingularPlanes K 0) := naturalPlaneImage K g '' T

theorem originalCliqueSpan_naturalImage (g : elementaryRootGroup K 4)
    (T : Set (SingularPlanes K 0)) :
    originalCliqueSpan K (naturalCliqueImage K g T) =
      (originalCliqueSpan K T).map (naturalLinearHom K 4 g).toLinearMap := by
  apply le_antisymm
  · apply sSup_le
    rintro P ⟨S, ⟨R, hR, rfl⟩, rfl⟩
    exact Submodule.map_mono (le_sSup ⟨R, hR, rfl⟩)
  · apply Submodule.map_le_iff_le_comap.mpr
    apply sSup_le
    rintro P ⟨R, hR, rfl⟩
    apply Submodule.map_le_iff_le_comap.mp
    exact le_sSup ⟨naturalPlaneImage K g R, ⟨R, hR, rfl⟩, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
