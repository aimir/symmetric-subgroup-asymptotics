import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarLabelInjective
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueComposition

/-! Literal E acts on point/maximal-space labels, and their full
original star sets transform by the SAME original plane action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

def naturalPointStarImage (g : elementaryRootGroup K 4) (S : PointStarLabels K) : PointStarLabels K :=
  ⟨(S.val.1.map (naturalLinearHom K 4 g).toLinearMap,
    ⟨S.val.2.val.map (naturalLinearHom K 4 g).toLinearMap,
      ((naturalLinearHom K 4 g).finrank_map_eq S.val.2.val).trans S.val.2.property.1,
      by rintro x ⟨y, hy, rfl⟩; exact (elementary_preserves_bundledQ K 0 g y).trans (S.val.2.property.2 y hy)⟩),
    ((naturalLinearHom K 4 g).finrank_map_eq S.val.1).trans S.property.1,
    Submodule.map_mono S.property.2⟩

theorem naturalPointStarImage_sets (g : elementaryRootGroup K 4) (S : PointStarLabels K) :
    naturalCliqueImage K g (pointStarPlanes K S) = pointStarPlanes K (naturalPointStarImage K g S) := by
  ext P
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact ⟨Submodule.map_mono hR.1, Submodule.map_mono hR.2⟩
  · intro hP
    let R := naturalPlaneImage K g⁻¹ P
    have he : naturalPlaneImage K g R = P := by
      simpa only [inv_inv] using naturalPlaneImage_inv_cancel K g⁻¹ P
    have hmap : R.val.map (naturalLinearHom K 4 g).toLinearMap = P.val := congrArg Subtype.val he
    refine ⟨R, ?_, he⟩
    constructor
    · apply (Submodule.map_le_map_iff_of_injective (naturalLinearHom K 4 g).injective S.val.1 R.val).mp
      rw [hmap]
      exact hP.1
    · apply (Submodule.map_le_map_iff_of_injective (naturalLinearHom K 4 g).injective R.val S.val.2.val).mp
      rw [hmap]
      exact hP.2

theorem naturalPointStarImage_inv_cancel (g : elementaryRootGroup K 4) (S : PointStarLabels K) :
    naturalPointStarImage K g⁻¹ (naturalPointStarImage K g S) = S := by
  apply pointStarPlanes_injective K
  rw [← naturalPointStarImage_sets, ← naturalPointStarImage_sets, naturalCliqueImage_inv_cancel]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
