import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarNaturalAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit

/-! Literal Q-singular points are exactly the point labels of actual
stars. Every incident original point/plane pair is contained in such
a star, using actual elementary vector/plane orbit theorems. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveSpace
variable (K : Type) [Field K]

abbrev OriginalPoints := CFSGOrthogonalDIndexQuadraticSubspacePoints.Points (splitQuadraticForm K 4)

def pointOfStar (S : PointStarLabels K) : OriginalPoints K :=
  ⟨S.val.1, S.property.1, fun x hx => S.val.2.property.2 x (S.property.2 hx)⟩

theorem pointOfStar_surjective : Function.Surjective (pointOfStar K) := by
  intro U
  obtain ⟨u, huU, hu0⟩ := CFSGOrthogonalDIndexQuadraticSubspacePoints.point_nonzero
    (splitQuadraticForm K 4) U
  have hQu : CFSGOrthogonalDIndexQuadraticForm.splitQ K u = 0 := by
    simpa only [splitQuadraticForm_apply] using U.property.2 u huU
  obtain ⟨g, hg⟩ := CFSGOrthogonalDIndexVectorCoordinates.exists_normalize_singular K 2 u hu0 hQu
  have hgu : naturalLinearHom K 4 g u = Pi.single (Sum.inl 0) 1 := hg
  let M := (positiveSpace K 4).map (naturalLinearHom K 4 g⁻¹).toLinearMap
  have hdM : Module.finrank K M = 4 :=
    ((naturalLinearHom K 4 g⁻¹).finrank_map_eq (positiveSpace K 4)).trans (positiveSpace_finrank K 4)
  have hzM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0 := by
    rintro x ⟨y, hy, rfl⟩
    exact (elementary_preserves_bundledQ K 0 g⁻¹ y).trans (positiveSpace_singular K 4 ⟨y, hy⟩)
  have huM : u ∈ M := by
    refine ⟨Pi.single (Sum.inl 0) 1, ?_, ?_⟩
    · intro j
      simp only [Pi.single_apply, Sum.inr_ne_inl, if_false]
    · rw [← hgu, map_inv]
      exact (naturalLinearHom K 4 g).symm_apply_apply u
  have hUM : U.val ≤ M := by
    rw [← CFSGOrthogonalDIndexQuadraticSubspacePoints.point_span (splitQuadraticForm K 4) U u huU hu0]
    exact (Submodule.span_singleton_le_iff_mem u M).mpr huM
  exact ⟨⟨(U.val, ⟨M, hdM, hzM⟩), U.property.1, hUM⟩, Subtype.ext rfl⟩

theorem incident_pair_in_star (U : OriginalPoints K) (P : SingularPlanes K 0)
    (hUP : U.val ≤ P.val) :
    ∃ S : PointStarLabels K, pointOfStar K S = U ∧ P ∈ pointStarPlanes K S := by
  obtain ⟨g, hg⟩ := exists_natural_root_transporter K P
  let M := (positiveSpace K 4).map (naturalLinearHom K 4 g).toLinearMap
  have hdM : Module.finrank K M = 4 :=
    ((naturalLinearHom K 4 g).finrank_map_eq (positiveSpace K 4)).trans (positiveSpace_finrank K 4)
  have hzM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0 := by
    rintro x ⟨y, hy, rfl⟩
    exact (elementary_preserves_bundledQ K 0 g y).trans (positiveSpace_singular K 4 ⟨y, hy⟩)
  have hPM : P.val ≤ M := by
    have hh := Submodule.map_mono (rootPlane_le_positive K) (f := (naturalLinearHom K 4 g).toLinearMap)
    have he : (rootPlane K).map (naturalLinearHom K 4 g).toLinearMap = P.val := congrArg Subtype.val hg
    rw [he] at hh
    exact hh
  exact ⟨⟨(U.val, ⟨M, hdM, hzM⟩), U.property.1, hUP.trans hPM⟩,
    Subtype.ext rfl, hUP, hPM⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
