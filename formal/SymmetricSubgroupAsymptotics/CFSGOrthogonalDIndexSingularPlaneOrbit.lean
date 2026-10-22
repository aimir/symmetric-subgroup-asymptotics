import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPairOrbit
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalSubmoduleBasis
import Mathlib.LinearAlgebra.Span.Basic

/-! Every two-dimensional submodule singular for the original split Q
is an original D root-plane label. This includes characteristic two;
polar isotropy alone is deliberately not substituted for Q-singularity.
There is no projective/building reconstruction or triality claim here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPlaneOrbit
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexFlagVectors CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexSingularRootPlanes
open CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

theorem exists_conjugateRootPlane_of_singular (s : ℕ)
    (P : Submodule K (Index (s + 4) → K)) (hdim : Module.finrank K P = 2)
    (hs : ∀ x ∈ P, splitQuadraticForm K (s + 4) x = 0) :
    ∃ g : elementaryRootGroup K (s + 4), P = conjugateRootPlane K s g := by
  obtain ⟨v, hv, w, hw, hv0, hnot, hspan⟩ :=
    CFSGTwoDimensionalSubmoduleBasis.exists_pair P hdim
  have hsv : splitQ K v = 0 := (splitQuadraticForm_apply K (s + 4) v).symm.trans (hs v hv)
  have hsw : splitQ K w = 0 := (splitQuadraticForm_apply K (s + 4) w).symm.trans (hs w hw)
  have hvw : polar K v w = 0 := by
    have hh := hs (v + w) (P.add_mem hv hw)
    rw [splitQuadraticForm_apply, splitQ_add, hsv, hsw, zero_add, zero_add] at hh
    exact hh
  obtain ⟨a, c, hav, haw⟩ := exists_singular_pair_frame K s v w hv0 hsv hsw hvw hnot
  have hmap : P.map (Matrix.mulVecLin (a.val : Mat K (s + 4))) = standardRootPlane K s := by
    rw [← hspan, Submodule.map_span, Set.image_pair]
    change Submodule.span K {(a.val : Mat K (s + 4)) *ᵥ v,
      (a.val : Mat K (s + 4)) *ᵥ w} = standardRootPlane K s
    rw [hav, haw]
    exact CFSGTwoDimensionalSubmoduleBasis.span_pair_shear (firstVector K s) (secondVector K s) c
  refine ⟨a⁻¹, ?_⟩
  rw [conjugateRootPlane_eq_map_standard]
  change P = (standardRootPlane K s).map (Matrix.mulVecLin (↑(a.val⁻¹) : Mat K (s + 4)))
  rw [← hmap, ← Submodule.map_comp, ← Matrix.mulVecLin_mul,
    Units.inv_mul, Matrix.mulVecLin_one, Submodule.map_id]

theorem singular_two_plane_iff_conjugateRootPlane (s : ℕ)
    (P : Submodule K (Index (s + 4) → K)) :
    (Module.finrank K P = 2 ∧ ∀ x ∈ P, splitQuadraticForm K (s + 4) x = 0) ↔
      ∃ g : elementaryRootGroup K (s + 4), P = conjugateRootPlane K s g := by
  constructor
  · rintro ⟨hd, hs⟩
    exact exists_conjugateRootPlane_of_singular K s P hd hs
  · rintro ⟨g, rfl⟩
    exact ⟨conjugateRootPlane_finrank K s g, conjugateRootPlane_singular K s g⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPlaneOrbit
