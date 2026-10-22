import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPairOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalSubmoduleBasis
import Mathlib.LinearAlgebra.Span.Basic

/-! Every independent totally singular ordered pair realizes its literal
bilinear skew operator as an actual original D root displacement.
The realizing element is an explicit conjugate using the checked actual
pair frame, not an abstract classical-group recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDIndexPairOperator CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexSingularRootPlanes CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexBundledQuadratic
open CFSGAlternatingPairOperator
variable {K : Type} [Field K]

theorem exists_root_with_pairOperator (s : ℕ)
    (v w : Index (s + 4) → K) (hv : v ≠ 0)
    (hsv : splitQ K v = 0)
    (hsw : splitQ K w = 0)
    (hvw : polar K v w = 0)
    (hnot : ∀ c : K, w ≠ c • v) (t : K) :
    ∃ x : elementaryRootGroup K (s + 4), IsRootElement s x ∧
      Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1) =
        t • pairOperator (splitQuadraticForm K (s + 4)).polarBilin v w ∧ (t ≠ 0 → x ≠ 1) ∧
        (t ≠ 0 → LinearMap.range (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1)) =
          Submodule.span K {v, w}) := by
  obtain ⟨g, c, hgv, hgw⟩ := exists_singular_pair_frame K s v w hv hsv hsw hvw hnot
  have h0 : (↑(g.val⁻¹) : Mat K (s + 4)) *ᵥ firstVector K s = v := by
    have he := congrArg (fun z : Index (s + 4) → K => (↑(g.val⁻¹) : Mat K (s + 4)) *ᵥ z) hgv
    dsimp only at he
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at he
    exact he.symm
  have h1 : (↑(g.val⁻¹) : Mat K (s + 4)) *ᵥ
      secondVector K s = w - c • v := by
    have hn : (g.val : Mat K (s + 4)) *ᵥ (w - c • v) =
        secondVector K s := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hgw, hgv]
      change c • firstVector K s + secondVector K s -
        c • firstVector K s = _
      abel
    have he := congrArg (fun z : Index (s + 4) → K => (↑(g.val⁻¹) : Mat K (s + 4)) *ᵥ z) hn
    dsimp only at he
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at he
    exact he.symm
  have hshear : pairOperator (splitQuadraticForm K (s + 4)).polarBilin v (w - c • v) =
      pairOperator (splitQuadraticForm K (s + 4)).polarBilin v w := by
    simpa [sub_eq_add_neg, neg_smul, add_comm] using
      pairOperator_basisChange (splitQuadraticForm K (s + 4)).polarBilin v w 1 0 (-c) 1
  have hmap : (Submodule.span K {v, w}).map (Matrix.mulVecLin (g.val : Mat K (s + 4))) =
      standardRootPlane K s := by
    rw [Submodule.map_span, Set.image_pair]
    change Submodule.span K {(g.val : Mat K (s + 4)) *ᵥ v,
      (g.val : Mat K (s + 4)) *ᵥ w} = _
    rw [hgv, hgw]
    exact CFSGTwoDimensionalSubmoduleBasis.span_pair_shear
      (firstVector K s) (secondVector K s) c
  have hplane : conjugateRootPlane K s g⁻¹ = Submodule.span K {v, w} := by
    rw [conjugateRootPlane_eq_map_standard]
    change (standardRootPlane K s).map
      (Matrix.mulVecLin (↑(g.val⁻¹) : Mat K (s + 4))) = _
    rw [← hmap, ← Submodule.map_comp, ← Matrix.mulVecLin_mul,
      Units.inv_mul, Matrix.mulVecLin_one, Submodule.map_id]
  let x := g⁻¹ * highestRoot K s t * g
  refine ⟨x, ⟨g⁻¹, t, by simp only [inv_inv]; rfl⟩, ?_, ?_, ?_⟩
  · have he := conjugate_highestRoot_displacement_pairOperator K s g⁻¹ t
    simp only [inv_inv, Subgroup.coe_inv] at he
    rw [h0, h1, hshear] at he
    exact he
  · intro ht hx
    have hroot : highestRoot K s t ≠ 1 := by
      intro he
      have hz : t = 0 := highestRoot_injective K s (he.trans (highestRoot_zero K s).symm)
      exact ht hz
    apply hroot
    apply (MulAut.conj g⁻¹).injective
    simpa only [MulAut.conj_apply, inv_inv, mul_one, inv_mul_cancel] using hx
  · intro ht
    have he := conjugate_highestRoot_displacement_range K s g⁻¹ t ht
    simpa only [inv_inv] using he.trans hplane

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
