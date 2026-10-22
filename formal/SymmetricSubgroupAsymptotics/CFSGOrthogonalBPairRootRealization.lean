import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPairOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPairOperator
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicRootLines
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalSubmoduleBasis
import Mathlib.LinearAlgebra.Span.Basic

/-! Every independent totally singular ordered pair realizes its literal
bilinear skew operator as an actual original B long-root displacement.
The realizing element is an explicit conjugate using the checked actual
pair frame, not an abstract classical-group recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBVectorCoordinates
open CFSGAlternatingPairOperator
variable {K : Type} [Field K] [Finite K]

theorem exists_longRoot_with_pairOperator (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v w : Index (s + 3) → K) (hv : v ≠ 0)
    (hsv : (gram K (s + 3)).toBilin' v v = 0)
    (hsw : (gram K (s + 3)).toBilin' w w = 0)
    (hvw : (gram K (s + 3)).toBilin' v w = 0)
    (hnot : ∀ c : K, w ≠ c • v) (t : K) :
    ∃ x : elementaryRootGroup K (s + 3), IsLongRootElement s x ∧
      Matrix.mulVecLin ((x.val : Mat K (s + 3)) - 1) =
        t • pairOperator (gram K (s + 3)).toBilin' v w ∧ (t ≠ 0 → x ≠ 1) ∧
        (t ≠ 0 → LinearMap.range (Matrix.mulVecLin ((x.val : Mat K (s + 3)) - 1)) =
          Submodule.span K {v, w}) := by
  obtain ⟨g, c, hgv, hgw⟩ := exists_singular_pair_frame K h2 s v w hv hsv hsw hvw hnot
  have h0 : (↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ positiveVector (K := K) s 0 = v := by
    have he := congrArg (fun z : Index (s + 3) → K => (↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ z) hgv
    dsimp only at he
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at he
    exact he.symm
  have h1 : (↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ
      positiveVector (K := K) s (secondIndex s) = w - c • v := by
    have hn : (g.val : Mat K (s + 3)) *ᵥ (w - c • v) =
        positiveVector (K := K) s (secondIndex s) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hgw, hgv]
      change c • positiveVector (K := K) s 0 + positiveVector (K := K) s (secondIndex s) -
        c • positiveVector (K := K) s 0 = _
      abel
    have he := congrArg (fun z : Index (s + 3) → K => (↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ z) hn
    dsimp only at he
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at he
    exact he.symm
  have hshear : pairOperator (gram K (s + 3)).toBilin' v (w - c • v) =
      pairOperator (gram K (s + 3)).toBilin' v w := by
    simpa [sub_eq_add_neg, neg_smul, add_comm] using
      pairOperator_basisChange (gram K (s + 3)).toBilin' v w 1 0 (-c) 1
  have hmap : (Submodule.span K {v, w}).map (Matrix.mulVecLin (g.val : Mat K (s + 3))) =
      standardRootPlane (K := K) s := by
    rw [Submodule.map_span, Set.image_pair]
    change Submodule.span K {(g.val : Mat K (s + 3)) *ᵥ v,
      (g.val : Mat K (s + 3)) *ᵥ w} = _
    rw [hgv, hgw]
    exact CFSGTwoDimensionalSubmoduleBasis.span_pair_shear
      (positiveVector (K := K) s 0) (positiveVector (K := K) s (secondIndex s)) c
  have hplane : conjugateRootPlane (K := K) s g⁻¹ = Submodule.span K {v, w} := by
    change (standardRootPlane (K := K) s).map
      (Matrix.mulVecLin (↑(g.val⁻¹) : Mat K (s + 3))) = _
    rw [← hmap, ← Submodule.map_comp, ← Matrix.mulVecLin_mul,
      Units.inv_mul, Matrix.mulVecLin_one, Submodule.map_id]
  let x := g⁻¹ * highestRoot s (2 * t) * g
  refine ⟨x, ⟨g⁻¹, 2 * t, by simp only [inv_inv]; rfl⟩, ?_, ?_, ?_⟩
  · have he := conjugate_highestRoot_displacement_pairOperator h2 s g⁻¹ (2 * t)
    simp only [inv_inv, Subgroup.coe_inv] at he
    have hscale : (2 * t) / 2 = t := by field_simp
    rw [h0, h1, hshear, hscale] at he
    exact he
  · intro ht hx
    have hroot : highestRoot (K := K) s (2 * t) ≠ 1 := by
      intro he
      have hz : 2 * t = 0 := highestRoot_injective h2 s (he.trans (highestRoot_zero h2 s).symm)
      exact mul_ne_zero h2 ht hz
    apply hroot
    apply (MulAut.conj g⁻¹).injective
    simpa only [MulAut.conj_apply, inv_inv, mul_one, inv_mul_cancel] using hx
  · intro ht
    have he := conjugate_highestRoot_displacement_range h2 s g⁻¹ (2 * t) (mul_ne_zero h2 ht)
    simpa only [inv_inv] using he.trans hplane

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
