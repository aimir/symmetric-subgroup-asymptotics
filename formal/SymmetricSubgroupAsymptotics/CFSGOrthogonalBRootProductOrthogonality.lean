import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootProductDisplacements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPairOperator
import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOrthogonality

/-! An intrinsic commuting/long-root-product test implies orthogonality
of the SAME original natural long-root planes. This is one incidence
constraint; it does not claim the full polar adjacency converse or
reconstruct points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGAlternatingPairOperator
variable {K : Type} [Field K] [Finite K]

theorem gram_pairing_symmetric (n : ℕ) (u v : Index n → K) :
    (gram K n).toBilin' u v = (gram K n).toBilin' v u := by
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hgram : gram K n i j = gram K n j i := by
    rcases i with (i | i) | ⟨⟩ <;> rcases j with (j | j) | ⟨⟩ <;>
      simp [gram, eq_comm]
  rw [hgram]
  ring

theorem longRoot_displacement_skew (h2 : (2 : K) ≠ 0) (s : ℕ)
    (x : elementaryRootGroup K (s + 3)) (hx : IsLongRootElement s x)
    (u v : Index (s + 3) → K) :
    (gram K (s + 3)).toBilin' ((((x.val : Mat K (s + 3)) - 1) *ᵥ u)) v =
      -(gram K (s + 3)).toBilin' u ((((x.val : Mat K (s + 3)) - 1) *ᵥ v)) := by
  obtain ⟨g, a, rfl⟩ := hx
  have he := conjugate_highestRoot_displacement_pairOperator h2 s g a
  change (gram K (s + 3)).toBilin'
      (Matrix.mulVecLin (((g * highestRoot s a * g⁻¹).val : Mat K (s + 3)) - 1) u) v =
    -(gram K (s + 3)).toBilin' u
      (Matrix.mulVecLin (((g * highestRoot s a * g⁻¹).val : Mat K (s + 3)) - 1) v)
  rw [he]
  simp only [LinearMap.smul_apply, map_smul]
  rw [pairOperator_skew (gram K (s + 3)).toBilin' (gram_pairing_symmetric (s + 3))]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_neg]

theorem root_product_planes_orthogonal (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : Commute (g * highestRoot s a * g⁻¹) (h * highestRoot s b * h⁻¹))
    (hp : IsLongRootElement s ((g * highestRoot s a * g⁻¹) * (h * highestRoot s b * h⁻¹)))
    (u : Index (s + 3) → K) (hu : u ∈ conjugateRootPlane (K := K) s g)
    (v : Index (s + 3) → K) (hv : v ∈ conjugateRootPlane (K := K) s h) :
    (gram K (s + 3)).toBilin' u v = 0 := by
  let x := g * highestRoot s a * g⁻¹
  let y := h * highestRoot s b * h⁻¹
  let A := Matrix.mulVecLin ((x.val : Mat K (s + 3)) - 1)
  let C := Matrix.mulVecLin ((y.val : Mat K (s + 3)) - 1)
  have hxy := commuting_longRoot_product_mixed_zero h2 s x y ⟨g, a, rfl⟩ ⟨h, b, rfl⟩ hc hp
  have hz : A.comp C = 0 := by
    change (Matrix.mulVecLin ((x.val : Mat K (s + 3)) - 1)).comp
      (Matrix.mulVecLin ((y.val : Mat K (s + 3)) - 1)) = 0
    rw [← Matrix.mulVecLin_mul, hxy]
    exact LinearMap.ext (by intro z; simp)
  rw [← conjugate_highestRoot_displacement_range h2 s g a ha] at hu
  rw [← conjugate_highestRoot_displacement_range h2 s h b hb] at hv
  exact mixed_zero_orthogonal_ranges (gram K (s + 3)).toBilin' A C
    (longRoot_displacement_skew h2 s x ⟨g, a, rfl⟩) hz u hu v hv

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
