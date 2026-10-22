import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGramNondegenerate
import SymmetricSubgroupAsymptotics.CFSGSkewDisjointRangeRank
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneLabels

/-! The intrinsic commuting/long-root-product test forces a nonzero
intersection of the SAME original root planes. The proof uses actual
displacement ranks and nondegeneracy, not a polar adjacency assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGSkewOrthogonalKernels
variable {K : Type} [Field K] [Finite K]

theorem longRoot_displacement_finrank_le_two (h2 : (2 : K) ≠ 0) (s : ℕ)
    (x : elementaryRootGroup K (s + 3)) (hx : IsLongRootElement s x) :
    Module.finrank K (LinearMap.range (Matrix.mulVecLin ((x.val : Mat K (s + 3)) - 1))) ≤ 2 := by
  obtain ⟨g, a, rfl⟩ := hx
  by_cases ha : a = 0
  · have he : g * highestRoot (K := K) s a * g⁻¹ = 1 := by
      rw [ha, highestRoot_zero h2 s, mul_one, mul_inv_cancel]
    rw [he]
    change Module.finrank K (LinearMap.range (Matrix.mulVecLin ((1 : Mat K (s + 3)) - 1))) ≤ 2
    have hM : Matrix.mulVecLin ((1 : Mat K (s + 3)) - 1) = 0 :=
      (congrArg (fun M : Mat K (s + 3) => Matrix.mulVecLin M) (sub_self (1 : Mat K (s + 3)))).trans
        Matrix.mulVecLin_zero
    have hR : LinearMap.range (Matrix.mulVecLin ((1 : Mat K (s + 3)) - 1)) =
        (⊥ : Submodule K (Index (s + 3) → K)) :=
      (congrArg LinearMap.range hM).trans LinearMap.range_zero
    have hd : Module.finrank K (LinearMap.range (Matrix.mulVecLin ((1 : Mat K (s + 3)) - 1))) = 0 :=
      (congrArg (fun P : Submodule K (Index (s + 3) → K) => Module.finrank K P) hR).trans
        (finrank_bot K (Index (s + 3) → K))
    exact hd.le.trans (Nat.zero_le 2)
  · rw [conjugate_highestRoot_displacement_range h2 s g a ha, conjugateRootPlane_finrank]

theorem root_product_planes_inf_ne_bot (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : Commute (g * highestRoot s a * g⁻¹) (h * highestRoot s b * h⁻¹))
    (hp : IsLongRootElement s ((g * highestRoot s a * g⁻¹) * (h * highestRoot s b * h⁻¹))) :
    conjugateRootPlane (K := K) s g ⊓ conjugateRootPlane (K := K) s h ≠ ⊥ := by
  intro hinf
  let x := g * highestRoot s a * g⁻¹
  let y := h * highestRoot s b * h⁻¹
  let A := Matrix.mulVecLin ((x.val : Mat K (s + 3)) - 1)
  let C := Matrix.mulVecLin ((y.val : Mat K (s + 3)) - 1)
  have hxy := commuting_longRoot_product_mixed_zero h2 s x y ⟨g, a, rfl⟩ ⟨h, b, rfl⟩ hc hp
  have hsum : A + C = Matrix.mulVecLin (((x * y).val : Mat K (s + 3)) - 1) := by
    have hm : (((x * y).val : Mat K (s + 3)) - 1) =
        ((x.val : Mat K (s + 3)) - 1) + ((y.val : Mat K (s + 3)) - 1) := by
      calc
        (((x * y).val : Mat K (s + 3)) - 1) =
            ((x.val : Mat K (s + 3)) - 1) + ((y.val : Mat K (s + 3)) - 1) +
              ((x.val : Mat K (s + 3)) - 1) * ((y.val : Mat K (s + 3)) - 1) := by
          change (x.val : Mat K (s + 3)) * (y.val : Mat K (s + 3)) - 1 = _
          noncomm_ring
        _ = _ := by rw [hxy, add_zero]
    rw [hm, Matrix.mulVecLin_add]
  have hrA : LinearMap.range A = conjugateRootPlane (K := K) s g :=
    conjugate_highestRoot_displacement_range h2 s g a ha
  have hrC : LinearMap.range C = conjugateRootPlane (K := K) s h :=
    conjugate_highestRoot_displacement_range h2 s h b hb
  have hd : Disjoint (LinearMap.range A) (LinearMap.range C) := by
    rw [hrA, hrC]
    exact disjoint_iff_inf_le.mpr hinf.le
  have hdim := disjoint_skew_ranges_rank_add (gram K (s + 3)).toBilin'
    (gram_nondegenerate h2 (s + 3)) (gram_pairing_symmetric (s + 3)) A C
    (longRoot_displacement_skew h2 s x ⟨g, a, rfl⟩)
    (longRoot_displacement_skew h2 s y ⟨h, b, rfl⟩) hd
  rw [hrA, hrC, conjugateRootPlane_finrank, conjugateRootPlane_finrank] at hdim
  have hsmall := longRoot_displacement_finrank_le_two h2 s (x * y) hp
  rw [← hsum] at hsmall
  omega

theorem root_product_distinct_planes_intersect_in_point (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : Commute (g * highestRoot s a * g⁻¹) (h * highestRoot s b * h⁻¹))
    (hp : IsLongRootElement s ((g * highestRoot s a * g⁻¹) * (h * highestRoot s b * h⁻¹)))
    (hne : conjugateRootPlane (K := K) s g ≠ conjugateRootPlane (K := K) s h) :
    Module.finrank K (conjugateRootPlane (K := K) s g ⊓ conjugateRootPlane (K := K) s h :
      Submodule K (Index (s + 3) → K)) = 1 := by
  let P : Submodule K (Index (s + 3) → K) := conjugateRootPlane (K := K) s g
  let Q : Submodule K (Index (s + 3) → K) := conjugateRootPlane (K := K) s h
  let W : Submodule K (Index (s + 3) → K) := P ⊓ Q
  have hP : Module.finrank K P = 2 := conjugateRootPlane_finrank s g
  have hQ : Module.finrank K Q = 2 := conjugateRootPlane_finrank s h
  have hbot : W ≠ ⊥ := root_product_planes_inf_ne_bot h2 s g h a b ha hb hc hp
  have hbound : Module.finrank K W ≤ 2 :=
    (Submodule.finrank_mono (show W ≤ P from inf_le_left)).trans_eq hP
  have hz : Module.finrank K W ≠ 0 := fun hz =>
    hbot (Submodule.finrank_eq_zero.mp hz)
  have ht : Module.finrank K W ≠ 2 := by
    intro ht
    have he : W = P := Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hP, ht])
    have hPQ : P ≤ Q := he.ge.trans (show W ≤ Q from inf_le_right)
    exact hne (Submodule.eq_of_le_of_finrank_le hPQ (by rw [hQ, hP]))
  change Module.finrank K W = 1
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
