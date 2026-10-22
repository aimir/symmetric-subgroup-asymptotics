import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements

/-! Commuting nontrivial original D root elements whose product is an
original root have intersecting original root planes. The mixed product
is killed only in the disjoint-image contradiction branch. Consequently
the proof is valid in characteristic two without cancelling two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexSingularRootPlanes CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexOperatorProduct CFSGSkewOrthogonalKernels
variable {K : Type} [Field K]

theorem root_product_planes_inf_ne_bot (s : ℕ)
    (g h : elementaryRootGroup K (s + 4)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : Commute (g * highestRoot K s a * g⁻¹) (h * highestRoot K s b * h⁻¹))
    (hp : IsRootElement s ((g * highestRoot K s a * g⁻¹) * (h * highestRoot K s b * h⁻¹))) :
    conjugateRootPlane K s g ⊓ conjugateRootPlane K s h ≠ ⊥ := by
  intro hinf
  let x := g * highestRoot K s a * g⁻¹
  let y := h * highestRoot K s b * h⁻¹
  let A := Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1)
  let C := Matrix.mulVecLin ((y.val : Mat K (s + 4)) - 1)
  have hrA : LinearMap.range A = conjugateRootPlane K s g :=
    conjugate_highestRoot_displacement_range K s g a ha
  have hrC : LinearMap.range C = conjugateRootPlane K s h :=
    conjugate_highestRoot_displacement_range K s h b hb
  have hd : Disjoint (LinearMap.range A) (LinearMap.range C) := by
    rw [hrA, hrC]
    exact disjoint_iff_inf_le.mpr hinf.le
  have hmat : (x.val : Mat K (s + 4)) * (y.val : Mat K (s + 4)) =
      (y.val : Mat K (s + 4)) * (x.val : Mat K (s + 4)) :=
    congrArg (fun z : elementaryRootGroup K (s + 4) => (z.val : Mat K (s + 4))) hc.eq
  have hAC : A.comp C = C.comp A := by
    change (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1)).comp
        (Matrix.mulVecLin ((y.val : Mat K (s + 4)) - 1)) =
      (Matrix.mulVecLin ((y.val : Mat K (s + 4)) - 1)).comp
        (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1))
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    congr 1
    calc
      ((x.val : Mat K (s + 4)) - 1) * ((y.val : Mat K (s + 4)) - 1) =
          (x.val : Mat K (s + 4)) * (y.val : Mat K (s + 4)) - x.val - y.val + 1 := by
        noncomm_ring
      _ = (y.val : Mat K (s + 4)) * (x.val : Mat K (s + 4)) - x.val - y.val + 1 := by
        rw [hmat]
      _ = ((y.val : Mat K (s + 4)) - 1) * ((x.val : Mat K (s + 4)) - 1) := by
        noncomm_ring
  have hz : A.comp C = 0 := commuting_disjoint_ranges_comp_zero A C hAC hd
  have hsum : A + C = Matrix.mulVecLin (((x * y).val : Mat K (s + 4)) - 1) := by
    have hm : (((x * y).val : Mat K (s + 4)) - 1) =
        ((x.val : Mat K (s + 4)) - 1) + ((y.val : Mat K (s + 4)) - 1) +
          ((x.val : Mat K (s + 4)) - 1) * ((y.val : Mat K (s + 4)) - 1) := by
      change (x.val : Mat K (s + 4)) * (y.val : Mat K (s + 4)) - 1 = _
      noncomm_ring
    symm
    rw [hm, Matrix.mulVecLin_add, Matrix.mulVecLin_add, Matrix.mulVecLin_mul]
    change A + C + A.comp C = A + C
    rw [hz, add_zero]
  have hdim := disjoint_skew_ranges_rank_add (splitQuadraticForm K (s + 4)).polarBilin
    (splitQuadraticForm_nondegenerate K (s + 4))
    (fun v w => QuadraticMap.polar_comm
      (splitQuadraticForm K (s + 4) : (Index (s + 4) → K) → K) v w) A C
    (root_displacement_skew s x ⟨g, a, rfl⟩)
    (root_displacement_skew s y ⟨h, b, rfl⟩) hd
  rw [hrA, hrC, conjugateRootPlane_finrank, conjugateRootPlane_finrank] at hdim
  have hsmall := root_displacement_finrank_le_two s (x * y) hp
  rw [← hsum] at hsmall
  omega

theorem root_product_distinct_planes_intersect_in_point (s : ℕ)
    (g h : elementaryRootGroup K (s + 4)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : Commute (g * highestRoot K s a * g⁻¹) (h * highestRoot K s b * h⁻¹))
    (hp : IsRootElement s ((g * highestRoot K s a * g⁻¹) * (h * highestRoot K s b * h⁻¹)))
    (hne : conjugateRootPlane K s g ≠ conjugateRootPlane K s h) :
    Module.finrank K ↥(conjugateRootPlane K s g ⊓ conjugateRootPlane K s h) = 1 := by
  let P := conjugateRootPlane K s g
  let Q := conjugateRootPlane K s h
  let W : Submodule K (Index (s + 4) → K) := P ⊓ Q
  have hP : Module.finrank K P = 2 := conjugateRootPlane_finrank K s g
  have hQ : Module.finrank K Q = 2 := conjugateRootPlane_finrank K s h
  have hbot : W ≠ ⊥ := root_product_planes_inf_ne_bot s g h a b ha hb hc hp
  have hbound : Module.finrank K W ≤ 2 :=
    (Submodule.finrank_mono (show W ≤ P from inf_le_left)).trans_eq hP
  have hz : Module.finrank K W ≠ 0 := fun hz => hbot (Submodule.finrank_eq_zero.mp hz)
  have ht : Module.finrank K W ≠ 2 := by
    intro ht
    have he : W = P := Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hP, ht])
    have hPQ : P ≤ Q := he.ge.trans (show W ≤ Q from inf_le_right)
    exact hne (Submodule.eq_of_le_of_finrank_le hPQ (by rw [hQ, hP]))
  change Module.finrank K W = 1
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
