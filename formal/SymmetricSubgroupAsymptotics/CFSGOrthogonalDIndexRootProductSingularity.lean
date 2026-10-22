import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProductQuadratic

/-! Every actual root displacement has Q-singular image. In a shared-
axis presentation, actual root-product membership therefore forces the
remaining two vectors to be polar-orthogonal, including characteristic
two. The hypotheses retain the exact original displacement operators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexRootPlaneImage CFSGOrthogonalDIndexSingularRootPlanes
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPairProductQuadratic
open CFSGAlternatingPairOperator
variable {K : Type} [Field K]

private theorem mulVecLin_sub {r : ℕ} (A C : Mat K r) :
    Matrix.mulVecLin (A - C) = Matrix.mulVecLin A - Matrix.mulVecLin C :=
  LinearMap.ext (fun v => Matrix.sub_mulVec A C v)

theorem root_displacement_singular (s : ℕ) (x : elementaryRootGroup K (s + 4))
    (hx : IsRootElement s x) (v : Index (s + 4) → K) :
    splitQuadraticForm K (s + 4) (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1) v) = 0 := by
  obtain ⟨g, a, rfl⟩ := hx
  by_cases ha : a = 0
  · have he : g * highestRoot K s a * g⁻¹ = 1 := by
      rw [ha, highestRoot_zero K s, mul_one, mul_inv_cancel]
    rw [he]
    change splitQuadraticForm K (s + 4) (Matrix.mulVecLin ((1 : Mat K (s + 4)) - 1) v) = 0
    rw [sub_self, Matrix.mulVecLin_zero, LinearMap.zero_apply, QuadraticMap.map_zero]
  · apply conjugateRootPlane_singular K s g
    rw [← conjugate_highestRoot_displacement_range K s g a ha]
    exact ⟨v, rfl⟩

theorem shared_axis_root_product_forces_orthogonal (s : ℕ)
    (x y : elementaryRootGroup K (s + 4))
    (u v w z : Index (s + 4) → K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : splitQuadraticForm K (s + 4) u = 0)
    (hv : splitQuadraticForm K (s + 4) v = 0)
    (hw : splitQuadraticForm K (s + 4) w = 0)
    (huv : (splitQuadraticForm K (s + 4)).polarBilin u v = 0)
    (huw : (splitQuadraticForm K (s + 4)).polarBilin u w = 0)
    (hz : (splitQuadraticForm K (s + 4)).polarBilin u z ≠ 0)
    (hX : Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1) =
      a • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v)
    (hY : Matrix.mulVecLin ((y.val : Mat K (s + 4)) - 1) =
      b • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u w)
    (hp : IsRootElement s (x * y)) :
    (splitQuadraticForm K (s + 4)).polarBilin v w = 0 := by
  have hX' : Matrix.mulVecLin (x.val : Mat K (s + 4)) =
      (LinearMap.id : (Index (s + 4) → K) →ₗ[K] (Index (s + 4) → K)) +
        a • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v := by
    rw [mulVecLin_sub, Matrix.mulVecLin_one] at hX
    exact (sub_eq_iff_eq_add.mp hX).trans (add_comm _ _)
  have hY' : Matrix.mulVecLin (y.val : Mat K (s + 4)) =
      (LinearMap.id : (Index (s + 4) → K) →ₗ[K] (Index (s + 4) → K)) +
        b • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u w := by
    rw [mulVecLin_sub, Matrix.mulVecLin_one] at hY
    exact (sub_eq_iff_eq_add.mp hY).trans (add_comm _ _)
  have hd : Matrix.mulVecLin (((x * y).val : Mat K (s + 4)) - 1) =
      ((LinearMap.id : (Index (s + 4) → K) →ₗ[K] (Index (s + 4) → K)) +
        a • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v).comp
        ((LinearMap.id : (Index (s + 4) → K) →ₗ[K] (Index (s + 4) → K)) +
          b • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u w) -
        (LinearMap.id : (Index (s + 4) → K) →ₗ[K] (Index (s + 4) → K)) := by
    change Matrix.mulVecLin ((x.val : Mat K (s + 4)) * (y.val : Mat K (s + 4)) - 1) = _
    rw [mulVecLin_sub, Matrix.mulVecLin_one, Matrix.mulVecLin_mul, hX', hY']
  apply shared_product_singular_forces_orthogonal (splitQuadraticForm K (s + 4))
    u v w hu hv hw huv huw a b ha hb z hz
  rw [← hd]
  exact root_displacement_singular s (x * y) hp z

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
