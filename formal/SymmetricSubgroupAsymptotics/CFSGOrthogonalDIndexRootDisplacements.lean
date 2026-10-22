import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOperatorProduct
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularRootPlanes

/-! Displacements of actual original D root elements have rank at most
two and are skew for the SAME nondegenerate polar form. Both statements
include characteristic two and refer to literal original conjugates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexRootPlaneImage CFSGOrthogonalDIndexSingularRootPlanes
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexOperatorProduct
variable {K : Type} [Field K]

def IsRootElement (s : ℕ) (x : elementaryRootGroup K (s + 4)) : Prop :=
  ∃ g : elementaryRootGroup K (s + 4), ∃ a : K, x = g * highestRoot K s a * g⁻¹

theorem root_displacement_finrank_le_two (s : ℕ)
    (x : elementaryRootGroup K (s + 4)) (hx : IsRootElement s x) :
    Module.finrank K (LinearMap.range (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1))) ≤ 2 := by
  obtain ⟨g, a, rfl⟩ := hx
  by_cases ha : a = 0
  · have he : g * highestRoot K s a * g⁻¹ = 1 := by
      rw [ha, highestRoot_zero K s, mul_one, mul_inv_cancel]
    rw [he]
    change Module.finrank K (LinearMap.range (Matrix.mulVecLin ((1 : Mat K (s + 4)) - 1))) ≤ 2
    have hM : Matrix.mulVecLin ((1 : Mat K (s + 4)) - 1) = 0 :=
      (congrArg (fun M : Mat K (s + 4) => Matrix.mulVecLin M) (sub_self (1 : Mat K (s + 4)))).trans
        Matrix.mulVecLin_zero
    have hR : LinearMap.range (Matrix.mulVecLin ((1 : Mat K (s + 4)) - 1)) =
        (⊥ : Submodule K (Index (s + 4) → K)) :=
      (congrArg LinearMap.range hM).trans LinearMap.range_zero
    have hd : Module.finrank K (LinearMap.range (Matrix.mulVecLin ((1 : Mat K (s + 4)) - 1))) = 0 :=
      (congrArg (fun P : Submodule K (Index (s + 4) → K) => Module.finrank K P) hR).trans
        (finrank_bot K (Index (s + 4) → K))
    exact hd.le.trans (Nat.zero_le 2)
  · rw [conjugate_highestRoot_displacement_range K s g a ha, conjugateRootPlane_finrank]

theorem root_displacement_skew (s : ℕ) (x : elementaryRootGroup K (s + 4))
    (hx : IsRootElement s x) (v w : Index (s + 4) → K) :
    (splitQuadraticForm K (s + 4)).polarBilin
        (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1) v) w =
      -(splitQuadraticForm K (s + 4)).polarBilin v
        (Matrix.mulVecLin ((x.val : Mat K (s + 4)) - 1) w) := by
  obtain ⟨g, a, rfl⟩ := hx
  rw [conjugate_highestRoot_displacement_pairOperator]
  apply smul_pairOperator_skew
  intro v w
  exact QuadraticMap.polar_comm (splitQuadraticForm K (s + 4) : (Index (s + 4) → K) → K) v w

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
