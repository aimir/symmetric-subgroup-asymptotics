import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentRoots
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentCenterMatrices

/-! Every actual central element of U is a symmetric upper shear.
The proof tests against the original coordinate long-root words. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGMatrixShearUnits
variable {K : Type} [Field K]

def diagonalLongInU (r : ℕ) (hr : 0 < r) (i : Fin (r + 1)) : unipotent K (r + 1) :=
  upperShearInU K r hr (Matrix.diagonal (Pi.single i 1)) (Matrix.isSymm_diagonal _)

theorem diagonalLongInU_val (r : ℕ) (hr : 0 < r) (i : Fin (r + 1)) :
    ((diagonalLongInU (K := K) r hr i).val.val : Mat K (r + 1)) =
      1 + Matrix.single (Sum.inl i) (Sum.inr i) 1 := by
  change Matrix.fromBlocks 1 (Matrix.diagonal (Pi.single i 1)) 0 1 = _
  rw [Matrix.diagonal_single]
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply]

theorem central_unipotent_is_symmetric_shear (r : ℕ) (hr : 0 < r)
    (z : unipotent K (r + 1)) (hz : z ∈ Subgroup.center (unipotent K (r + 1))) :
    ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      B.IsSymm ∧ (z.val.val : Mat K (r + 1)) = Matrix.fromBlocks 1 B 0 1 := by
  have hcomm (i : Fin (r + 1)) :
      (z.val.val : Mat K (r + 1)) * Matrix.single (Sum.inl i) (Sum.inr i) 1 =
        Matrix.single (Sum.inl i) (Sum.inr i) 1 * (z.val.val : Mat K (r + 1)) := by
    have h := congrArg (fun u : unipotent K (r + 1) => (u.val.val : Mat K (r + 1)))
      (Subgroup.mem_center_iff.mp hz (diagonalLongInU (K := K) r hr i)).symm
    change (z.val.val : Mat K (r + 1)) *
        ((diagonalLongInU (K := K) r hr i).val.val : Mat K (r + 1)) =
      ((diagonalLongInU (K := K) r hr i).val.val : Mat K (r + 1)) * (z.val.val : Mat K (r + 1)) at h
    rw [diagonalLongInU_val] at h
    simp only [mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  have hupper := upper_of_diagonal_long_commutation (r + 1) (z.val.val : Mat K (r + 1))
    (unipotent_lower_left_zero K (r + 1) z) z.property.2 hcomm
  let B := (z.val.val : Mat K (r + 1)).submatrix Sum.inl Sum.inr
  refine ⟨B, ?_, hupper⟩
  have hform := elementaryRootGroup_le_formPreserving K (r + 1) z.val.property
  change (z.val.val : Mat K (r + 1)) * Matrix.J (Fin (r + 1)) K *
    (z.val.val : Mat K (r + 1)).transpose = Matrix.J (Fin (r + 1)) K at hform
  rw [hupper] at hform
  exact upperShear_symmetric_of_form (r + 1) B hform

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
