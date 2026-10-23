import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllPairSwap
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotent

/-! All-pairs exchange converts transpose-upper matrices into upper
matrices for the SAME positive/reverse-negative coordinate order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSwapTriangular
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDAllPairSwap CFSGOrthogonalDIndexUnipotent
variable (K : Type) [Field K]

theorem pairSwap_conjugation (r : ℕ) (M : Mat K r) :
    (pairSwap K r : Mat K r) * M * (pairSwap K r : Mat K r) =
      Matrix.fromBlocks M.toBlocks₂₂ M.toBlocks₂₁ M.toBlocks₁₂ M.toBlocks₁₁ := by
  calc
    _ = (pairSwap K r : Mat K r) *
        Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ *
        (pairSwap K r : Mat K r) := by rw [Matrix.fromBlocks_toBlocks]
    _ = _ := by
      change Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 1 0 *
        Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ *
        Matrix.fromBlocks 0 1 1 0 = _
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp only [Matrix.zero_mul, Matrix.mul_zero, one_mul, mul_one, zero_add, add_zero]

theorem pairSwap_conjugation_entry (r : ℕ) (M : Mat K r) (x y : Index r) :
    ((pairSwap K r : Mat K r) * M * (pairSwap K r : Mat K r)) x y =
      M (Sum.swap x) (Sum.swap y) := by
  rw [pairSwap_conjugation]
  cases x <;> cases y <;> rfl

theorem flag_swap_reverses (r : ℕ) (x y : Index r) (h : flagEquiv r y < flagEquiv r x) :
    flagEquiv r (Sum.swap x) < flagEquiv r (Sum.swap y) := by
  rcases x with i | i <;> rcases y with j | j
  · change r + (Fin.rev i).val < r + (Fin.rev j).val
    change j.val < i.val at h
    simp only [Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    omega
  · exact False.elim ((not_lt_of_gt (flag_pos_lt_neg r i j)) h)
  · exact flag_pos_lt_neg r i j
  · change i.val < j.val
    change r + (Fin.rev j).val < r + (Fin.rev i).val at h
    simp only [Fin.val_rev] at h
    have hi := i.isLt
    have hj := j.isLt
    omega

theorem pairSwap_conjugate_triangular (r : ℕ) (M : Mat K r)
    (hM : M.transpose.BlockTriangular (flagEquiv r)) :
    ((pairSwap K r : Mat K r) * M * (pairSwap K r : Mat K r)).BlockTriangular (flagEquiv r) := by
  intro x y hxy
  rw [pairSwap_conjugation_entry]
  exact hM (flag_swap_reverses r x y hxy)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSwapTriangular
