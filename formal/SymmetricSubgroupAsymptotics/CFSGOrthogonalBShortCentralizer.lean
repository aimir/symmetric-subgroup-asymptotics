import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortArrays
import SymmetricSubgroupAsymptotics.CFSGMatrixSingleCentralizer
import Mathlib.Tactic.LinearCombination

/-! In rank at least two the actual positive short-root coefficients
force a unit-diagonal centralizer to be an upper shear. Both the linear
and the quadratic coefficient are essential; no square-zero short-root
substitution is made. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
variable {K : Type} [Field K]

theorem shear_of_short_coefficient_commutation (h2 : (2 : K) ≠ 0) (s : ℕ)
    (A : Mat K (s + 2)) (hd : ∀ x, A x x = 1)
    (hQ : ∀ i : Fin (s + 2), A * Matrix.single (pos (s + 2) i) (neg (s + 2) i) 1 =
      Matrix.single (pos (s + 2) i) (neg (s + 2) i) 1 * A)
    (hL : ∀ i : Fin (s + 2), A * shortArray K (s + 2) (Sum.inl i) =
      shortArray K (s + 2) (Sum.inl i) * A) :
    A = Matrix.fromBlocks
      (Matrix.fromBlocks 1 (A.submatrix (pos (s + 2)) (neg (s + 2))) 0 1) 0 0 1 := by
  have hc (i : Fin (s + 2)) (x : Index (s + 2)) :
      A x (pos (s + 2) i) = if x = pos (s + 2) i then 1 else 0 :=
    CFSGMatrixSingleCentralizer.column_eq_single A _ _ (hQ i) (hd _) x
  have hr (i : Fin (s + 2)) (x : Index (s + 2)) :
      A (neg (s + 2) i) x = if x = neg (s + 2) i then 1 else 0 :=
    CFSGMatrixSingleCentralizer.row_eq_single A _ _ (hQ i) (hd _) x
  have hpm (k : Fin (s + 2)) : A (pos (s + 2) k) (middle (s + 2)) = 0 := by
    obtain ⟨i, hik⟩ := exists_ne k
    have hk : pos (s + 2) k ≠ pos (s + 2) i := by simpa [pos] using Ne.symm hik
    have he := congrArg (fun M : Mat K (s + 2) => M (pos (s + 2) k) (neg (s + 2) i)) (hL i)
    dsimp only at he
    simp only [shortArray, paired, Sum.swap_inl, pos, neg, mul_sub, sub_mul, Matrix.sub_apply] at he
    rw [Matrix.mul_single_apply_of_ne 1 _ _ _ _ (by simp [pos, neg, middle]),
      Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne 1 _ _ _ _ hk,
      Matrix.single_mul_apply_of_ne 2 _ _ _ _ (by simp [pos, middle])] at he
    have hz : A (pos (s + 2) k) (middle (s + 2)) * 2 = 0 := by linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_right h2
  have hmn (k : Fin (s + 2)) : A (middle (s + 2)) (neg (s + 2) k) = 0 := by
    obtain ⟨i, hik⟩ := exists_ne k
    have hk : neg (s + 2) k ≠ neg (s + 2) i := by simpa [neg] using Ne.symm hik
    have he := congrArg (fun M : Mat K (s + 2) => M (pos (s + 2) i) (neg (s + 2) k)) (hL i)
    dsimp only at he
    simp only [shortArray, paired, Sum.swap_inl, pos, neg, mul_sub, sub_mul, Matrix.sub_apply] at he
    rw [Matrix.mul_single_apply_of_ne 1 _ _ _ _ (by simp [neg, middle]),
      Matrix.mul_single_apply_of_ne 2 _ _ _ _ hk, Matrix.single_mul_apply_same,
      Matrix.single_mul_apply_of_ne 2 _ _ _ _ (by simp [pos, middle]), one_mul] at he
    linear_combination -he
  ext x y
  rcases x with (i | i) | ⟨⟩ <;> rcases y with (j | j) | ⟨⟩
  · simpa [pos, Matrix.fromBlocks, Matrix.one_apply, eq_comm] using hc j (pos (s + 2) i)
  · rfl
  · simpa [pos, middle, Matrix.fromBlocks] using hpm i
  · simpa [pos, neg, Matrix.fromBlocks] using hr i (pos (s + 2) j)
  · simpa [neg, Matrix.fromBlocks, Matrix.one_apply, eq_comm] using hr i (neg (s + 2) j)
  · simpa [neg, middle, Matrix.fromBlocks] using hr i (middle (s + 2))
  · simpa [pos, middle, Matrix.fromBlocks] using hc j (middle (s + 2))
  · simpa [neg, middle, Matrix.fromBlocks] using hmn j
  · simpa [middle, Matrix.fromBlocks] using hd (middle (s + 2))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
