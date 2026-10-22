import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRationalForm
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.LinearCombination

/-! The actual odd-B Gram form forces an upper shear to be alternating.
All coordinates include the unchanged middle axis. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

def upperShearMatrix (n : ℕ) (B : Matrix (Fin n) (Fin n) K) : Mat K n :=
  Matrix.fromBlocks (Matrix.fromBlocks 1 B 0 1) 0 0 1

theorem gram_blocks (n : ℕ) : gram K n =
    Matrix.fromBlocks (Matrix.fromBlocks 0 ((2 : K) • 1) ((2 : K) • 1) 0) 0 0 1 := by
  ext x y
  rcases x with (i | i) | ⟨⟩ <;> rcases y with (j | j) | ⟨⟩ <;>
    simp [gram, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem upperShear_alternating_of_form (h2 : (2 : K) ≠ 0) (n : ℕ)
    (B : Matrix (Fin n) (Fin n) K)
    (h : (upperShearMatrix n B).transpose * gram K n * upperShearMatrix n B = gram K n) :
    B.transpose = -B ∧ ∀ i, B i i = 0 := by
  have he := congrArg (fun M : Mat K n => M.toBlocks₁₁.toBlocks₂₂) h
  simp only [upperShearMatrix, gram_blocks, Matrix.fromBlocks_transpose,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂,
    one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at he
  simp [Matrix.fromBlocks_multiply] at he
  have hb : B.transpose + B = 0 := by
    apply (smul_right_injective (Matrix (Fin n) (Fin n) K) h2)
    simpa only [smul_add, smul_zero, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, add_comm] using he
  refine ⟨eq_neg_of_add_eq_zero_left hb, ?_⟩
  intro i
  have hei := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hb
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at hei
  have hz : (2 : K) * B i i = 0 := by linear_combination hei
  exact (mul_eq_zero.mp hz).resolve_left h2

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
