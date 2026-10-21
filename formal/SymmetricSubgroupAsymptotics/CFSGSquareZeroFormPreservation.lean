import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

/-! A square-zero infinitesimal isometry exponentiates to the literal
matrix `1 + t N`. This statement uses the actual bilinear-form matrix. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSquareZeroFormPreservation
variable {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

theorem quadratic_term_zero (J N : Matrix I I R)
    (hN : N * N = 0) (hLie : N * J + J * N.transpose = 0) :
    N * J * N.transpose = 0 := by
  have hlin : J * N.transpose = -(N * J) := by
    calc
      J * N.transpose = (N * J + J * N.transpose) - N * J := by abel
      _ = -(N * J) := by rw [hLie]; simp
  rw [mul_assoc, hlin, mul_neg, ← mul_assoc, hN, zero_mul, neg_zero]

theorem transvection_preserves (J N : Matrix I I R)
    (hN : N * N = 0) (hLie : N * J + J * N.transpose = 0) (t : R) :
    (1 + t • N) * J * (1 + t • N).transpose = J := by
  have hlin : J * N.transpose = -(N * J) := by
    calc
      J * N.transpose = (N * J + J * N.transpose) - N * J := by abel
      _ = -(N * J) := by rw [hLie]; simp
  have hquad := quadratic_term_zero J N hN hLie
  simp [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hquad, hlin] <;> abel

end SymmetricSubgroupAsymptotics.CFSGSquareZeroFormPreservation
