import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis

/-! The literal weight of a matrix unit under a diagonal commutator. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixLie
variable {R I : Type*} [Ring R] [Fintype I] [DecidableEq I]

theorem diagonal_lie_single (d : I → R) (a b : I) (c : R) :
    ⁅Matrix.diagonal d, Matrix.single a b c⁆ =
      Matrix.single a b (d a * c - c * d b) := by
  apply Matrix.ext
  intro x y
  by_cases hx : x = a
  · subst x
    by_cases hy : y = b
    · subst y
      simp [Ring.lie_def, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single]
    · have hby : b ≠ y := Ne.symm hy
      simp [Ring.lie_def, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single, hby]
  · have hax : a ≠ x := Ne.symm hx
    simp [Ring.lie_def, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single, hax]

end SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixLie
