import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction

/-! A support calculation for diagonal conjugation of actual matrix
root lines. The matrix may have several nonzero entries; its original
coordinates and signs are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]

theorem diagonal_intertwines (d : I → K) (X : Matrix I I K) (l : K)
    (hsupport : ∀ i j, X i j ≠ 0 → d i = l * d j) :
    Matrix.diagonal d * X = (l • X) * Matrix.diagonal d := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hz : X i j = 0
  · simp only [hz, mul_zero, zero_mul]
  · rw [hsupport i j hz]
    ring

/-- Exact conjugation on a matrix root line, with no assumption that
the ambient unit group equals a named classical group. -/
theorem root_line_conjugation (W U V : (Matrix I I K)ˣ)
    (d : I → K) (X : Matrix I I K) (l a : K)
    (hW : (W : Matrix I I K) = Matrix.diagonal d)
    (hU : (U : Matrix I I K) = 1 + a • X)
    (hV : (V : Matrix I I K) = 1 + (l * a) • X)
    (hsupport : ∀ i j, X i j ≠ 0 → d i = l * d j) :
    W * U * W⁻¹ = V := by
  have hDX := diagonal_intertwines d X l hsupport
  have hm : W * U = V * W := by
    apply Units.ext
    change (W : Matrix I I K) * (U : Matrix I I K) =
      (V : Matrix I I K) * (W : Matrix I I K)
    rw [hW, hU, hV, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp only [Matrix.mul_smul, hDX, Matrix.smul_mul, smul_smul, mul_comm a l]
  have hc := congrArg (fun Y : (Matrix I I K)ˣ => Y * W⁻¹) hm
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hc

end SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction
