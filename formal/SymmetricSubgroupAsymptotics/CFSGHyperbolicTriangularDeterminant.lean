import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.Torsion.Free

/-! A literal block-upper-triangular hyperbolic isometry has determinant
one. This is an elementary block calculation, with no orthogonal-group
identification and no nonsingularity assumption on a diagonal block. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicTriangularDeterminant
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def hyperbolicGram : Matrix (I ⊕ I) (I ⊕ I) K :=
  Matrix.fromBlocks 0 ((2 : K) • 1) ((2 : K) • 1) 0

theorem diagonal_pairing (h2 : (2 : K) ≠ 0) (A B D : Matrix I I K)
    (hf : (Matrix.fromBlocks A B 0 D).transpose * hyperbolicGram *
      Matrix.fromBlocks A B 0 D = hyperbolicGram) : A.transpose * D = 1 := by
  have he := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) K => M.toBlocks₁₂) hf
  simp only [hyperbolicGram, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂,
    zero_mul, mul_zero, zero_add, add_zero] at he
  apply smul_right_injective (Matrix I I K) h2
  simpa only [mul_smul_comm, smul_mul_assoc, mul_one] using he

theorem determinant_eq_one (h2 : (2 : K) ≠ 0) (A B D : Matrix I I K)
    (hf : (Matrix.fromBlocks A B 0 D).transpose * hyperbolicGram *
      Matrix.fromBlocks A B 0 D = hyperbolicGram) :
    (Matrix.fromBlocks A B 0 D).det = 1 := by
  have hAD := diagonal_pairing h2 A B D hf
  calc
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det := Matrix.det_fromBlocks_zero₂₁ A B D
    _ = (A.transpose * D).det := by rw [Matrix.det_mul, Matrix.det_transpose]
    _ = 1 := by rw [hAD, Matrix.det_one]

end SymmetricSubgroupAsymptotics.CFSGHyperbolicTriangularDeterminant
