import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Units.Hom

/-! The genuine natural GL block embedding A ↦ diag(A,A⁻ᵀ). -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixDiagonalBlockLift
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]

def diagonalUnit (d : I → Kˣ) : (Matrix I I K)ˣ where
  val := Matrix.diagonal (fun i => (d i : K))
  inv := Matrix.diagonal (fun i => (↑((d i)⁻¹) : K))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i => (↑(d i * (d i)⁻¹) : K)) = 1
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i => (↑((d i)⁻¹ * d i) : K)) = 1
    simp

def lift : (Matrix I I K)ˣ →* (Matrix (I ⊕ I) (I ⊕ I) K)ˣ where
  toFun A := {
    val := Matrix.fromBlocks (A : Matrix I I K) 0 0 (↑(A⁻¹) : Matrix I I K).transpose
    inv := Matrix.fromBlocks (↑(A⁻¹) : Matrix I I K) 0 0 (A : Matrix I I K).transpose
    val_inv := by simp [Matrix.fromBlocks_multiply, ← Matrix.transpose_mul]
    inv_val := by simp [Matrix.fromBlocks_multiply, ← Matrix.transpose_mul] }
  map_one' := by
    apply Units.ext
    simp [Matrix.fromBlocks_one]
  map_mul' A B := by
    apply Units.ext
    simp [Matrix.fromBlocks_multiply, Matrix.transpose_mul]

end SymmetricSubgroupAsymptotics.CFSGMatrixDiagonalBlockLift
