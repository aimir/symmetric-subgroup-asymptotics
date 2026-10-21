import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! An actual opposite block cell with an invertible diagonal block.
All three parameters are recovered from its literal matrix blocks. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixBlockCell
variable {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I R

def cell (A : Mˣ) (S T : M) :
    Matrix (I ⊕ I) (I ⊕ I) R :=
  Matrix.fromBlocks 1 S 0 1 *
    Matrix.fromBlocks (A : M) 0 0 (↑(A⁻¹) : M).transpose *
    Matrix.fromBlocks 1 0 T 1

theorem cell_blocks (A : Mˣ) (S T : M) :
    cell A S T = Matrix.fromBlocks
      ((A : M) + S * (↑(A⁻¹) : M).transpose * T)
      (S * (↑(A⁻¹) : M).transpose)
      ((↑(A⁻¹) : M).transpose * T) (↑(A⁻¹) : M).transpose := by
  simp [cell, Matrix.fromBlocks_multiply]

theorem cell_injective : Function.Injective
    (fun p : Mˣ × (M × M) => cell p.1 p.2.1 p.2.2) := by
  rintro ⟨A, S, T⟩ ⟨B, S', T'⟩ h
  have hA := congrArg Matrix.toBlocks₂₂ h
  simp only [cell_blocks, Matrix.toBlocks_fromBlocks₂₂] at hA
  have hAB : A = B := by
    apply inv_injective
    apply Units.ext
    exact Matrix.transpose_injective hA
  subst B
  have hS := congrArg Matrix.toBlocks₁₂ h
  have hT := congrArg Matrix.toBlocks₂₁ h
  simp only [cell_blocks, Matrix.toBlocks_fromBlocks₁₂] at hS
  simp only [cell_blocks, Matrix.toBlocks_fromBlocks₂₁] at hT
  have hi : (↑(A⁻¹) : M) * (A : M) = 1 := Units.inv_mul A
  have hj : (A : M) * (↑(A⁻¹) : M) = 1 := Units.mul_inv A
  have hSS : S = S' := by
    have hh := congrArg (fun X : M => X * (A : M).transpose) hS
    simpa only [mul_assoc, ← Matrix.transpose_mul, hj, Matrix.transpose_one, mul_one] using hh
  have hTT : T = T' := by
    have hh := congrArg (fun X : M => (A : M).transpose * X) hT
    simpa only [← mul_assoc, ← Matrix.transpose_mul, hi, Matrix.transpose_one, one_mul] using hh
  subst S'
  subst T'
  rfl

end SymmetricSubgroupAsymptotics.CFSGMatrixBlockCell
