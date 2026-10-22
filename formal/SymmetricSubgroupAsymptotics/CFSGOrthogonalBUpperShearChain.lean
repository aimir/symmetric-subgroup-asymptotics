import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUpperShearForm
import Mathlib.Data.Matrix.Basis

/-! Actual chain-root commutation on the unchanged B upper shear is
the alternating congruence equation E_ij B + B E_ji = 0. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

theorem chainCoefficient_blocks (n : ℕ) (i j : Fin n) :
    Matrix.single (pos n i) (pos n j) (1 : K) - Matrix.single (neg n j) (neg n i) 1 =
      Matrix.fromBlocks (Matrix.fromBlocks (Matrix.single i j 1) 0 0
        (-Matrix.single j i 1)) 0 0 0 := by
  ext x y
  rcases x with (a | a) | ⟨⟩ <;> rcases y with (b | b) | ⟨⟩ <;>
    simp [pos, neg, Matrix.fromBlocks, Matrix.single_apply]

theorem upperShear_chain_commutation (n : ℕ) (B : Matrix (Fin n) (Fin n) K)
    (i j : Fin n)
    (h : upperShearMatrix n B *
        (Matrix.single (pos n i) (pos n j) 1 - Matrix.single (neg n j) (neg n i) 1) =
      (Matrix.single (pos n i) (pos n j) 1 - Matrix.single (neg n j) (neg n i) 1) *
        upperShearMatrix n B) :
    Matrix.single i j 1 * B + B * Matrix.single j i 1 = 0 := by
  have he := congrArg (fun M : Mat K n => M.toBlocks₁₁.toBlocks₁₂) h
  simp only [upperShearMatrix, chainCoefficient_blocks, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    zero_mul, mul_zero, zero_add, add_zero] at he
  simp [Matrix.fromBlocks_multiply] at he
  have he' : -(B * Matrix.single j i 1) = Matrix.single i j 1 * B := by
    simpa only [mul_neg] using he
  rw [← he', neg_add_cancel]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
