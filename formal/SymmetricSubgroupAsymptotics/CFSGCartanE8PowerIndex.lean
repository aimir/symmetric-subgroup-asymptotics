import SymmetricSubgroupAsymptotics.CFSGCartanPowerIndex
import Mathlib.Data.Matrix.Cartan

/-! Explicit integral Smith witnesses for the literal Mathlib E8 Cartan
matrix. The displayed finite integer identities are checked by the kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCartanE8PowerIndex
open CFSGIntegerMatrixPowerHom CFSGCartanPowerIndex

private def left : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0;
      1, 1, 2, 2, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 0, 0, -1, 0;
      0, 0, 0, 0, 0, 0, 0, -1;
      2, 3, 4, 6, 5, 4, 3, 2]

private def right : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 2, -3, -2, -1, 0, 1;
      0, 1, -1, 3, 3, 3, 3, 3;
      0, 0, 1, -1, 0, 1, 2, 3;
      0, 0, 0, 1, 2, 3, 4, 5;
      0, 0, 0, 0, 1, 2, 3, 4;
      0, 0, 0, 0, 0, 1, 2, 3;
      0, 0, 0, 0, 0, 0, 1, 2;
      0, 0, 0, 0, 0, 0, 0, 1]

private def rightInv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, -2, 1, 0, 0, 0, 0;
      0, 1, 1, -2, 1, 0, 0, 0;
      0, 0, 1, 1, -2, 0, 0, 0;
      0, 0, 0, 1, -2, 1, 0, 0;
      0, 0, 0, 0, 1, -2, 1, 0;
      0, 0, 0, 0, 0, 1, -2, 1;
      0, 0, 0, 0, 0, 0, 1, -2;
      0, 0, 0, 0, 0, 0, 0, 1]

/-- Actual integral change-of-variable certificate; no Smith decomposition
or determinant statement is taken as a hypothesis. -/
def certificate : OneFactorCertificate CartanMatrix.E₈ (7 : Fin 8) 1 where
  left := left
  right := right
  rightInv := rightInv
  right_inverse := by decide
  diagonalization := by decide

/-- Literal Cartan monomial-image index over every finite field. -/
theorem range_index_le (K : Type*) [Field K] [Finite K] :
    (powerHom CartanMatrix.E₈ : (Fin 8 → Kˣ) →* (Fin 8 → Kˣ)).range.index ≤ 1 :=
  CFSGCartanPowerIndex.range_index_le certificate K

end SymmetricSubgroupAsymptotics.CFSGCartanE8PowerIndex
