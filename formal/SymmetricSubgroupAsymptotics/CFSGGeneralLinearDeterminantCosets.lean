import SymmetricSubgroupAsymptotics.CFSGMatrixDiagonalBlockLift
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.BigOperators.Fin

/-! Every literal general-linear matrix is a chosen one-coordinate
diagonal times an actual special-linear matrix. No finite-field or
generation theorem is involved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGeneralLinearDeterminantCosets
open CFSGMatrixDiagonalBlockLift
variable (K : Type) [Field K]

def lastDiagonal (s : ℕ) (a : Kˣ) : Matrix.GeneralLinearGroup (Fin (s + 1)) K :=
  diagonalUnit (fun i => if i = Fin.last s then a else 1)

theorem lastDiagonal_det (s : ℕ) (a : Kˣ) :
    Matrix.GeneralLinearGroup.det (lastDiagonal K s a) = a := by
  apply Units.ext
  change (Matrix.diagonal (fun i : Fin (s + 1) =>
    ((if i = Fin.last s then a else 1 : Kˣ) : K))).det = (a : K)
  rw [Matrix.det_diagonal, Fin.prod_univ_castSucc]
  simp

theorem exists_special_factor (s : ℕ) (A : Matrix.GeneralLinearGroup (Fin (s + 1)) K) :
    ∃ S : Matrix.SpecialLinearGroup (Fin (s + 1)) K,
      A = lastDiagonal K s (Matrix.GeneralLinearGroup.det A) * S.toGL := by
  let d := lastDiagonal K s (Matrix.GeneralLinearGroup.det A)
  let B := d⁻¹ * A
  have hd : Matrix.GeneralLinearGroup.det B = 1 := by
    dsimp [B, d]
    rw [map_mul, map_inv, lastDiagonal_det, inv_mul_cancel]
  let S : Matrix.SpecialLinearGroup (Fin (s + 1)) K :=
    ⟨(B : Matrix (Fin (s + 1)) (Fin (s + 1)) K),
      congrArg (fun a : Kˣ => (a : K)) hd⟩
  have hS : S.toGL = B := Units.ext rfl
  refine ⟨S, ?_⟩
  rw [hS]
  change A = d * (d⁻¹ * A)
  group

end SymmetricSubgroupAsymptotics.CFSGGeneralLinearDeterminantCosets
