import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexGeneralLinearLift
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits

/-! The remaining GL determinant parameter is an actual one-pair
diagonal homomorphism. Every SQUARE parameter is an original D word:
the fork torus times the inverse-parameter chain torus. This is a
literal matrix identity, valid in every characteristic and rank>=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexLastSquares
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDIsometryIndexGeneralLinearLift
variable (K : Type) [Field K]

def lastWeightsHom (s : ℕ) : Kˣ →* (Fin (s + 1) → Kˣ) where
  toFun a i := if i = Fin.last s then a else 1
  map_one' := by funext i; split_ifs <;> rfl
  map_mul' a b := by
    funext i
    by_cases hi : i = Fin.last s <;> simp [hi]

def lastGLHom (s : ℕ) : Kˣ →* Matrix.GeneralLinearGroup (Fin (s + 1)) K :=
  (CFSGDiagonalMatrixUnits.diagonalHom (Fin (s + 1)) K).comp (lastWeightsHom K s)

theorem lastGLHom_apply (s : ℕ) (a : Kˣ) :
    lastGLHom K s a = CFSGGeneralLinearDeterminantCosets.lastDiagonal K s a := Units.ext rfl

def lastDiagonalHom (s : ℕ) : Kˣ →* (Mat K (s + 1))ˣ :=
  (generalLinearLift K (s + 1)).comp (lastGLHom K s)

theorem lastDiagonalHom_eq_lift (s : ℕ) (a : Kˣ) :
    lastDiagonalHom K s a = generalLinearLift K (s + 1)
      (CFSGGeneralLinearDeterminantCosets.lastDiagonal K s a) := by
  change generalLinearLift K (s + 1) (lastGLHom K s a) = _
  rw [lastGLHom_apply]

def squareLastWord (s : ℕ) (a : Kˣ) : elementaryRootGroup K (s + 2) :=
  forkTorus K s a * doubleIntoElementary K (s + 2)
    (CFSGTypeARootTorus.torus (pen_ne_last s) a⁻¹)

theorem squareLastWord_val (s : ℕ) (a : Kˣ) :
    (squareLastWord K s a).val = lastDiagonalHom K (s + 1) (a ^ 2) := by
  apply Units.ext
  change ((forkTorus K s a).val : Mat K (s + 2)) *
      doubleMatrix K (s + 2) (CFSGTypeARootTorus.torus (pen_ne_last s) a⁻¹) = _
  rw [forkTorus_coe, doubleMatrix_torus, lastDiagonalHom_eq_lift, generalLinearLift_val]
  change Matrix.diagonal (forkDiagonal K s a) * Matrix.diagonal (chainDiagonal K s a⁻¹) =
    Matrix.fromBlocks
      (Matrix.diagonal (fun i : Fin (s + 2) =>
        ((if i = Fin.last (s + 1) then a ^ 2 else 1 : Kˣ) : K))) 0 0
      (Matrix.diagonal (fun i : Fin (s + 2) =>
        (((if i = Fin.last (s + 1) then a ^ 2 else 1 : Kˣ)⁻¹ : Kˣ) : K))).transpose
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_transpose, Matrix.fromBlocks_diagonal]
  congr 1
  funext x
  have hne : pen s ≠ Fin.last (s + 1) := pen_ne_last s
  rcases x with i | i
  all_goals simp only [forkDiagonal, chainDiagonal, last, Sum.elim_inl, Sum.elim_inr]
  all_goals by_cases hp : i = pen s
  · subst i
    simp [hne, Units.val_inv_eq_inv_val, Units.ne_zero]
  · by_cases hl : i = Fin.last (s + 1)
    · subst i
      simp [Ne.symm hne, Units.val_inv_eq_inv_val, pow_two]
    · simp [hp, hl]
  · subst i
    simp [hne, Units.val_inv_eq_inv_val, Units.ne_zero]
  · by_cases hl : i = Fin.last (s + 1)
    · subst i
      simp [Ne.symm hne, Units.val_inv_eq_inv_val, pow_two]
    · simp [hp, hl]

theorem last_square_mem (s : ℕ) (a : Kˣ) :
    lastDiagonalHom K (s + 1) (a ^ 2) ∈ elementaryRootGroup K (s + 2) := by
  rw [← squareLastWord_val]
  exact (squareLastWord K s a).property

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexLastSquares
