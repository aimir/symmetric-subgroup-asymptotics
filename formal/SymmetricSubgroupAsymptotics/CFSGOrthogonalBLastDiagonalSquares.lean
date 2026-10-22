import SymmetricSubgroupAsymptotics.CFSGOrthogonalBLastDiagonal
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneDiagonal

/-! Squares of the actual last-pair diagonal are original elementary B
words in every positive rank. This is the checked rank-one six-root
word transported through the literal elementary tail embeddings. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBLastDiagonalSquares
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBLastDiagonal
open CFSGOrthogonalBTailCoordinates CFSGOrthogonalBIsometryIndexRankOneDiagonal
variable (K : Type) [Field K]

theorem last_zero (a : Kˣ) : lastDiagonalHom K 0 a = diagonalHom K a := by
  apply Units.ext
  ext i j
  rcases i with (i | i) | ⟨⟩ <;> rcases j with (j | j) | ⟨⟩
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [lastDiagonalHom, diagonalHom, lastWeights, diagonalWeights, CFSGMatrixDiagonalBlockLift.diagonalUnit]

theorem square_lastDiagonal_mem (s : ℕ) (a : Kˣ) :
    lastDiagonalHom K s (a ^ 2) ∈ elementaryRootGroup K (s + 1) := by
  induction s with
  | zero =>
    rw [last_zero]
    exact square_diagonal_mem K a
  | succ s ih =>
    rw [← tailUnitHom_lastDiagonal K s (a ^ 2)]
    exact (tailElementaryHom K (s + 1) ⟨lastDiagonalHom K s (a ^ 2), ih⟩).property

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBLastDiagonalSquares
