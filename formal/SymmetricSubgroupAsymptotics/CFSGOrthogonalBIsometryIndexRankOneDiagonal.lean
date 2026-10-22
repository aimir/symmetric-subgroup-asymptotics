import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneTorus
import SymmetricSubgroupAsymptotics.CFSGMatrixDiagonalBlockLift
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm

/-! The full hyperbolic diagonal parameter in the original rank-one
natural space. It preserves the literal Gram form and determinant one;
its squares are actual elementary words by the checked sparse formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneDiagonal
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIsometryIndexRankOneTorus
open CFSGMatrixDiagonalBlockLift
variable (K : Type) [Field K]

def diagonalWeights (a : Kˣ) : Index 1 → Kˣ
  | .inl (.inl _) => a
  | .inl (.inr _) => a⁻¹
  | .inr _ => 1

def diagonalHom : Kˣ →* (Mat K 1)ˣ where
  toFun a := diagonalUnit (diagonalWeights K a)
  map_one' := by
    apply Units.ext
    ext i j
    rcases i with ((i | i) | ⟨⟩) <;> rcases j with ((j | j) | ⟨⟩)
    all_goals try fin_cases i
    all_goals try fin_cases j
    all_goals simp [diagonalUnit, diagonalWeights, Matrix.diagonal_apply, Matrix.one_apply]
  map_mul' a b := by
    apply Units.ext
    change Matrix.diagonal (fun i => (diagonalWeights K (a * b) i : K)) =
      Matrix.diagonal (fun i => (diagonalWeights K a i : K)) *
        Matrix.diagonal (fun i => (diagonalWeights K b i : K))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases i with ((i | i) | ⟨⟩) <;> simp [diagonalWeights, mul_comm]

theorem diagonalHom_val (a : Kˣ) : (diagonalHom K a : Mat K 1) =
    Matrix.diagonal (fun i => (diagonalWeights K a i : K)) := rfl

theorem diagonalHom_preserves (a : Kˣ) :
    (diagonalHom K a : Mat K 1).transpose * gram K 1 * (diagonalHom K a : Mat K 1) = gram K 1 := by
  rw [diagonalHom_val, Matrix.diagonal_transpose]
  ext i j
  rcases i with ((i | i) | ⟨⟩) <;> rcases j with ((j | j) | ⟨⟩)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [Matrix.diagonal_mul, Matrix.mul_diagonal, diagonalWeights, gram,
    pos, neg, middle, Units.ne_zero a, mul_comm, mul_left_comm, mul_assoc]

theorem diagonalHom_det (a : Kˣ) : (diagonalHom K a : Mat K 1).det = 1 := by
  rw [diagonalHom_val, Matrix.det_diagonal]
  simp [diagonalWeights, Fintype.prod_sum_type, Units.ne_zero a]

theorem squareTorus_eq_diagonalHom (a : Kˣ) :
    (squareTorus K a).val = diagonalHom K (a ^ 2) := by
  apply Units.ext
  rw [squareTorus_val, diagonalHom_val]
  congr 1
  funext i
  rcases i with ((i | i) | ⟨⟩) <;> simp [squareDiagonal, diagonalWeights, inv_pow]

theorem square_diagonal_mem (a : Kˣ) : diagonalHom K (a ^ 2) ∈ elementaryRootGroup K 1 :=
  squareTorus_eq_diagonalHom K a ▸ (squareTorus K a).property

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneDiagonal
