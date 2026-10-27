import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformRootMatrixArithmetic
import SymmetricSubgroupAsymptotics.QuadraticRootOperatorAntiTransport
import Mathlib.Tactic.NormNum

/-! The literal B negative simple matrices are weighted transposes,
not bare transposes: the middle coordinate has weight two. The map is
anti-multiplicative, with its quadratic-operator sign retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBWeightedTranspose
open CFSGOrthogonalBSerreMatrices
variable (r : ℕ)

def weight : Index r → ℚ
  | .inl _ => 1
  | .inr _ => 2

def inverseWeight : Index r → ℚ
  | .inl _ => 1
  | .inr _ => 1 / 2

def diagonal : Mat ℚ r := Matrix.diagonal (weight r)
def inverseDiagonal : Mat ℚ r := Matrix.diagonal (inverseWeight r)

theorem inverseDiagonal_mul : inverseDiagonal r * diagonal r = 1 := by
  have h : (fun i : Index r => inverseWeight r i * weight r i) = fun _ => 1 := by
    funext i
    cases i <;> norm_num [weight, inverseWeight]
  rw [inverseDiagonal, diagonal, Matrix.diagonal_mul_diagonal, h, Matrix.diagonal_one]

def weightedTranspose : Mat ℚ r →ₗ[ℚ] Mat ℚ r where
  toFun M := diagonal r * M.transpose * inverseDiagonal r
  map_add' M N := by simp only [Matrix.transpose_add, mul_add, add_mul]
  map_smul' a M := by simp only [Matrix.transpose_smul, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

theorem weightedTranspose_apply (M : Mat ℚ r) (a b : Index r) :
    weightedTranspose r M a b = weight r a * M b a * inverseWeight r b := by
  change (diagonal r * M.transpose * inverseDiagonal r) a b = _
  simp only [diagonal, inverseDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.transpose_apply]

theorem weightedTranspose_mul (M N : Mat ℚ r) :
    weightedTranspose r (M * N) = weightedTranspose r N * weightedTranspose r M := by
  change diagonal r * (M * N).transpose * inverseDiagonal r =
    (diagonal r * N.transpose * inverseDiagonal r) *
      (diagonal r * M.transpose * inverseDiagonal r)
  rw [Matrix.transpose_mul]
  symm
  calc
    _ = diagonal r * N.transpose * (inverseDiagonal r * diagonal r) *
        M.transpose * inverseDiagonal r := by simp only [mul_assoc]
    _ = diagonal r * N.transpose * M.transpose * inverseDiagonal r := by
      rw [inverseDiagonal_mul, mul_one]
    _ = diagonal r * (N.transpose * M.transpose) * inverseDiagonal r := by
      simp only [mul_assoc]

theorem weightedTranspose_positive (i : Fin r) :
    weightedTranspose r (positive ℚ r i) = negative ℚ r i := by
  by_cases hi : i.val + 1 < r
  all_goals
    ext a b
    rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
      simp [weightedTranspose_apply, positive, negative, hi, weight, inverseWeight,
        Matrix.single_apply, pos, neg, middle, eq_comm, and_comm] <;>
      (try split_ifs) <;> simp_all <;> ring

theorem weightedTranspose_positiveSecond (i : Fin r) :
    weightedTranspose r (positiveSecond ℚ r i) = negativeSecond ℚ r i := by
  by_cases hi : i.val + 1 < r
  all_goals
    ext a b
    rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
      simp [weightedTranspose_apply, positiveSecond, negativeSecond, hi, weight, inverseWeight,
        Matrix.single_apply, pos, neg, middle, eq_comm, and_comm] <;>
      (try split_ifs) <;> simp_all <;> ring

theorem operator_negative (i : Fin r) (k : ℕ) (X : Mat ℚ r) :
    CFSGIntegralQuadraticRootOperators.operator ℚ
      (negative ℚ r i) (negativeSecond ℚ r i) k (weightedTranspose r X) =
        ((-1 : ℚ) ^ k) • weightedTranspose r
          (CFSGIntegralQuadraticRootOperators.operator ℚ
            (positive ℚ r i) (positiveSecond ℚ r i) k X) := by
  have h := QuadraticRootOperatorAntiTransport.operator
    (weightedTranspose r) (weightedTranspose_mul r)
    (positive ℚ r i) (positiveSecond ℚ r i) X k
  rw [weightedTranspose_positive, weightedTranspose_positiveSecond] at h
  rw [h, smul_smul, ← mul_pow]
  simp

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBWeightedTranspose
