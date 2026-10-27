import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositivePrimitiveFamily
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBWeightedTranspose

/-! Actual negative B root images, by weighted anti-transpose execution
of the SAME signed source paths. The middle-coordinate weight two and
every (-1)^k coefficient are retained; no bare-transpose shortcut. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSignedPathImages
open CFSG.Models.Chevalley CFSGSerreDividedPowerPaths
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates CFSGOrthogonalBWeightedTranspose
variable (r : ℕ)

def rationalSteps (neg : Bool) : List (Fin r × ℕ) → Mat ℚ r → Mat ℚ r
  | [], X => X
  | s :: ss, X => rationalSteps neg ss
      (CFSGIntegralQuadraticRootOperators.operator ℚ (rootMatrix ℚ r neg s.1)
        (rootSecond ℚ r neg s.1) s.2 X)

theorem rational_operator_image (neg : Bool) (i : Fin r) (k : ℕ)
    (x : RationalLie (CartanMatrix.B r).transpose) :
    rationalOrthogonalRepresentation r (dividedPower (CartanMatrix.B r).transpose neg i k x) =
      CFSGIntegralQuadraticRootOperators.operator ℚ (rootMatrix ℚ r neg i)
        (rootSecond ℚ r neg i) k (rationalOrthogonalRepresentation r x) := by
  change (realizationData r).rational (dividedPower (CartanMatrix.B r).transpose neg i k x) = _
  rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,
    CFSGSerreQuadraticMatrix.rational_rootVector, realizationData_fieldRoot]
  exact CFSGQuadraticRootDividedPowers.rational_operator _ _
    (rootMatrix_square ℚ r neg i) (rootMatrix_mul_second ℚ r neg i)
    (rootSecond_mul_matrix ℚ r neg i) k _

theorem rational_applySteps_image (neg : Bool) (ss : List (Fin r × ℕ)) (x : Source r) :
    rationalOrthogonalRepresentation r (applySteps (CartanMatrix.B r).transpose neg ss x).val =
      rationalSteps r neg ss (rationalOrthogonalRepresentation r x.val) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    change rationalOrthogonalRepresentation r
      (applySteps _ neg ss (integralOperator _ neg s.1 s.2 x)).val = _
    rw [ih]
    change rationalSteps r neg ss
      (rationalOrthogonalRepresentation r (dividedPower _ neg s.1 s.2 x.val)) = _
    rw [rational_operator_image]
    rfl

theorem rational_path_image (neg : Bool) (start : Fin r) (ss : List (Fin r × ℕ)) :
    rationalOrthogonalRepresentation r (path r neg start ss).val =
      (if neg then (-1 : ℤ) ^ (ss.map Prod.snd).sum else 1) •
        rationalSteps r neg ss (rootMatrix ℚ r neg start) := by
  simp only [path, Submodule.coe_smul, map_zsmul, pathVector, rational_applySteps_image]
  congr 1
  congr 1
  cases neg
  · exact rationalOrthogonalRepresentation_E r start
  · exact rationalOrthogonalRepresentation_F r start

theorem rationalSteps_smul (neg : Bool) (ss : List (Fin r × ℕ)) (a : ℤ) (X : Mat ℚ r) :
    rationalSteps r neg ss (a • X) = a • rationalSteps r neg ss X := by
  induction ss generalizing X with
  | nil => rfl
  | cons s ss ih => simp only [rationalSteps, map_zsmul, ih]

theorem rationalSteps_negative (ss : List (Fin r × ℕ)) (X : Mat ℚ r) :
    rationalSteps r true ss (weightedTranspose r X) =
      ((-1 : ℤ) ^ (ss.map Prod.snd).sum) • weightedTranspose r (rationalSteps r false ss X) := by
  induction ss generalizing X with
  | nil => simp only [rationalSteps, List.map_nil, List.sum_nil, pow_zero, one_smul]
  | cons s ss ih =>
    change rationalSteps r true ss
      (CFSGIntegralQuadraticRootOperators.operator ℚ (negative ℚ r s.1)
        (negativeSecond ℚ r s.1) s.2 (weightedTranspose r X)) = _
    have ho : CFSGIntegralQuadraticRootOperators.operator ℚ (negative ℚ r s.1)
        (negativeSecond ℚ r s.1) s.2 (weightedTranspose r X) =
        ((-1 : ℤ) ^ s.2) • weightedTranspose r
          (CFSGIntegralQuadraticRootOperators.operator ℚ (positive ℚ r s.1)
            (positiveSecond ℚ r s.1) s.2 X) := by
      simpa only [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one] using
        operator_negative r s.1 s.2 X
    rw [ho, rationalSteps_smul, ih]
    simp only [List.map_cons, List.sum_cons, pow_add, smul_smul]
    rfl

theorem path_negative_image (start : Fin r) (ss : List (Fin r × ℕ)) :
    rationalOrthogonalRepresentation r (path r true start ss).val =
      weightedTranspose r (rationalOrthogonalRepresentation r (path r false start ss).val) := by
  simp only [rational_path_image, Bool.false_eq_true, if_false, if_true, one_smul,
    rootMatrix]
  rw [← weightedTranspose_positive, rationalSteps_negative, smul_smul, ← mul_pow]
  norm_num

theorem weightedTranspose_positive_matrix (j : RootIndex r) :
    weightedTranspose r (matrix ℚ r (.inr (false, j))) = matrix ℚ r (.inr (true, j)) := by
  ext a b
  rcases j with ij | (i | ij) <;>
    rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
      simp [weightedTranspose_apply, matrix, CFSGOrthogonalBWeightedTranspose.weight, inverseWeight,
        CFSGOrthogonalBUniformRootMatrixArithmetic.difference,
        CFSGOrthogonalBUniformRootMatrixArithmetic.short,
        CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot,
        Matrix.transpose_apply, Matrix.single_apply, pos, neg, middle, eq_comm, and_comm] <;>
      (try split_ifs) <;> (try simp_all) <;> ring

theorem root_negative_image (j : RootIndex r) :
    rationalOrthogonalRepresentation r (root r true j).val = matrix ℚ r (.inr (true, j)) := by
  have hp : rationalOrthogonalRepresentation r (root r true j).val =
      weightedTranspose r (rationalOrthogonalRepresentation r (root r false j).val) := by
    rcases j with ij | (i | ij)
    · exact path_negative_image r _ _
    · exact path_negative_image r _ _
    · simp only [root, sumRoot, Submodule.coe_smul, map_zsmul, path_negative_image]
  rw [hp]
  have h := CFSGOrthogonalBOriginalPositivePrimitiveFamily.source_image r (.inr j)
  change rationalOrthogonalRepresentation r (root r false j).val = matrix ℚ r (.inr (false, j)) at h
  rw [h, weightedTranspose_positive_matrix]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSignedPathImages
