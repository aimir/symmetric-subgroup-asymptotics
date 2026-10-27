import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCartanTailGrading

/-! Positive comparison for original B source-height induction, using
actual positive Cartan-tail charges. Cancellation uses nonzero natural
basis vectors, never a possibly-zero raising bracket. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveComparison
open CFSG.Models.Chevalley CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBFullMatrixCoordinates
open CFSGOrthogonalBUniformRootGrading CFSGOrthogonalBUniformPositiveTables
open CFSGOrthogonalBOriginalPositiveSourceProfile CFSGOrthogonalBCartanTailGrading
variable (r : ℕ)

def weightAt (w : Fin r → ℚ) (a : ℕ) : ℚ :=
  if h : a < r then (if a + 1 < r then (1 : ℚ) else 1 / 2) * w ⟨a, h⟩ else 0

def charge (w : Fin r → ℚ) : ℚ :=
  ∑ i : Fin r, coefficient r i * ∑ a ∈ Finset.range (r - i.val), weightAt r w (i.val + a)

private theorem charge_eigen (M : Mat ℚ r) (w : Fin r → ℚ)
    (hw : ∀ a, ⁅cartan ℚ r a, M⁆ = w a • M) :
    ⁅gradingMatrix r, M⁆ = charge r w • M := by
  have ha : ∀ a, ⁅cartanAt r a, M⁆ = weightAt r w a • M := by
    intro a
    by_cases h : a < r
    · simp only [cartanAt, weightAt, dif_pos h, smul_lie, hw, smul_smul]
    · simp only [cartanAt, weightAt, dif_neg h, zero_lie, zero_smul]
  rw [grading_tail_sum, sum_lie]
  simp_rw [smul_lie, sum_lie, ha]
  simp_rw [← Finset.sum_smul, smul_smul]
  rw [← Finset.sum_smul]
  rfl

private theorem charge_eq (M : Mat ℚ r) (hM : M ≠ 0) (w : Fin r → ℚ) (mu : ℚ)
    (hw : ∀ a, ⁅cartan ℚ r a, M⁆ = w a • M)
    (hZ : ⁅gradingMatrix r, M⁆ = mu • M) : charge r w = mu := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, M x y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hM (Matrix.ext fun x y => h x y)
  have h := congrArg (fun N : Mat ℚ r => N x y) ((charge_eigen r M w hw).symm.trans hZ)
  exact mul_right_cancel₀ hxy h

private theorem charge_nonpos (w : Fin r → ℚ) (hw : ∀ a, w a ≤ 0) : charge r w ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (coefficient_pos r i))
  apply Finset.sum_nonpos
  intro a ha
  by_cases h : i.val + a < r
  · rw [weightAt, dif_pos h]
    have hc : (0 : ℚ) ≤ if i.val + a + 1 < r then 1 else 1 / 2 := by
      split_ifs <;> norm_num
    exact mul_nonpos_of_nonneg_of_nonpos hc (hw ⟨i.val + a, h⟩)
  · rw [weightAt, dif_neg h]

private theorem positive_ne_zero (i : Fin r) : positive ℚ r i ≠ 0 := by
  intro hz
  by_cases hi : i.val + 1 < r
  · have h := congrArg (fun M : Mat ℚ r => M (pos r i) (pos r ⟨i.val + 1, hi⟩)) hz
    simpa [positive, hi, Matrix.single_apply, pos, neg, middle] using h
  · have h := congrArg (fun M : Mat ℚ r => M (pos r i) (middle r)) hz
    simpa [positive, hi, Matrix.single_apply, pos, neg, middle] using h

theorem positive_comparison (i : Fin r) (j : PositiveIndex r) :
    ∃ a, 0 < ((CartanMatrix.B r).transpose a i : ℚ) +
      CFSGOrthogonalBUniformCorootWeights.weight r a j := by
  have hE : charge r (fun a => ((CartanMatrix.B r).transpose a i : ℚ)) = 1 :=
    charge_eq r _ (positive_ne_zero r i) _ 1
      (fun a => by simpa only [Int.cast_smul_eq_zsmul] using HE ℚ r a i)
      (by simpa only [one_smul] using positive_weight r i)
  have hM : positiveMatrix r j ≠ 0 := by
    intro hz
    have h := congrArg (fun M : Mat ℚ r => positiveCoordinates r M j) hz
    simpa only [positive_coordinates_matrix, map_zero, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] using h
  have hJ : charge r (fun a => CFSGOrthogonalBUniformCorootWeights.weight r a j) = (height r j : ℚ) :=
    charge_eq r _ hM _ _ (fun a => CFSGOrthogonalBUniformCorootWeights.positive_matrix_weight r a j)
      (by simpa only [positiveMatrix, fullIndex_grade] using matrix_weight r (fullIndex r j))
  by_contra h
  push_neg at h
  have hn := charge_nonpos r
    (fun a => ((CartanMatrix.B r).transpose a i : ℚ) + CFSGOrthogonalBUniformCorootWeights.weight r a j) h
  have hadd : charge r (fun a => ((CartanMatrix.B r).transpose a i : ℚ) +
        CFSGOrthogonalBUniformCorootWeights.weight r a j) =
      charge r (fun a => ((CartanMatrix.B r).transpose a i : ℚ)) +
        charge r (fun a => CFSGOrthogonalBUniformCorootWeights.weight r a j) := by
    have hat : ∀ a, weightAt r (fun a => ((CartanMatrix.B r).transpose a i : ℚ) +
          CFSGOrthogonalBUniformCorootWeights.weight r a j) a =
        weightAt r (fun a => ((CartanMatrix.B r).transpose a i : ℚ)) a +
          weightAt r (fun a => CFSGOrthogonalBUniformCorootWeights.weight r a j) a := by
      intro a
      by_cases h : a < r <;> simp [weightAt, h, mul_add]
    simp only [charge, hat, Finset.sum_add_distrib, mul_add]
  rw [hadd, hE, hJ] at hn
  have hnonneg : (0 : ℚ) ≤ (height r j : ℚ) := Nat.cast_nonneg _
  linarith

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveComparison
