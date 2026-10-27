import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveWeightIdentification

/-! The B grading matrix is a positive combination of actual Cartan
tails, with the genuine terminal one-half coefficient retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBCartanTailGrading
open CFSG.Models.Chevalley CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBFullMatrixCoordinates
open CFSGOrthogonalBUniformRootGrading
variable (r : ℕ)

def cartanAt (a : ℕ) : Mat ℚ r :=
  if h : a < r then (if a + 1 < r then (1 : ℚ) else 1 / 2) • cartan ℚ r ⟨a, h⟩ else 0

theorem Hhalf_rational_image (a : ℕ) :
    rationalOrthogonalRepresentation r (CFSGOrthogonalBOriginalRationalCartanTail.Hhalf r a) =
      cartanAt r a := by
  by_cases h : a < r
  · simp only [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, cartanAt, dif_pos h,
      map_smul, rationalOrthogonalRepresentation_H]
  · simp only [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, cartanAt, dif_neg h, map_zero]

theorem diagonal_tail (i : Fin r) :
    matrix ℚ r (.inl i) = ∑ a ∈ Finset.range (r - i.val), cartanAt r (i.val + a) := by
  have h := CFSGOrthogonalBOriginalRationalCartanTail.tail_image r i.val
  simp only [CFSGOrthogonalBOriginalRationalCartanTail.tail, map_sum, Hhalf_rational_image,
    CFSGOrthogonalBOriginalRationalCartanTail.diagonal, dif_pos i.isLt] at h
  exact h.symm

def coefficient (i : Fin r) : ℚ := (r : ℚ) - i.val

theorem coefficient_pos (i : Fin r) : 0 < coefficient r i := by
  have hi : (i.val : ℚ) + 1 ≤ (r : ℚ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  unfold coefficient
  linarith

private theorem sum_selected (f : Fin r → ℚ) (x y : Fin r) :
    (∑ i : Fin r, if x = i ∧ y = i then f i else 0) = if x = y then f x else 0 := by
  by_cases h : x = y
  · subst y; simp [eq_comm]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hx : x = i
    · subst i; simp [Ne.symm h]
    · simp [hx]

theorem grading_diagonal_sum :
    gradingMatrix r = ∑ i : Fin r, coefficient r i • matrix ℚ r (.inl i) := by
  ext x y
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp [gradingMatrix, Matrix.diagonal_apply, diagonalWeight, coefficient,
      matrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
      mul_ite, Finset.sum_neg_distrib, sum_selected, eq_comm, pos, neg, middle]
  all_goals (try split_ifs) <;> (try simp_all only [sum_selected]) <;> ring

theorem grading_tail_sum :
    gradingMatrix r = ∑ i : Fin r, coefficient r i •
      ∑ a ∈ Finset.range (r - i.val), cartanAt r (i.val + a) := by
  rw [grading_diagonal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [diagonal_tail]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBCartanTailGrading
