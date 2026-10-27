import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullMatrixCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRationalForm

/-! Literal full B block coordinates and their relation to the actual
Gram form. The source realization is not assumed injective. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullBlockCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates
variable (R : Type*) [CommRing R] (r : ℕ)

structure Block (M : Mat R r) : Prop where
  nn : ∀ i j, M (neg r i) (neg r j) = -M (pos r j) (pos r i)
  pn : ∀ i j, M (pos r i) (neg r j) = -M (pos r j) (neg r i)
  np : ∀ i j, M (neg r i) (pos r j) = -M (neg r j) (pos r i)
  pn_diag : ∀ i, M (pos r i) (neg r i) = 0
  np_diag : ∀ i, M (neg r i) (pos r i) = 0
  mp : ∀ i, M (middle r) (pos r i) = -2 * M (neg r i) (middle r)
  mn : ∀ i, M (middle r) (neg r i) = -2 * M (pos r i) (middle r)
  mm : M (middle r) (middle r) = 0

theorem coordinates_injective (M N : Mat R r) (hM : Block R r M) (hN : Block R r N)
    (hc : coordinates R r M = coordinates R r N) : M = N := by
  have hEntry (j : BasisIndex r) :
      sign R r j * M (entry r j).1 (entry r j).2 =
        sign R r j * N (entry r j).1 (entry r j).2 := by
    change coordinates R r M j = coordinates R r N j
    exact congrFun hc j
  have hPP : ∀ i j : Fin r, M (pos r i) (pos r j) = N (pos r i) (pos r j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | he | hji
    · simpa only [entry, sign, one_mul] using
        hEntry (.inr (false, .inl ⟨(i, j), hij⟩))
    · have he' : i = j := Fin.ext he
      subst j
      simpa only [entry, sign, one_mul] using hEntry (.inl i)
    · simpa only [entry, sign, one_mul] using
        hEntry (.inr (true, .inl ⟨(j, i), hji⟩))
  have hPN : ∀ i j : Fin r, M (pos r i) (neg r j) = N (pos r i) (neg r j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | he | hji
    · simpa only [entry, sign, one_mul] using
        hEntry (.inr (false, .inr (.inr ⟨(i, j), hij⟩)))
    · have he' : i = j := Fin.ext he
      subst j
      rw [hM.pn_diag, hN.pn_diag]
    · rw [hM.pn i j, hN.pn i j]
      apply congrArg Neg.neg
      simpa only [entry, sign, one_mul] using
        hEntry (.inr (false, .inr (.inr ⟨(j, i), hji⟩)))
  have hNP : ∀ i j : Fin r, M (neg r i) (pos r j) = N (neg r i) (pos r j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | he | hji
    · rw [hM.np i j, hN.np i j]
      apply congrArg Neg.neg
      simpa only [entry, sign, one_mul] using
        hEntry (.inr (true, .inr (.inr ⟨(i, j), hij⟩)))
    · have he' : i = j := Fin.ext he
      subst j
      rw [hM.np_diag, hN.np_diag]
    · simpa only [entry, sign, one_mul] using
        hEntry (.inr (true, .inr (.inr ⟨(j, i), hji⟩)))
  have hPM : ∀ i : Fin r, M (pos r i) (middle r) = N (pos r i) (middle r) := by
    intro i
    simpa only [entry, sign, one_mul] using
      hEntry (.inr (false, .inr (.inl i)))
  have hNM : ∀ i : Fin r, M (neg r i) (middle r) = N (neg r i) (middle r) := by
    intro i
    apply neg_injective
    simpa only [entry, sign, neg_one_mul] using
      hEntry (.inr (true, .inr (.inl i)))
  apply Matrix.ext
  intro a b
  rcases a with (a | a) | a
  · rcases b with (b | b) | b
    · exact hPP a b
    · exact hPN a b
    · exact hPM a
  · rcases b with (b | b) | b
    · exact hNP a b
    · rw [hM.nn, hN.nn, hPP]
    · exact hNM a
  · rcases b with (b | b) | b
    · rw [hM.mp, hN.mp, hNM]
    · rw [hM.mn, hN.mn, hPM]
    · rw [hM.mm, hN.mm]

/-- Every literal natural basis matrix has the full B block shape. -/
theorem matrix_mem (j : BasisIndex r) : Block R r (matrix R r j) := by
  rcases j with i | ⟨neg, j⟩
  all_goals
    try (cases neg <;> rcases j with ij | (i | ij))
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;>
      simp [matrix, CFSGOrthogonalBUniformRootMatrixArithmetic.difference,
        CFSGOrthogonalBUniformRootMatrixArithmetic.short,
        CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot,
        Matrix.transpose_apply, Matrix.single_apply, pos, neg, middle,
        eq_comm, and_comm] <;>
      (try split_ifs) <;> ring

/-- Over the rational field the structural block conditions are exactly
membership in the actual pinned Gram-form Lie algebra. -/
theorem block_iff_mem_orthogonal (M : Mat ℚ r) :
    Block ℚ r M ↔ M ∈ skewAdjointMatricesLieSubalgebra (gram ℚ r) := by
  constructor
  · intro hM
    rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
    change M.transpose * gram ℚ r = gram ℚ r * (-M)
    ext a b
    rcases a with (a | a) | a <;> rcases b with (b | b) | b
    all_goals
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply]
    · linarith [hM.np a b]
    · linarith [hM.nn a b]
    · linarith [hM.mp a]
    · linarith [hM.nn b a]
    · linarith [hM.pn a b]
    · linarith [hM.mn a]
    · linarith [hM.mp b]
    · linarith [hM.mn b]
    · linarith [hM.mm]
  · intro hM
    rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] at hM
    change M.transpose * gram ℚ r = gram ℚ r * (-M) at hM
    have he (a b : Index r) := congrArg (fun T : Mat ℚ r => T a b) hM
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      have h := he (pos r i) (neg r j)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith
    · intro i j
      have h := he (neg r i) (neg r j)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith
    · intro i j
      have h := he (pos r i) (pos r j)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith
    · intro i
      have h := he (neg r i) (neg r i)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith
    · intro i
      have h := he (pos r i) (pos r i)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith
    · intro i
      have h := he (pos r i) (middle r)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith
    · intro i
      have h := he (neg r i) (middle r)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith
    · have h := he (middle r) (middle r)
      simp [gram, pos, neg, middle, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply] at h
      linarith

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullBlockCoordinates
