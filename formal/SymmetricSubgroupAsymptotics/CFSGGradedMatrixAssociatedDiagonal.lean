import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularUnits

/-! The literal degree-zero projection is multiplicative on weak
triangular matrices. Its identity fibre is the strict associated-graded
kernel, including repeated weights and arbitrary characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixAssociatedDiagonal
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def associatedDiagonal (w : I → ℤ) (M : Matrix I I K) : Matrix I I K :=
  fun i j => if w i = w j then M i j else 0

theorem associatedDiagonal_one (w : I → ℤ) :
    associatedDiagonal w (1 : Matrix I I K) = 1 := by
  ext i j
  by_cases hij : w i = w j
  · simp only [associatedDiagonal,if_pos hij]
  · have hne : i ≠ j := fun h => hij (congrArg w h)
    simp only [associatedDiagonal,if_neg hij,Matrix.one_apply,if_neg hne]

theorem associatedDiagonal_mul (w : I → ℤ) (M N : Matrix I I K)
    (hM : M.BlockTriangular (fun i => -w i))
    (hN : N.BlockTriangular (fun i => -w i)) :
    associatedDiagonal w (M*N) = associatedDiagonal w M * associatedDiagonal w N := by
  ext i j
  by_cases hij : w i = w j
  · change (if w i = w j then (M*N) i j else 0) = _
    rw [if_pos hij,Matrix.mul_apply,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : w i = w k
    · have hkj : w k = w j := hik.symm.trans hij
      simp only [associatedDiagonal,if_pos hik,if_pos hkj]
    · rw [show associatedDiagonal w M i k = 0 from if_neg hik,zero_mul]
      rcases lt_or_gt_of_ne hik with hlt | hgt
      · rw [hM (show -w k < -w i by omega),zero_mul]
      · rw [hN (show -w j < -w k by omega),mul_zero]
  · change (if w i = w j then (M*N) i j else 0) = _
    rw [if_neg hij,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : w i = w k
    · have hkj : w k ≠ w j := fun h => hij (hik.trans h)
      rw [show associatedDiagonal w N k j = 0 from if_neg hkj,mul_zero]
    · rw [show associatedDiagonal w M i k = 0 from if_neg hik,zero_mul]

theorem associatedDiagonal_eq_one_iff (w : I → ℤ) (M : Matrix I I K)
    (hM : M.BlockTriangular (fun i => -w i)) :
    associatedDiagonal w M = 1 ↔
      ∀ i j, w i ≤ w j → M i j = (1 : Matrix I I K) i j := by
  constructor
  · intro h i j hij
    by_cases he : w i = w j
    · have hv := congrArg (fun A : Matrix I I K => A i j) h
      simpa only [associatedDiagonal,if_pos he] using hv
    · have hlt : w i < w j := lt_of_le_of_ne hij he
      have hne : i ≠ j := fun h => he (congrArg w h)
      rw [hM (show -w j < -w i by omega),Matrix.one_apply,if_neg hne]
  · intro h
    ext i j
    by_cases he : w i = w j
    · exact (if_pos he).trans (h i j he.le)
    · have hne : i ≠ j := fun h => he (congrArg w h)
      simp only [associatedDiagonal,if_neg he,Matrix.one_apply,if_neg hne]

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixAssociatedDiagonal
