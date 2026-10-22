import SymmetricSubgroupAsymptotics.CFSGSymplecticFormPreservation
import Mathlib.Data.Matrix.Basis

/-! A unit-diagonal block-upper matrix centralizing all coordinate
long-root directions is an upper shear. Form preservation then forces
the same remaining block to be symmetric. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem upper_of_diagonal_long_commutation (n : ℕ) (A : Mat K n)
    (hL : ∀ i j, A (Sum.inr i) (Sum.inl j) = 0)
    (hdiag : ∀ i, A i i = 1)
    (hcomm : ∀ i : Fin n,
      A * Matrix.single (Sum.inl i) (Sum.inr i) 1 =
        Matrix.single (Sum.inl i) (Sum.inr i) 1 * A) :
    A = Matrix.fromBlocks 1 (A.submatrix Sum.inl Sum.inr) 0 1 := by
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      change A (Sum.inl i) (Sum.inl j) = (1 : Matrix (Fin n) (Fin n) K) i j
      by_cases hij : i = j
      · subst j; rw [hdiag, Matrix.one_apply_eq]
      · have he := congrArg (fun M : Mat K n => M (Sum.inl i) (Sum.inr j)) (hcomm j)
        dsimp only at he
        rw [Matrix.mul_single_apply_same,
          Matrix.single_mul_apply_of_ne 1 _ _ _ _ (by simpa using hij), mul_one] at he
        simpa only [Matrix.one_apply, if_neg hij] using he
    | inr j => rfl
  | inr i =>
    cases y with
    | inl j => exact hL i j
    | inr j =>
      change A (Sum.inr i) (Sum.inr j) = (1 : Matrix (Fin n) (Fin n) K) i j
      by_cases hij : i = j
      · subst j; rw [hdiag, Matrix.one_apply_eq]
      · have he := congrArg (fun M : Mat K n => M (Sum.inl i) (Sum.inr j)) (hcomm i)
        dsimp only at he
        rw [Matrix.mul_single_apply_of_ne 1 _ _ _ _ (by simpa using Ne.symm hij),
          Matrix.single_mul_apply_same, one_mul] at he
        simpa only [Matrix.one_apply, if_neg hij] using he.symm

theorem upperShear_symmetric_of_form (n : ℕ) (B : Matrix (Fin n) (Fin n) K)
    (h : Matrix.fromBlocks 1 B 0 1 * Matrix.J (Fin n) K *
      (Matrix.fromBlocks 1 B 0 1).transpose = Matrix.J (Fin n) K) : B.IsSymm := by
  have he := congrArg Matrix.toBlocks₁₁ h
  simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
    one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, Matrix.mul_neg, neg_mul, neg_zero] at he
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)).symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
