import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
import Mathlib.Data.Matrix.Cartan

/-! The actual symplectic simple positive/negative matrices satisfy the
mixed EF relations. The Cartan convention agrees with the pinned C model. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_negative_of_ne (i j : Fin r) (hij : i ≠ j) :
    ⁅positive R r i, negative R r j⁆ = 0 := by
  by_cases hi : i.val + 1 < r
  · by_cases hj : j.val + 1 < r
    · have hnext : (⟨i.val + 1, hi⟩ : Fin r) ≠ ⟨j.val + 1, hj⟩ := by
        intro he
        apply hij
        apply Fin.ext
        have hv := congrArg Fin.val he
        change i.val + 1 = j.val + 1 at hv
        omega
      simp [positive, negative, hi, hj, Ring.lie_def, Matrix.transpose_sub,
        Matrix.transpose_single, sub_mul, mul_sub, hij, hij.symm, hnext, hnext.symm]
    · simp [positive, negative, hi, hj, Ring.lie_def,
        Matrix.transpose_single, sub_mul, mul_sub, hij, hij.symm]
  · by_cases hj : j.val + 1 < r
    · simp [positive, negative, hi, hj, Ring.lie_def, Matrix.transpose_sub,
        Matrix.transpose_single, sub_mul, mul_sub, hij, hij.symm]
    · simp [positive, negative, hi, hj, Ring.lie_def, Matrix.transpose_single, hij, hij.symm]

theorem EF (i j : Fin r) :
    ⁅positive R r i, negative R r j⁆ = if i = j then cartan R r i else 0 := by
  by_cases hij : i = j
  · subst j
    exact (if_pos rfl).symm
  · rw [if_neg hij]
    exact positive_negative_of_ne R r i j hij

theorem typeC_transpose (r : ℕ) : (CartanMatrix.C r).transpose = CartanMatrix.B r := by
  apply Matrix.ext
  intro i j
  change CartanMatrix.C r j i = CartanMatrix.B r i j
  by_cases he : i = j
  · subst j
    simp [CartanMatrix.C, CartanMatrix.B]
  · have her : j ≠ i := Ne.symm he
    simp only [CartanMatrix.C, CartanMatrix.B, Matrix.of_apply, if_neg he, if_neg her]
    by_cases hij : i.val + 1 = j.val
    · have hji : ¬j.val + 1 = i.val := by omega
      simp only [if_pos hij, if_neg hji]
    · by_cases hji : j.val + 1 = i.val
      · simp only [if_neg hij, if_pos hji]
      · simp only [if_neg hij, if_neg hji]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
