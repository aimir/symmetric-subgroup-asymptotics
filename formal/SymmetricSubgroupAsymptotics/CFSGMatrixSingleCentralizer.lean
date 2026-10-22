import Mathlib.Data.Matrix.Basis

/-! Commutation with a literal matrix unit controls its entire column
and row. These entry lemmas retain the original matrix. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixSingleCentralizer
variable {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]

theorem column_eq_single (A : Matrix I I K) (i j : I)
    (h : A * Matrix.single i j 1 = Matrix.single i j 1 * A) (hd : A j j = 1) (x : I) :
    A x i = if x = i then 1 else 0 := by
  have he := congrArg (fun M : Matrix I I K => M x j) h
  dsimp only at he
  by_cases hx : x = i
  · subst x
    simpa only [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same,
      mul_one, one_mul, hd, if_pos rfl] using he
  · rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne 1 i j x j hx,
      mul_one] at he
    simpa only [if_neg hx] using he

theorem row_eq_single (A : Matrix I I K) (i j : I)
    (h : A * Matrix.single i j 1 = Matrix.single i j 1 * A) (hd : A i i = 1) (x : I) :
    A j x = if x = j then 1 else 0 := by
  have he := congrArg (fun M : Matrix I I K => M i x) h
  dsimp only at he
  by_cases hx : x = j
  · subst x
    simpa only [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same,
      mul_one, one_mul, hd, if_pos rfl] using he.symm
  · rw [Matrix.mul_single_apply_of_ne 1 i j i x hx,
      Matrix.single_mul_apply_same, one_mul] at he
    simpa only [if_neg hx] using he.symm

end SymmetricSubgroupAsymptotics.CFSGMatrixSingleCentralizer
