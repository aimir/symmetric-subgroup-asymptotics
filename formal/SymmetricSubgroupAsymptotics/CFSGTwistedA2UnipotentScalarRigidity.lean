import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
import SymmetricSubgroupAsymptotics.CFSGStrictUpperNilpotence
import SymmetricSubgroupAsymptotics.CFSGMatrixCubicUnipotentScalar

/-! Projective conjugacy between two actual upper-unipotent arrays has
scalar one, including characteristic three. Nilpotence, rather than a
trace division, removes the projective ambiguity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices
variable {K : Type} [Field K] (σ : K ≃+* K)

theorem upperArray_upper (a b : K) : (upperArray σ a b).BlockTriangular id := by
  intro i j hji
  fin_cases i <;> fin_cases j <;> simp_all [upperArray]

theorem upperArray_diagonal (a b : K) (i : Fin 3) : upperArray σ a b i i = 1 := by
  fin_cases i <;> simp [upperArray]

theorem upperArray_shift_strict (a b : K) :
    ∀ i j : Fin 3, j ≤ i → (upperArray σ a b - 1) i j = 0 := by
  intro i j hji
  by_cases he : j = i
  · subst j
    simp only [Matrix.sub_apply, upperArray_diagonal, Matrix.one_apply_eq, sub_self]
  · have hlt : j < i := lt_of_le_of_ne hji he
    simp only [Matrix.sub_apply, upperArray_upper σ a b hlt,
      Matrix.one_apply, if_neg (Ne.symm he), sub_zero]

theorem upperArray_shift_cube (a b : K) : (upperArray σ a b - 1) ^ 3 = 0 :=
  CFSGStrictUpperNilpotence.pow_dimension_eq_zero _ (upperArray_shift_strict σ a b)

theorem upperArray_scalar_of_conjugate (a b c d : K) (M : (Mat K 2)ˣ) (s : K)
    (he : (M : Mat K 2) * upperArray σ a b * (↑(M⁻¹) : Mat K 2) = s • upperArray σ c d) :
    s = 1 := by
  let X := upperArray σ a b - 1
  let Y := upperArray σ c d - 1
  have hX : X ^ 3 = 0 := upperArray_shift_cube σ a b
  have hY : Y ^ 3 = 0 := upperArray_shift_cube σ c d
  have hXsum : 1 + X = upperArray σ a b := by dsimp only [X]; abel
  have hYsum : 1 + Y = upperArray σ c d := by dsimp only [Y]; abel
  have hdiag : Y (0 : Fin 3) 0 = 0 := upperArray_shift_strict σ c d _ _ le_rfl
  have hdiag2 : (Y * Y) (0 : Fin 3) 0 = 0 := by
    have h := CFSGStrictUpperNilpotence.pow_entry_eq_zero Y
      (upperArray_shift_strict σ c d) 2 (0 : Fin 3) 0 (by decide)
    simpa only [pow_two] using h
  have hn := CFSGMatrixCubicUnipotentScalar.conjugate_shift_cube_zero X hX M
  rw [hXsum, he] at hn
  apply CFSGMatrixCubicUnipotentScalar.scalar_shift_cube_zero Y hY 0 hdiag hdiag2 s
  rw [hYsum]
  exact hn

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
