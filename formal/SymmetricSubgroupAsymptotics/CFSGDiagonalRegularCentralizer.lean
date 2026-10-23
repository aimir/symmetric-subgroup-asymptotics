import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Field.Defs

/-! A diagonal matrix commuting with one regular upper matrix is
scalar. This entrywise statement is independent of any group realization. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.CFSGDiagonalRegularCentralizer
variable {K : Type*} [Field K] {r : ℕ}

theorem scalar_of_diagonal_regular (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hoff : ∀ i j, i ≠ j → A i j = 0)
    (hregular : ∀ i : Fin r, B i.castSucc i.succ ≠ 0)
    (hcomm : A * B = B * A) : ∃ c : K, A = c • 1 := by
  have hdiag : A = Matrix.diagonal (fun i => A i i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ h, hoff i j h]
  have hstep (i : Fin r) : A i.castSucc i.castSucc = A i.succ i.succ := by
    have hh := congrArg (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) K =>
      M i.castSucc i.succ) hcomm
    dsimp only at hh
    rw [hdiag, Matrix.diagonal_mul, Matrix.mul_diagonal] at hh
    change A i.castSucc i.castSucc * B i.castSucc i.succ =
      B i.castSucc i.succ * A i.succ i.succ at hh
    exact mul_right_cancel₀ (hregular i) (hh.trans (mul_comm _ _))
  have hconstant (i : Fin (r + 1)) : A i i = A 0 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i hi => exact (hstep i).symm.trans hi
  refine ⟨A 0 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hconstant i
  · simp only [hoff i j hij, Matrix.smul_apply, Matrix.one_apply_ne hij,
      smul_eq_mul, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGDiagonalRegularCentralizer
