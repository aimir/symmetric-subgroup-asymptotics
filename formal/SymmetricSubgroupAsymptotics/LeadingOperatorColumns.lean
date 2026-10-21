import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Pi

/-! Column certificates for genuine leading-term operators.

Only the columns at or below the original leading index matter. Thus an
arbitrary lower-layer affine error is allowed when the desired leading
term remains in the upper layer. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.LeadingOperatorColumns

variable {k : Type} [Field k] {n : ℕ}

theorem apply_eq_sum_columns (T : (Fin n → k) →ₗ[k] (Fin n → k))
    (v : Fin n → k) (i : Fin n) :
    T v i = ∑ j : Fin n, v j * T (Pi.single j 1) i := by
  classical
  calc
    T v i = T (∑ j : Fin n, v j • (Pi.single j 1 : Fin n → k)) i :=
      congrArg (fun z : Fin n → k => T z i) (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]

theorem hasLeading_apply_of_columns
    (T : (Fin n → k) →ₗ[k] (Fin n → k)) (v : Fin n → k) (a b : Fin n)
    (hv : FiniteRowLeadingWeight.HasLeading v a)
    (hdiag : T (Pi.single a 1) b ≠ 0)
    (hrow : ∀ j, j < a → T (Pi.single j 1) b = 0)
    (habove : ∀ c, b < c → ∀ j, j ≤ a → T (Pi.single j 1) c = 0) :
    FiniteRowLeadingWeight.HasLeading (T v) b := by
  classical
  have he : T v b = v a * T (Pi.single a 1) b := by
    rw [apply_eq_sum_columns]
    apply Finset.sum_eq_single a
    · intro j _ hja
      rcases lt_or_gt_of_ne hja with hj | hj
      · rw [hrow j hj, mul_zero]
      · rw [hv.2 j hj, zero_mul]
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  refine ⟨?_, ?_⟩
  · rw [he]
    exact mul_ne_zero hv.1 hdiag
  · intro c hc
    rw [apply_eq_sum_columns]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ≤ a
    · rw [habove c hc j hj, mul_zero]
    · rw [hv.2 j (lt_of_not_ge hj), zero_mul]

end SymmetricSubgroupAsymptotics.LeadingOperatorColumns
