import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! Exact multiplication of row-monomial matrices. Both the permutation
order and the transported nonzero row coefficient are explicit. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGMonomialProductCoordinates
open CFSGTypeAMonomialMatrices
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem monomial_mul (σ τ : Equiv.Perm I) (d e : I → K) :
    monomial σ d * monomial τ e =
      monomial (τ * σ) (fun i => d i * e (σ i)) := by
  ext i j
  simp only [Matrix.mul_apply, monomial_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp only [if_pos rfl, Equiv.Perm.mul_apply]
    split_ifs <;> simp
  · intro k _ hk
    simp only [if_neg (Ne.symm hk), zero_mul]
  · intro hk
    exact False.elim (hk (Finset.mem_univ (σ i)))

end SymmetricSubgroupAsymptotics.CFSGMonomialProductCoordinates
