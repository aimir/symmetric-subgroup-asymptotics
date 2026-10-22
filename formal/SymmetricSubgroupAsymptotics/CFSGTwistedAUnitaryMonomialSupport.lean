import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMonomialEntries

/-! Two-axis displacement support is transported by the actual monomial
permutation, retaining its nonzero row weights. This statement applies to
arbitrary matrix units, without a classical-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport
open CFSGTypeAMonomialMatrices
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem inverse_monomial_conjugation_support
    (W : (Matrix I I K)ˣ) (sigma : Equiv.Perm I) (d : I → K)
    (hW : (W : Matrix I I K) = monomial sigma d) (hd : ∀ i, d i ≠ 0)
    (R : Matrix I I K) (a b : I)
    (hdiag : ∀ i, R i i = 1)
    (hR : ∀ i j, i ≠ a → j ≠ b → R i j = (1 : Matrix I I K) i j) :
    ∀ i j, i ≠ sigma a → j ≠ sigma b →
      ((↑(W⁻¹) : Matrix I I K) * R * (W : Matrix I I K)) i j =
        (1 : Matrix I I K) i j := by
  intro i j hi hj
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply, if_pos rfl]
    exact inverse_monomial_conjugation_diag_one W sigma d hW hd R hdiag i
  · let S := (↑(W⁻¹) : Matrix I I K) * R * (W : Matrix I I K)
    have hs : (W : Matrix I I K) * S * (↑(W⁻¹) : Matrix I I K) = R := by
      dsimp only [S]
      calc
        _ = ((W : Matrix I I K) * (↑(W⁻¹) : Matrix I I K)) * R *
            ((W : Matrix I I K) * (↑(W⁻¹) : Matrix I I K)) := by
              simp only [mul_assoc]
        _ = R := by rw [Units.mul_inv, one_mul, mul_one]
    have hai : sigma.symm i ≠ a := by
      intro he
      apply hi
      simpa only [sigma.apply_symm_apply] using congrArg sigma he
    have hbj : sigma.symm j ≠ b := by
      intro he
      apply hj
      simpa only [sigma.apply_symm_apply] using congrArg sigma he
    have hne : sigma.symm i ≠ sigma.symm j := fun he => hij (sigma.symm.injective he)
    have hr := hR (sigma.symm i) (sigma.symm j) hai hbj
    rw [Matrix.one_apply, if_neg hne] at hr
    have he := monomial_conjugation_entries W sigma d hW hd S (sigma.symm i) (sigma.symm j)
    rw [hs, hr, sigma.apply_symm_apply, sigma.apply_symm_apply] at he
    have hz : S i j = 0 := by
      have hm : d (sigma.symm i) * S i j = 0 :=
        (div_eq_zero_iff.mp he.symm).resolve_right (hd _)
      exact (mul_eq_zero.mp hm).resolve_left (hd _)
    change S i j = _
    rw [hz, Matrix.one_apply, if_neg hij]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport
