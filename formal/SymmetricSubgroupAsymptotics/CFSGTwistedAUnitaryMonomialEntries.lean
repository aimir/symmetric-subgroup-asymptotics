import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! General conjugation entries for actual matrix units with a literal
monomial value. This preserves all row weights and proves diagonal1
preservation in both conjugation directions, without a group-recognition
or root-generator premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport
open CFSGTypeAMonomialMatrices
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem monomial_conjugation_entries (W : (Matrix I I K)ˣ) (sigma : Equiv.Perm I)
    (d : I → K) (hW : (W : Matrix I I K) = monomial sigma d) (hd : ∀ i, d i ≠ 0)
    (R : Matrix I I K) (i j : I) :
    ((W : Matrix I I K) * R * (↑(W⁻¹) : Matrix I I K)) i j =
      d i * R (sigma i) (sigma j) / d j := by
  let M : Matrix I I K := fun i j => d i * R (sigma i) (sigma j) / d j
  have hl (i j : I) : (monomial sigma d * R) i j = d i * R (sigma i) j := by
    simp [Matrix.mul_apply, monomial_apply, ite_mul]
  have hr (i j : I) : (M * monomial sigma d) i j = M i (sigma.symm j) * d (sigma.symm j) := by
    simp only [Matrix.mul_apply, monomial_apply, mul_ite, sigma.apply_eq_iff_eq_symm_apply]
    simp
  have hm : (W : Matrix I I K) * R = M * (W : Matrix I I K) := by
    rw [hW]
    ext a b
    rw [hl, hr]
    dsimp only [M]
    rw [sigma.apply_symm_apply, div_mul_cancel₀ _ (hd _)]
  have he := congrArg (fun A : Matrix I I K => A * (↑(W⁻¹) : Matrix I I K)) hm
  have he' : (W : Matrix I I K) * R * (↑(W⁻¹) : Matrix I I K) = M := by
    simpa only [mul_assoc, Units.mul_inv, mul_one] using he
  exact congrArg (fun A : Matrix I I K => A i j) he'

theorem monomial_conjugation_diag (W : (Matrix I I K)ˣ) (sigma : Equiv.Perm I)
    (d : I → K) (hW : (W : Matrix I I K) = monomial sigma d) (hd : ∀ i, d i ≠ 0)
    (R : Matrix I I K) (i : I) :
    ((W : Matrix I I K) * R * (↑(W⁻¹) : Matrix I I K)) i i = R (sigma i) (sigma i) := by
  rw [monomial_conjugation_entries W sigma d hW hd]
  exact mul_div_cancel_left₀ _ (hd i)

theorem inverse_monomial_conjugation_diag_one (W : (Matrix I I K)ˣ) (sigma : Equiv.Perm I)
    (d : I → K) (hW : (W : Matrix I I K) = monomial sigma d) (hd : ∀ i, d i ≠ 0)
    (R : Matrix I I K) (hR : ∀ i, R i i = 1) :
    ∀ i, ((↑(W⁻¹) : Matrix I I K) * R * (W : Matrix I I K)) i i = 1 := by
  intro i
  let S := (↑(W⁻¹) : Matrix I I K) * R * (W : Matrix I I K)
  have hs : (W : Matrix I I K) * S * (↑(W⁻¹) : Matrix I I K) = R := by
    dsimp only [S]
    calc
      _ = ((W : Matrix I I K) * (↑(W⁻¹) : Matrix I I K)) * R *
        ((W : Matrix I I K) * (↑(W⁻¹) : Matrix I I K)) := by simp only [mul_assoc]
      _ = R := by rw [Units.mul_inv, one_mul, mul_one]
  have hh := monomial_conjugation_diag W sigma d hW hd S (sigma.symm i)
  rw [hs, sigma.apply_symm_apply, hR] at hh
  exact hh.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport
