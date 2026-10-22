import SymmetricSubgroupAsymptotics.CFSGMonomialUnitCoordinates

/-! Strict grading support transported by an actual monomial unit.
The coefficient is retained and only its support is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGMonomialWeightedSupport
open CFSGTypeAMonomialMatrices
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem conjugation_single_zero (weight : I → ℤ) (W : (Matrix I I K)ˣ)
    (σ : Equiv.Perm I) (d : I → K) (hW : (W : Matrix I I K) = monomial σ d)
    (hd : ∀ i, d i ≠ 0) (a b : I) (c : K)
    (hab : weight (σ.symm b) < weight (σ.symm a))
    (x y : I) (hxy : weight x ≤ weight y) :
    ((W : Matrix I I K) * Matrix.single a b c * (↑(W⁻¹) : Matrix I I K)) x y = 0 := by
  have hz : Matrix.single (σ.symm a) (σ.symm b) (1 : K) x y = 0 := by
    apply Matrix.single_apply_of_ne
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_ge hxy) hab
  have hc : Matrix.single a b c = c • Matrix.single a b (1 : K) := by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hc, mul_smul_comm, smul_mul_assoc,
    CFSGMonomialUnitCoordinates.conjugation_single W σ d hW a b (hd _)]
  simp only [Matrix.smul_apply, hz, smul_zero]

end SymmetricSubgroupAsymptotics.CFSGMonomialWeightedSupport
