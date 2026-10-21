import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction

/-! Every original matrix coordinate has exact monomial conjugation,
including its nonzero weight. No determinant or named-group equality
is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonomialUnitCoordinates
open CFSGTypeAMonomialMatrices CFSGTypeAMonomialRootAction
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]

theorem conjugation_single (W : (Matrix I I K)ˣ) (σ : Equiv.Perm I) (d : I → K)
    (hW : (W : Matrix I I K) = monomial σ d) (i j : I) (hd : d (σ.symm j) ≠ 0) :
    (W : Matrix I I K) * Matrix.single i j 1 * (↑(W⁻¹) : Matrix I I K) =
      (d (σ.symm i) / d (σ.symm j)) • Matrix.single (σ.symm i) (σ.symm j) 1 := by
  have hm := monomial_mul_transvection σ d i j (1 : K) hd
  rw [← hW] at hm
  simp only [mul_one] at hm
  have hc := congrArg (fun A : Matrix I I K => A * (↑(W⁻¹) : Matrix I I K)) hm
  have hh : (1 : Matrix I I K) +
      (W : Matrix I I K) * Matrix.single i j 1 * (↑(W⁻¹) : Matrix I I K) =
      1 + Matrix.single (σ.symm i) (σ.symm j) (d (σ.symm i) / d (σ.symm j)) := by
    simpa only [Matrix.transvection, mul_add, add_mul, mul_one, one_mul, mul_assoc, Units.mul_inv] using hc
  have he := add_left_cancel hh
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using he

end SymmetricSubgroupAsymptotics.CFSGMonomialUnitCoordinates
