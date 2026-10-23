import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! A genuine graded matrix unit transports strict triangularity to the
transported grading. This tracks literal integer weights, independently
of their images in the coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixTransportStrict
open CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups
variable {I W K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem conjugate_mem_strict (ell : I → W) (height : W → ℤ) (e : W ≃ W)
    (p : (Matrix I I K)ˣ)
    (hp : Supported ell e (p : Matrix I I K))
    (hpi : Supported ell e.symm (↑(p⁻¹) : Matrix I I K))
    (u : (Matrix I I K)ˣ) (hu : u ∈ strictUnits (fun i => height (ell i))) :
    p * u * p⁻¹ ∈ strictUnits (fun i => height (e.symm (ell i))) := by
  have hu' : ∀ i j, height (ell i) ≤ height (ell j) →
      (u : Matrix I I K) i j = (1 : Matrix I I K) i j := hu
  intro i j hij
  have hz : ((p : Matrix I I K) * ((u : Matrix I I K) - 1) *
      (↑(p⁻¹) : Matrix I I K)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : ell l = e.symm (ell j)
    · have hinner : ((p : Matrix I I K) * ((u : Matrix I I K) - 1)) i l = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : ell i = e (ell k)
        · have hk' : e.symm (ell i) = ell k :=
            (congrArg e.symm hk).trans (e.symm_apply_apply (ell k))
          have hkl : height (ell k) ≤ height (ell l) := by
            simpa only [hk', ← hl] using hij
          rw [Matrix.sub_apply, hu' k l hkl, sub_self, mul_zero]
        · rw [hp i k hk, zero_mul]
      rw [hinner, zero_mul]
    · rw [hpi l j hl, mul_zero]
  have hpq : (p : Matrix I I K) * (↑(p⁻¹) : Matrix I I K) = 1 := Units.mul_inv p
  have hd : (p : Matrix I I K) * ((u : Matrix I I K) - 1) *
      (↑(p⁻¹) : Matrix I I K) =
      (p : Matrix I I K) * (u : Matrix I I K) * (↑(p⁻¹) : Matrix I I K) - 1 := by
    rw [mul_sub, sub_mul, mul_one, hpq]
  rw [hd, Matrix.sub_apply] at hz
  exact sub_eq_zero.mp hz

theorem entry_eq_one_of_nonpositive_degree (ell : I → W) (height : W → ℤ)
    (u : (Matrix I I K)ˣ) (hu : u ∈ strictUnits (fun i => height (ell i)))
    (i j : I) (hij : height (ell i) ≤ height (ell j)) :
    (u : Matrix I I K) i j = (1 : Matrix I I K) i j := hu i j hij

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixTransportStrict
