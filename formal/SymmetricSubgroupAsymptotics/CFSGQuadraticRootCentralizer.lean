import Mathlib.Data.Matrix.Basis

/-! Recover the true linear root from its quadratic unipotent in odd
characteristic. The quadratic coefficient is retained and cancelled
through the square of the unipotent minus one. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootCentralizer
variable {K : Type*} [Field K] {I : Type*} [Fintype I] [DecidableEq I]

theorem commutes_linear_of_commutes_quadratic (h2 : (2 : K) ≠ 0)
    (A E D : Matrix I I K) (he : E * E = D + D)
    (hed : E * D = 0) (hde : D * E = 0) (hdd : D * D = 0)
    (hU : A * (1 + E + D) = (1 + E + D) * A) : A * E = E * A := by
  have hsum : A * E + A * D = E * A + D * A := by
    apply add_left_cancel (a := A)
    simpa only [mul_add, add_mul, mul_one, one_mul, add_assoc] using hU
  have hN : A * (E + D) = (E + D) * A := by
    simpa only [mul_add, add_mul] using hsum
  have hN2 : A * ((E + D) * (E + D)) = ((E + D) * (E + D)) * A := by
    rw [← mul_assoc, hN, mul_assoc, hN, ← mul_assoc]
  have hNN : (E + D) * (E + D) = D + D := by
    simp only [mul_add, add_mul, he, hed, hde, hdd, zero_add, add_zero]
  rw [hNN] at hN2
  have hD : A * D = D * A := by
    ext i j
    have hh := congrArg (fun M : Matrix I I K => M i j) hN2
    simp only [mul_add, add_mul, Pi.add_apply] at hh
    apply mul_left_cancel₀ h2
    simpa only [two_mul] using hh
  rw [hD] at hsum
  exact add_right_cancel hsum

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootCentralizer
