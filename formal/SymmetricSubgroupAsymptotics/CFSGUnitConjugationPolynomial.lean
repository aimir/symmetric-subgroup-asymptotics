import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Field.Rat

/-! Exact powers and quadratic polynomials under unit conjugation in
the SAME possibly noncommutative algebra. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem conjugate_pow (u : Rˣ) (x y : R)
    (h : (u:R)*x*((u⁻¹:Rˣ):R)=y) (n : ℕ) :
    (u:R)*x^n*((u⁻¹:Rˣ):R)=y^n := by
  have hc : SemiconjBy (u:R) x y := by
    have hh := congrArg (fun z : R=>z*(u:R)) h
    simpa only [mul_assoc,Units.inv_mul,mul_one] using hh
  have hh := congrArg (fun z : R=>z*((u⁻¹:Rˣ):R)) (hc.pow_right n)
  simpa only [mul_assoc,Units.mul_inv,mul_one] using hh

theorem conjugate_quadratic (u : Rˣ) (x y : R)
    (h : (u:R)*x*((u⁻¹:Rˣ):R)=y) (a : ℚ) :
    (u:R)*(1+a • x+(a^2/2) • x^2)*((u⁻¹:Rˣ):R)=
      1+a • y+(a^2/2) • y^2 := by
  have h2 := conjugate_pow u x y h 2
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one,Units.mul_inv,h,h2]

end SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
