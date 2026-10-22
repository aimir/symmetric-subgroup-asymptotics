import SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationNilpotence
import SymmetricSubgroupAsymptotics.CFSGPairSubalgebraQuadraticExponentials

/-! Two-parameter collecting inside the SAME noncommutative algebra.
Every cubic identity is recovered from a genuine unit conjugation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticParameterizedCollecting
open CFSGUnitConjugationPolynomial CFSGUnitConjugationNilpotence
variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem conjugate_scaled_difference (u w : Rˣ) (x y : R) (hc : Commute x y)
    (hx : x^3=0) (t a : ℚ)
    (hplus : (u:R)*x*((u⁻¹:Rˣ):R)=x+t • y)
    (hweyl : (w:R)*x*((w⁻¹:Rˣ):R)=y) :
    (u:R)*(1+a • x+(a^2/2) • x^2)*((u⁻¹:Rˣ):R)*
      (1+(-a) • x+((-a)^2/2) • x^2)=
    (w:R)*(1+(a*t) • x+((a*t)^2/2) • x^2)*((w⁻¹:Rˣ):R) := by
  have hy : y^3=0 := pow_eq_zero_of_conjugate w x y hweyl 3 hx
  have hty : (t • y)^3=0 := by rw [smul_pow,hy,smul_zero]
  have hsum : (x+t • y)^3=0 := pow_eq_zero_of_conjugate u x _ hplus 3 hx
  have hpolyU := conjugate_quadratic u x (x+t • y) hplus a
  have hpolyW := conjugate_quadratic w x y hweyl (a*t)
  rw [hpolyU,hpolyW]
  have hh := CFSGPairSubalgebraQuadraticExponentials.product_difference_of_commute
    x (t • y) (hc.smul_right t) hx hty hsum a
  have hscale : 1+a • (t • y)+(a^2/2) • (t • y)^2=
      1+(a*t) • y+((a*t)^2/2) • y^2 := by
    simp only [smul_smul,smul_pow]
    rw [show (a^2/2)*t^2=(a*t)^2/2 by ring]
  rw [hscale] at hh
  simpa only [neg_smul,smul_neg,neg_sq] using hh

end SymmetricSubgroupAsymptotics.CFSGQuadraticParameterizedCollecting
