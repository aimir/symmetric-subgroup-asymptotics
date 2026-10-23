import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel

/-! A division-free multiplication identity for two quadratic root
polynomials. The three mixed products are actual algebra equalities. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootOrthogonalProduct
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

theorem polynomial_product (e f d h : B)
    (heh : e*h=0) (hdf : d*f=0) (hdh : d*h=0) (t : R) :
    (1+t • e+t^2 • d)*(1+t • f+t^2 • h)=
      1+t • (e+f)+t^2 • (d+h+e*f) := by
  simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,
    mul_smul_comm,smul_smul,heh,hdf,hdh,smul_zero,add_zero,
    smul_add,pow_two]
  abel

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootOrthogonalProduct
