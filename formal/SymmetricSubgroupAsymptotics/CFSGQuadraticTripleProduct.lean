import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Module

/-! The ordered product of three quadratic root polynomials has a
literal cubic coefficient. All coefficients are integral expressions;
no factorial is inverted and the formula works in every characteristic.
The vanishing cross-products will be supplied by actual lattice degrees. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticTripleProduct
variable {K R : Type*} [CommRing K] [Ring R] [Algebra K R]

def value (e d : R) (t : K) : R := 1+t • e+t^2 • d

theorem product_three (e f g d h k : R) (t : K)
    (heh : e*h=0) (hdf : d*f=0) (hdh : d*h=0)
    (hek : e*k=0) (hfk : f*k=0) (hdg : d*g=0) (hhg : h*g=0)
    (hdk : d*k=0) (hhk : h*k=0) :
    value e d t*value f h t*value g k t=
      1+t • (e+f+g)+t^2 • (d+h+k+e*f+e*g+f*g)+t^3 • (e*f*g) := by
  have hefk : (e*f)*k=0 := by rw [mul_assoc,hfk,mul_zero]
  simp only [value,add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
    smul_smul,heh,hdf,hdh,hek,hfk,hdg,hhg,hdk,hhk,hefk,
    smul_zero,zero_mul,mul_zero,zero_add,add_zero,smul_add]
  module

end SymmetricSubgroupAsymptotics.CFSGQuadraticTripleProduct
