import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Ring.Defs

/-! Nilpotence transport through an ACTUAL algebra-unit conjugation,
using semiconjugation powers. No inverse on the ambient ring is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGUnitConjugationNilpotence
variable {R : Type*} [Ring R]

theorem pow_eq_zero_of_conjugate (u : Rˣ) (x y : R)
    (h : (u:R)*x*((u⁻¹:Rˣ):R)=y) (n : ℕ) (hx : x^n=0) : y^n=0 := by
  have hc : SemiconjBy (u:R) x y := by
    have hh := congrArg (fun z : R=>z*(u:R)) h
    simpa only [mul_assoc,Units.inv_mul,mul_one] using hh
  have hh := hc.pow_right n
  change (u:R)*x^n=y^n*(u:R) at hh
  rw [hx,mul_zero] at hh
  have hp := congrArg (fun z : R=>z*((u⁻¹:Rˣ):R)) hh.symm
  simpa only [mul_assoc,Units.mul_inv,mul_one,zero_mul] using hp

end SymmetricSubgroupAsymptotics.CFSGUnitConjugationNilpotence
