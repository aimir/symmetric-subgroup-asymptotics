import Mathlib.Algebra.Group.Units.Basic

/-! Unit conjugation fixes an element exactly when the two commute. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGUnitConjugation

theorem fix_iff_commute {R : Type*} [Monoid R] (u : Rˣ) (x : R) :
    (u:R)*x*(↑(u⁻¹):R)=x↔(u:R)*x=x*(u:R) := by
  constructor
  · intro h
    have hh := congrArg (fun y : R => y*(u:R)) h
    simpa only [mul_assoc,Units.inv_mul,mul_one] using hh
  · intro h
    rw [h,mul_assoc,Units.mul_inv,mul_one]

end SymmetricSubgroupAsymptotics.CFSGUnitConjugation
