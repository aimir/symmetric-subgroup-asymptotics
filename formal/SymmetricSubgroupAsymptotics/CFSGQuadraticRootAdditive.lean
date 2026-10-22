import SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! The actual integral quadratic polynomial is additive in its root
parameter. No characteristic restriction or divided-by-two coefficient
is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential
open CFSGIntegralQuadraticRootOperators
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

theorem exponential_add (e d : B) (he : e*e=d+d) (hed : e*d=0)
    (hde : d*e=0) (hdd : d*d=0) (t u : R) :
    exponential R e d t*exponential R e d u=exponential R e d (t+u) := by
  simp only [exponential,add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,
    mul_smul_comm,smul_smul,he,hed,hde,hdd,smul_zero,smul_add,add_zero,zero_add]
  module

theorem rootUnit_add (e d : B) (he : e*e=d+d) (hed : e*d=0)
    (hde : d*e=0) (hdd : d*d=0) (t u : R) :
    rootUnit e d he hed hde hdd t*rootUnit e d he hed hde hdd u=
      rootUnit e d he hed hde hdd (t+u) := by
  apply Units.ext
  exact exponential_add e d he hed hde hdd t u

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential
