import SymmetricSubgroupAsymptotics.CFSGIntegralQuadraticRootOperators
import Mathlib.Algebra.Group.Units.Basic

/-! The actual integral quadratic polynomial and its inverse define a
unit over every coefficient ring, without dividing by two. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential
open CFSGIntegralQuadraticRootOperators
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

theorem mul_inverse (e d : B) (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0) (hdd : d*d=0)
    (t : R) : exponential R e d t*exponential R e d (-t)=1 := by
  simp only [exponential,pow_two,neg_mul,mul_neg,neg_neg,neg_smul,add_mul,mul_add,
    one_mul,mul_one,smul_mul_assoc,mul_smul_comm,smul_smul,
    he,hed,hde,hdd,smul_zero,smul_add,add_zero,zero_add,mul_assoc,smul_neg]
  abel

theorem inverse_mul (e d : B) (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0) (hdd : d*d=0)
    (t : R) : exponential R e d (-t)*exponential R e d t=1 := by
  simpa only [neg_neg] using mul_inverse e d he hed hde hdd (-t)

def rootUnit (e d : B) (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0) (hdd : d*d=0)
    (t : R) : Bˣ where
  val := exponential R e d t
  inv := exponential R e d (-t)
  val_inv := mul_inverse e d he hed hde hdd t
  inv_val := inverse_mul e d he hed hde hdd t

@[simp] theorem rootUnit_val (e d : B) (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0) (hdd : d*d=0)
    (t : R) : (rootUnit e d he hed hde hdd t : B)=1+t • e+t^2 • d := rfl
@[simp] theorem rootUnit_inv_val (e d : B) (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0) (hdd : d*d=0)
    (t : R) : (↑((rootUnit e d he hed hde hdd t)⁻¹):B)=1-t • e+t^2 • d := by
  change exponential R e d (-t)=_
  simp only [exponential,neg_smul,neg_sq,sub_eq_add_neg]

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential
