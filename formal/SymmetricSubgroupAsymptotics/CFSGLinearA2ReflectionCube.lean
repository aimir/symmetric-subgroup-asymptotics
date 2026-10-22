import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module

/-! The A2 reflection cube on two distinguished Cartan columns and any
additional column. All coefficients remain in the given coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGLinearA2ReflectionCube
variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

theorem cube (q t : Module.End K M) (x u v : M) (a b : K)
    (hqx : q x=x-a • u) (hqu : q u= -u) (hqv : q v=v-u)
    (htx : t x=x-b • v) (htu : t u=u-v) (htv : t v= -v) :
    ((q*t)^3) x=x := by
  simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
    map_sub,map_neg,map_smul,hqx,hqu,hqv,htx,htu,htv]
  module

end SymmetricSubgroupAsymptotics.CFSGLinearA2ReflectionCube
