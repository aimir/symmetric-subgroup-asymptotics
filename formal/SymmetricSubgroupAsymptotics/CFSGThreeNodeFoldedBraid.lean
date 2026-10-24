import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Tactic.Group

/-! Small group identities for folding an A3 chain at its two commuting
end nodes. No representation, root-group recognition or finite census is
used in this symbolic braid calculation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGThreeNodeFoldedBraid
variable {G : Type*} [Group G]

theorem braid_of_involutions_cube (x y : G) (hx : x^2=1) (hy : y^2=1)
    (hc : (x*y)^3=1) : x*y*x=y*x*y := by
  have hxx : x*x=1 := by simpa only [pow_two] using hx
  have hyy : y*y=1 := by simpa only [pow_two] using hy
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹=y := inv_eq_of_mul_eq_one_right hyy
  have hprod : (x*y*x)*(y*x*y)=1 := by
    calc
      _=(x*y)^3 := by simp only [pow_succ,pow_zero,one_mul,mul_assoc]
      _=1 := hc
  calc
    _=(y*x*y)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    _=_ := by simp only [mul_inv_rev,hxi,hyi,mul_assoc]

theorem folded_braid (x y z : G) (hxz : Commute x z)
    (hxy : x*y*x=y*x*y) (hzy : z*y*z=y*z*y) :
    (x*z)*y*(x*z)*y=y*(x*z)*y*(x*z) := by
  calc
    _=(x*z*y)*(x*z)*y := by group
    _=(x*z*y)*(z*x)*y := congrArg (fun t : G=>(x*z*y)*t*y) hxz.eq
    _=x*(z*y*z)*x*y := by group
    _=x*(y*z*y)*x*y := by rw [hzy]
    _=x*y*z*(y*x*y) := by group
    _=x*y*z*(x*y*x) := by rw [←hxy]
    _=x*y*(z*x)*y*x := by group
    _=x*y*(x*z)*y*x := congrArg (fun t : G=>x*y*t*y*x) hxz.eq.symm
    _=(x*y*x)*z*y*x := by group
    _=(y*x*y)*z*y*x := by rw [hxy]
    _=y*x*(y*z*y)*x := by group
    _=y*x*(z*y*z)*x := by rw [←hzy]
    _=y*x*z*y*(z*x) := by group
    _=y*x*z*y*(x*z) := congrArg (fun t : G=>y*x*z*y*t) hxz.eq.symm
    _=_ := by group

end SymmetricSubgroupAsymptotics.CFSGThreeNodeFoldedBraid
