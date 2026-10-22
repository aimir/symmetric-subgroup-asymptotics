import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Group

/-! Centrality forced by an actual additive collecting formula.
The comparison of t+1 with t is a group calculation; no third root
relation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveCollectingCentrality
variable {K G : Type*} [Ring K] [Group G]

theorem fixed_of_conjugation_factors (u v c : K→G)
    (hu : ∀t s,u (t+s)=u t*u s)
    (hc : ∀a b,c (a+b)=c a*c b)
    (h : ∀t a,u t*v a*(u t)⁻¹=c (a*t)*v a) (t a : K) :
    u t*c a*(u t)⁻¹=c a := by
  have hh : c (a*(t+1))*v a=(u t*c a*(u t)⁻¹)*(c (a*t)*v a) := by
    calc
      c (a*(t+1))*v a=u (t+1)*v a*(u (t+1))⁻¹ := (h (t+1) a).symm
      _=u t*(u 1*v a*(u 1)⁻¹)*(u t)⁻¹ := by rw [hu]; group
      _=u t*(c a*v a)*(u t)⁻¹ := by rw [h]; simp only [mul_one]
      _=(u t*c a*(u t)⁻¹)*(u t*v a*(u t)⁻¹) := by group
      _=(u t*c a*(u t)⁻¹)*(c (a*t)*v a) := by rw [h]
  have he : c (a*(t+1))=(u t*c a*(u t)⁻¹)*c (a*t) :=
    mul_right_cancel (by simpa only [mul_assoc] using hh)
  rw [show a*(t+1)=a+a*t by rw [mul_add,mul_one,add_comm],hc] at he
  exact (mul_right_cancel he).symm

end SymmetricSubgroupAsymptotics.CFSGAdditiveCollectingCentrality
