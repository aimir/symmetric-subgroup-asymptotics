import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Group

/-! If conjugation multiplies one additive parameter group by another
additive parameter group, the two resulting factors commute. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveConjugationFactorsCommute
variable {K G : Type*} [Add K] [Group G]

theorem factors_commute (u : G) (v c : K→G)
    (hv : ∀a b,v (a+b)=v a*v b) (hc : ∀a b,c (a+b)=c a*c b)
    (h : ∀a,u*v a*u⁻¹=c a*v a) (a b : K) : Commute (v a) (c b) := by
  have hh : c (a+b)*v (a+b)=(c a*v a)*(c b*v b) := by
    calc
      _=u*v (a+b)*u⁻¹ := (h (a+b)).symm
      _=(u*v a*u⁻¹)*(u*v b*u⁻¹) := by rw [hv]; group
      _=(c a*v a)*(c b*v b) := by rw [h,h]
  rw [hc,hv] at hh
  have hh' : c a*(c b*v a)*v b=c a*(v a*c b)*v b := by
    simpa only [mul_assoc] using hh
  exact (mul_left_cancel (mul_right_cancel hh')).symm

end SymmetricSubgroupAsymptotics.CFSGAdditiveConjugationFactorsCommute
