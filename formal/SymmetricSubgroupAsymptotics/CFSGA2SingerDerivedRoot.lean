import Mathlib.GroupTheory.Abelianization.Defs

/-! Literal involution, braid-cube and Singer-seven words force an actual
root into the derived subgroup. No perfectness or named A2 group is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGA2SingerDerivedRoot
variable {G : Type*} [Group G]

theorem root_mem_commutator (u v u' v' : G)
    (hu : u^2=1) (hv : v^2=1) (hu' : u'^2=1) (hv' : v'^2=1)
    (hthree : ((u*v*u)*(u'*v'*u'))^3=1)
    (hseven : (u*(u*v*u)*(u'*v'*u'))^7=1) : u∈commutator G := by
  let f : G→*Abelianization G := Abelianization.of
  have huq : (f u)^2=1 := by rw [←map_pow,hu,map_one]
  have hvq : (f v)^2=1 := by rw [←map_pow,hv,map_one]
  have huq' : (f u')^2=1 := by rw [←map_pow,hu',map_one]
  have hvq' : (f v')^2=1 := by rw [←map_pow,hv',map_one]
  have ha : f (u*v*u)=f v := by
    rw [map_mul,map_mul]
    calc
      f u*f v*f u=(f u)^2*f v := by rw [pow_two];ac_rfl
      _=f v := by rw [huq,one_mul]
  have hb : f (u'*v'*u')=f v' := by
    rw [map_mul,map_mul]
    calc
      f u'*f v'*f u'=(f u')^2*f v' := by rw [pow_two];ac_rfl
      _=f v' := by rw [huq',one_mul]
  have h3 := congrArg f hthree
  rw [map_pow,map_mul,ha,hb,map_one] at h3
  have h2 : (f v*f v')^2=1 := by rw [mul_pow,hvq,hvq',one_mul]
  have hp : f v*f v'=1 := by
    have he : (f v*f v')^3=f v*f v' := by
      rw [show (3:ℕ)=2+1 by rfl,pow_succ,h2,one_mul]
    exact he.symm.trans h3
  have h7 := congrArg f hseven
  rw [map_pow,map_mul,map_mul,ha,hb,map_one,mul_assoc,hp,mul_one] at h7
  have he : (f u)^7=f u := by
    calc
      (f u)^7=(f u)^(2*3+1) := rfl
      _=((f u)^2)^3*f u := by rw [pow_succ,pow_mul]
      _=f u := by rw [huq,one_pow,one_mul]
  have hfu : f u=1 := he.symm.trans h7
  have hm : u∈(Abelianization.of : G→*Abelianization G).ker := hfu
  rw [Abelianization.ker_of] at hm
  exact hm

end SymmetricSubgroupAsymptotics.CFSGA2SingerDerivedRoot
