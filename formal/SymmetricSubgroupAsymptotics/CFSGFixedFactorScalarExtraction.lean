import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! An available product of a scaled additive factor and a fixed factor
recovers the entire scaled factor by a single actual group commutator.
No individual membership of the fixed factor is required. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGFixedFactorScalarExtraction
variable {K G : Type*} [Field K] [Group G]

theorem all_scaled_parameters (A B : K→G)
    (hBadd : ∀a b,B (a+b)=B a*B b) (hB0 : B 0=1)
    (T : G) (k : K) (hk : k≠1)
    (hA : ∀a,T*A a*T⁻¹=A a) (hB : ∀a,T*B a*T⁻¹=B (k*a))
    (H : Subgroup G) (hT : T∈H) (hpair : ∀a,B (-a)*A a∈H) :
    ∀b,B b∈H := by
  have hden : 1-k≠0 := sub_ne_zero.mpr (Ne.symm hk)
  have hinv (a : K) : (B (-a))⁻¹=B a := by
    apply inv_eq_of_mul_eq_one_right
    rw [←hBadd,neg_add_cancel,hB0]
  intro b
  let a : K := b/(1-k)
  have ha : (1-k)*a=b := by
    dsimp only [a]
    field_simp [hden]
  have he : T*(B (-a)*A a)*T⁻¹*(B (-a)*A a)⁻¹=B b := by
    calc
      _=(T*B (-a)*T⁻¹)*(T*A a*T⁻¹)*(B (-a)*A a)⁻¹ := by group
      _=B (k*(-a))*A a*(B (-a)*A a)⁻¹ := by rw [hB,hA]
      _=B (k*(-a))*(B (-a))⁻¹ := by group
      _=B (k*(-a))*B a := by rw [hinv]
      _=B (k*(-a)+a) := (hBadd _ _).symm
      _=B ((1-k)*a) := by congr 1; ring
      _=B b := by rw [ha]
  rw [←he]
  exact H.mul_mem (H.mul_mem (H.mul_mem hT (hpair a)) (H.inv_mem hT))
    (H.inv_mem (hpair a))

end SymmetricSubgroupAsymptotics.CFSGFixedFactorScalarExtraction
